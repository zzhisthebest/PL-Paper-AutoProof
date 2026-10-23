(** System F parametricity benchmark, Hard variant.
    Features: if-nondeterminism-recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFParametricityIfNondeterminismRecursionHardTask.

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
  | Ty_Bool : ty
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
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm
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

Notation "'Bool'" := Ty_Bool (in custom systemf_ty at level 0) : systemf_scope.
Notation "'true'" := tm_true (in custom systemf_tm at level 0) : systemf_scope.
Notation "'false'" := tm_false (in custom systemf_tm at level 0) : systemf_scope.
Notation "'if' t1 'then' t2 'else' t3" := (tm_if t1 t2 t3)
  (in custom systemf_tm at level 200, t1 custom systemf_tm, t2 custom systemf_tm, t3 custom systemf_tm at level 200) : systemf_scope.
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
  | Ty_Bool => Ty_Bool
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
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (open_tm_rec k u t1) (open_tm_rec k u t2) (open_tm_rec k u t3)
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
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (open_tm_ty_rec k U t1) (open_tm_ty_rec k U t2) (open_tm_ty_rec k U t3)
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
  | Ty_Bool => Ty_Bool
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
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (tm_ty_subst X U t1) (tm_ty_subst X U t2) (tm_ty_subst X U t3)
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
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (tm_subst x s t1) (tm_subst x s t2) (tm_subst x s t3)
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
  | lc_ty_bool : forall k, lc_ty_at k Ty_Bool
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
  | lc_tm_true : forall K k, lc_tm_at K k tm_true
  | lc_tm_false : forall K k, lc_tm_at K k tm_false
  | lc_tm_if : forall K k t1 t2 t3,
      lc_tm_at K k t1 -> lc_tm_at K k t2 -> lc_tm_at K k t3 -> lc_tm_at K k (tm_if t1 t2 t3)
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
  | v_true : value tm_true
  | v_false : value tm_false
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
  | ST_IfTrue : forall t1 t2,
      locally_closed_tm t1 ->
      locally_closed_tm t2 ->
      tm_if tm_true t1 t2 --> t1
  | ST_IfFalse : forall t1 t2,
      locally_closed_tm t1 ->
      locally_closed_tm t2 ->
      tm_if tm_false t1 t2 --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      locally_closed_tm t2 ->
      locally_closed_tm t3 ->
      tm_if t1 t2 t3 --> tm_if t1' t2 t3
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
  | WF_Bool : forall Delta, wf_ty Delta Ty_Bool
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
  | T_True : forall Delta Gamma, has_type Delta Gamma tm_true Ty_Bool
  | T_False : forall Delta Gamma, has_type Delta Gamma tm_false Ty_Bool
  | T_If : forall Delta Gamma t1 t2 t3 T,
      has_type Delta Gamma t1 Ty_Bool ->
      has_type Delta Gamma t2 T -> has_type Delta Gamma t3 T ->
      has_type Delta Gamma (tm_if t1 t2 t3) T
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

Definition value_relation := tm -> tm -> Prop.
Definition bound_relations := nat -> value_relation.
Definition free_relations := atom -> value_relation.

Definition extend_bound (R : value_relation) (rho : bound_relations)
  : bound_relations :=
  fun i => match i with 0 => R | S j => rho j end.

Fixpoint relates (T : ty) (rho : bound_relations)
    (eta : free_relations) (v w : tm) : Prop :=
  match T with
  | Ty_BVar i => rho i v w
  | Ty_FVar x => eta x v w
  | Ty_Arrow A B =>
      value v /\ value w /\
      forall a b, relates A rho eta a b ->
        exists c d, tm_app v a -->* c /\ tm_app w b -->* d /\
          relates B rho eta c d
  | Ty_All A =>
      value v /\ value w /\
      forall U V (R : value_relation),
        locally_closed_ty U -> locally_closed_ty V ->
        (forall a b, R a b -> value a /\ value b) ->
        exists c d, tm_tapp v U -->* c /\ tm_tapp w V -->* d /\
          relates A (extend_bound R rho) eta c d
  | Ty_Bool => (v = tm_true /\ w = tm_true) \/
               (v = tm_false /\ w = tm_false)
  | Ty_Nat => exists n, v = numeral n /\ w = numeral n
  end.

Definition expression_relation T rho eta t u : Prop :=
  exists v w, t -->* v /\ u -->* w /\ relates T rho eta v w.

Fixpoint close_ty (sigma : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar x => sigma x
  | Ty_Arrow A B => Ty_Arrow (close_ty sigma A) (close_ty sigma B)
  | Ty_All A => Ty_All (close_ty sigma A)
  | Ty_Bool => Ty_Bool
  | Ty_Nat => Ty_Nat
  end.

Fixpoint close_tm (sigma : atom -> ty) (theta : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => theta x
  | tm_abs T s => tm_abs (close_ty sigma T) (close_tm sigma theta s)
  | tm_app s u => tm_app (close_tm sigma theta s) (close_tm sigma theta u)
  | tm_tabs s => tm_tabs (close_tm sigma theta s)
  | tm_tapp s T => tm_tapp (close_tm sigma theta s) (close_ty sigma T)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if s u v => tm_if (close_tm sigma theta s)
                         (close_tm sigma theta u) (close_tm sigma theta v)
  | tm_zero => tm_zero
  | tm_succ s => tm_succ (close_tm sigma theta s)
  | tm_natrec s u v => tm_natrec (close_tm sigma theta s)
                                  (close_tm sigma theta u) (close_tm sigma theta v)
  | tm_choice s u => tm_choice (close_tm sigma theta s) (close_tm sigma theta u)
  end.

Definition set_ty (sigma : atom -> ty) (x : atom) (U : ty) : atom -> ty :=
  fun y => if Nat.eqb x y then U else sigma y.
Definition set_tm (theta : atom -> tm) (x : atom) (v : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then v else theta y.
Definition set_rel (eta : free_relations) (x : atom) (R : value_relation)
  : free_relations := fun y => if Nat.eqb x y then R else eta y.

Fixpoint type_names (T : ty) : list atom :=
  match T with
  | Ty_FVar x => [x]
  | Ty_Arrow A B => type_names A ++ type_names B
  | Ty_All A => type_names A
  | _ => []
  end.

Fixpoint term_names (t : tm) : list atom :=
  match t with
  | tm_fvar x => [x]
  | tm_abs T s => type_names T ++ term_names s
  | tm_app s u | tm_choice s u => term_names s ++ term_names u
  | tm_tabs s | tm_succ s => term_names s
  | tm_tapp s T => term_names s ++ type_names T
  | tm_if s u v | tm_natrec s u v =>
      term_names s ++ term_names u ++ term_names v
  | _ => []
  end.

Definition fresh_name (names : list atom) : atom :=
  S (fold_right Nat.max 0 names).

Lemma fresh_name_not_in : forall names, ~ In (fresh_name names) names.
Proof.
  intros names; unfold fresh_name.
  assert (forall x, In x names -> x <= fold_right Nat.max 0 names) as H.
  { induction names as [|a names IH]; simpl; intros x H; [contradiction|].
    destruct H as [->|H]; [lia|specialize (IH x H); lia]. }
  intros HIn; specialize (H _ HIn); lia.
Qed.

Lemma numeric_numeral : forall n, numeric_value (numeral n).
Proof. induction n; simpl; constructor; assumption. Qed.

Lemma relates_value : forall T rho eta v w,
  (forall i a b, rho i a b -> value a /\ value b) ->
  (forall x a b, eta x a b -> value a /\ value b) ->
  relates T rho eta v w -> value v /\ value w.
Proof.
  destruct T; simpl; intros rho eta v w Hb Hf H;
    try (exact (Hb _ _ _ H)); try (exact (Hf _ _ _ H));
    try (tauto).
  - destruct H as [[-> ->]|[-> ->]]; auto.
  - destruct H as [n [-> ->]]; split; constructor; apply numeric_numeral.
Qed.

Lemma lc_ty_weaken : forall T k j,
  lc_ty_at k T -> k <= j -> lc_ty_at j T.
Proof.
  intros T k j H; revert j.
  induction H; intros j Hle.
  - apply lc_ty_bvar; lia.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; eauto.
  - apply lc_ty_all; apply IHlc_ty_at; lia.
  - apply lc_ty_bool.
  - apply lc_ty_nat.
Qed.

Lemma lc_tm_weaken : forall t K k J j,
  lc_tm_at K k t -> K <= J -> k <= j -> lc_tm_at J j t.
Proof.
  intros t K k J j H; revert J j.
  induction H; intros J j HK Hk;
    try (econstructor; eauto using lc_ty_weaken; fail).
  - apply lc_tm_bvar; lia.
  - apply lc_tm_abs; [eapply lc_ty_weaken; eauto|].
    apply IHlc_tm_at; lia.
  - apply lc_tm_tabs. apply IHlc_tm_at; lia.
Qed.

Lemma lc_ty_open_inv : forall T k x,
  lc_ty_at k (open_ty_rec k (Ty_FVar x) T) -> lc_ty_at (S k) T.
Proof.
  induction T; intros k x H; simpl in H.
  - destruct (Nat.eqb k n) eqn:Heq; inversion H; subst;
      apply lc_ty_bvar; apply Nat.eqb_eq in Heq + apply Nat.eqb_neq in Heq; lia.
  - constructor.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - constructor.
  - constructor.
Qed.

Lemma lc_tm_open_inv : forall t K k x,
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) -> lc_tm_at K (S k) t.
Proof.
  induction t; intros K k x H; simpl in H.
  - destruct (Nat.eqb k n) eqn:Heq; inversion H; subst;
      apply lc_tm_bvar; apply Nat.eqb_eq in Heq + apply Nat.eqb_neq in Heq; lia.
  - constructor.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - constructor.
  - constructor.
  - inversion H; subst; constructor; eauto.
  - constructor.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
Qed.

Lemma lc_tm_ty_open_inv : forall t K k x,
  lc_tm_at K k (open_tm_ty_rec K (Ty_FVar x) t) ->
  lc_tm_at (S K) k t.
Proof.
  induction t; intros K k x H; simpl in H;
    inversion H; subst; try (constructor; eauto; fail).
  - constructor; eauto using lc_ty_open_inv.
  - constructor; eauto using lc_ty_open_inv.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H; induction H; unfold locally_closed_ty in *;
    try (constructor; eauto; fail).
  pose (x := fresh_name L).
  specialize (H0 x (fresh_name_not_in L)).
  constructor; eapply lc_ty_open_inv; exact H0.
Qed.

Lemma typing_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T H; induction H; unfold locally_closed_tm in *.
  - constructor.
  - apply lc_tm_abs; [eapply wf_ty_lc; eassumption|].
    eapply lc_tm_open_inv; apply H1; apply fresh_name_not_in.
  - apply lc_tm_app; assumption.
  - apply lc_tm_tabs. eapply lc_tm_ty_open_inv.
    apply H0; apply fresh_name_not_in.
  - apply lc_tm_tapp; [assumption|eapply wf_ty_lc; eassumption].
  - constructor.
  - constructor.
  - apply lc_tm_if; assumption.
  - constructor.
  - apply lc_tm_succ; assumption.
  - apply lc_tm_rec; assumption.
  - apply lc_tm_choice; assumption.
Qed.

Lemma close_ty_lc : forall T k sigma,
  lc_ty_at k T -> (forall x, locally_closed_ty (sigma x)) ->
  lc_ty_at k (close_ty sigma T).
Proof.
  intros T k sigma H; induction H; intros Hsigma; simpl;
    try (constructor; eauto; fail).
  eapply lc_ty_weaken; [apply Hsigma|lia].
Qed.

Lemma close_tm_lc : forall t K k sigma theta,
  lc_tm_at K k t ->
  (forall x, locally_closed_ty (sigma x)) ->
  (forall x, locally_closed_tm (theta x)) ->
  lc_tm_at K k (close_tm sigma theta t).
Proof.
  intros t K k sigma theta H; induction H; intros Hsigma Htheta; simpl;
    try (constructor; eauto using close_ty_lc; fail).
  eapply lc_tm_weaken; [apply Htheta|lia|lia].
Qed.

Lemma wf_closed : forall sigma Delta T,
  (forall x, locally_closed_ty (sigma x)) ->
  wf_ty Delta T -> locally_closed_ty (close_ty sigma T).
Proof.
  intros; apply close_ty_lc; [eapply wf_ty_lc; eassumption|assumption].
Qed.

Lemma typing_closed : forall sigma theta Delta Gamma t T,
  (forall x, locally_closed_ty (sigma x)) ->
  (forall x, locally_closed_tm (theta x)) ->
  has_type Delta Gamma t T -> locally_closed_tm (close_tm sigma theta t).
Proof.
  intros; apply close_tm_lc; [eapply typing_lc; eassumption|assumption|assumption].
Qed.

Definition overwrite_bound (k : nat) (R : value_relation)
    (rho : bound_relations) : bound_relations :=
  fun i => if Nat.eqb k i then R else rho i.

Lemma relates_congr : forall T rho rho' eta eta' v w,
  (forall i a b, rho i a b <-> rho' i a b) ->
  (forall x a b, eta x a b <-> eta' x a b) ->
  (relates T rho eta v w <-> relates T rho' eta' v w).
Proof.
  induction T; intros rho rho' eta eta' v w Hb Hf; simpl.
  - apply Hb.
  - apply Hf.
  - split; intros [Hv [Hw H]]; repeat split; auto;
      intros a b Hab; apply (proj2 (IHT1 _ _ _ _ _ _ Hb Hf)) in Hab +
        apply (proj1 (IHT1 _ _ _ _ _ _ Hb Hf)) in Hab;
      destruct (H a b Hab) as [c [d [Hc [Hd Hcd]]]];
      exists c, d; repeat split; auto;
      apply (proj1 (IHT2 _ _ _ _ _ _ Hb Hf)) in Hcd +
        apply (proj2 (IHT2 _ _ _ _ _ _ Hb Hf)) in Hcd; assumption.
  - assert (Hshift : forall R i a b,
      extend_bound R rho i a b <-> extend_bound R rho' i a b).
    { intros R [|i] a b; simpl; [tauto|apply Hb]. }
    split; intros [Hv [Hw H]]; repeat split; auto;
      intros U V R HU HV HR;
      destruct (H U V R HU HV HR) as [c [d [Hc [Hd Hcd]]]];
      exists c, d; repeat split; auto;
      apply (proj1 (IHT _ _ _ _ _ _ (Hshift R) Hf)) in Hcd +
        apply (proj2 (IHT _ _ _ _ _ _ (Hshift R) Hf)) in Hcd; assumption.
  - tauto.
  - tauto.
Qed.

Lemma relates_below : forall T k rho rho' eta v w,
  lc_ty_at k T ->
  (forall i a b, i < k -> rho i a b <-> rho' i a b) ->
  (relates T rho eta v w <-> relates T rho' eta v w).
Proof.
  intros T k rho rho' eta v w Hlc; revert rho rho' eta v w.
  induction Hlc; intros rho rho' eta v w Hagree; simpl.
  - apply Hagree; assumption.
  - tauto.
  - split; intros [Hv [Hw H]]; repeat split; auto;
      intros a b Hab;
      apply (proj2 (IHHlc1 _ _ _ _ _ Hagree)) in Hab +
        apply (proj1 (IHHlc1 _ _ _ _ _ Hagree)) in Hab;
      destruct (H a b Hab) as [c [d [Hc [Hd Hcd]]]];
      exists c, d; repeat split; auto;
      apply (proj1 (IHHlc2 _ _ _ _ _ Hagree)) in Hcd +
        apply (proj2 (IHHlc2 _ _ _ _ _ Hagree)) in Hcd; assumption.
  - assert (Hshift : forall R i a b, i < S k ->
      extend_bound R rho i a b <-> extend_bound R rho' i a b).
    { intros R [|i] a b Hi; simpl; [tauto|apply Hagree; lia]. }
    split; intros [Hv [Hw H]]; repeat split; auto;
      intros U V R HU HV HR;
      destruct (H U V R HU HV HR) as [c [d [Hc [Hd Hcd]]]];
      exists c, d; repeat split; auto;
      apply (proj1 (IHHlc _ _ _ _ _ (Hshift R))) in Hcd +
        apply (proj2 (IHHlc _ _ _ _ _ (Hshift R))) in Hcd; assumption.
  - tauto.
  - tauto.
Qed.

Lemma relates_open : forall T k rho eta eta' U R v w,
  locally_closed_ty U ->
  (forall a b, R a b <-> relates U rho eta' a b) ->
  (forall x, In x (type_names T) ->
     forall a b, eta x a b <-> eta' x a b) ->
  (relates T (overwrite_bound k R rho) eta v w <->
   relates (open_ty_rec k U T) rho eta' v w).
Proof.
  induction T; intros k rho eta eta' U R v w HU HR Heq; simpl.
  - unfold overwrite_bound; destruct (Nat.eqb k n) eqn:Heqn;
      simpl; [apply HR|tauto].
  - apply Heq; simpl; auto.
  - split; intros [Hv [Hw H]]; repeat split; auto;
      intros a b Hab;
      apply (proj2 (IHT1 _ _ _ _ _ _ _ _ HU HR
        (fun x Hx => Heq x (in_or_app _ _ _ (or_introl Hx))))) in Hab +
        apply (proj1 (IHT1 _ _ _ _ _ _ _ _ HU HR
          (fun x Hx => Heq x (in_or_app _ _ _ (or_introl Hx))))) in Hab;
      destruct (H a b Hab) as [c [d [Hc [Hd Hcd]]]];
      exists c, d; repeat split; auto;
      apply (proj1 (IHT2 _ _ _ _ _ _ _ _ HU HR
        (fun x Hx => Heq x (in_or_app _ _ _ (or_intror Hx))))) in Hcd +
        apply (proj2 (IHT2 _ _ _ _ _ _ _ _ HU HR
          (fun x Hx => Heq x (in_or_app _ _ _ (or_intror Hx))))) in Hcd; assumption.
  - assert (HRQ : forall Q a b,
        R a b <-> relates U (extend_bound Q rho) eta' a b).
    { intros Q a b; rewrite HR.
      apply relates_below with (k := 0); auto; intros; lia. }
    assert (Hshift : forall Q i a b,
      extend_bound Q (overwrite_bound k R rho) i a b <->
      overwrite_bound (S k) R (extend_bound Q rho) i a b).
    { intros Q [|i] a b; unfold overwrite_bound, extend_bound; simpl.
      - destruct (Nat.eqb (S k) 0); tauto.
      - destruct (Nat.eqb k i); tauto. }
    split; intros [Hv [Hw H]]; repeat split; auto;
      intros A B Q HA HB HQ;
      destruct (H A B Q HA HB HQ) as [c [d [Hc [Hd Hcd]]]];
      exists c, d; repeat split; auto.
    + apply (proj1 (relates_congr T _ _ eta eta c d
        (Hshift Q) (fun x a b => iff_refl _))) in Hcd.
      apply (proj1 (IHT _ _ _ _ _ _ _ _ HU (HRQ Q) Heq)) in Hcd.
      exact Hcd.
    + apply (proj2 (IHT _ _ _ _ _ _ _ _ HU (HRQ Q) Heq)) in Hcd.
      apply (proj2 (relates_congr T _ _ eta eta c d
        (Hshift Q) (fun x a b => iff_refl _))) in Hcd.
      exact Hcd.
  - tauto.
  - tauto.
Qed.

Lemma open_ty_above : forall depth T,
  lc_ty_at depth T -> forall j U, open_ty_rec (depth + j) U T = T.
Proof.
  intros depth T H; induction H; intros j U; simpl; f_equal; auto.
  - destruct (Nat.eqb (k + j) i) eqn:E;
      [apply Nat.eqb_eq in E; lia|reflexivity].
  - replace (S (k + j)) with (S k + j) by lia; auto.
Qed.

Lemma open_ty_closed : forall T k U,
  locally_closed_ty T -> open_ty_rec k U T = T.
Proof.
  intros T k U H; replace k with (0 + k) by lia;
    now apply open_ty_above.
Qed.

Lemma open_tm_above : forall K depth t,
  lc_tm_at K depth t -> forall j u,
    open_tm_rec (depth + j) u t = t.
Proof.
  intros K depth t H; induction H; intros j u; simpl; f_equal; auto.
  - destruct (Nat.eqb (k + j) i) eqn:E;
      [apply Nat.eqb_eq in E; lia|reflexivity].
  - replace (S (k + j)) with (S k + j) by lia; auto.
Qed.

Lemma open_tm_closed : forall t k u,
  locally_closed_tm t -> open_tm_rec k u t = t.
Proof.
  intros t k u H; replace k with (0 + k) by lia;
    now apply open_tm_above with (K := 0).
Qed.

Lemma open_tm_ty_above : forall depth k t,
  lc_tm_at depth k t -> forall j U,
    open_tm_ty_rec (depth + j) U t = t.
Proof.
  intros depth k t H; induction H; intros j U; simpl; f_equal; auto.
  - now apply open_ty_above.
  - replace (S (K + j)) with (S K + j) by lia; auto.
  - now apply open_ty_above.
Qed.

Lemma open_tm_ty_closed : forall t k U,
  locally_closed_tm t -> open_tm_ty_rec k U t = t.
Proof.
  intros t k U H; replace k with (0 + k) by lia;
    now apply open_tm_ty_above with (k := 0).
Qed.

Lemma not_in_app : forall (x : atom) a b,
  ~ In x (a ++ b) -> ~ In x a /\ ~ In x b.
Proof. intros x a b H; rewrite in_app_iff in H; tauto. Qed.

Lemma close_ty_open : forall T k sigma x U,
  ~ In x (type_names T) ->
  (forall y, locally_closed_ty (sigma y)) ->
  close_ty (set_ty sigma x U) (open_ty_rec k (Ty_FVar x) T) =
  open_ty_rec k U (close_ty sigma T).
Proof.
  induction T; intros k sigma x U Hfresh Hclosed; simpl in *; auto.
  - destruct (Nat.eqb k n); simpl; auto.
    unfold set_ty; now rewrite Nat.eqb_refl.
  - unfold set_ty; destruct (Nat.eqb x a) eqn:Hxa.
    + apply Nat.eqb_eq in Hxa; subst; exfalso; apply Hfresh; auto.
    + symmetry; apply open_ty_closed; apply Hclosed.
  - apply not_in_app in Hfresh; destruct Hfresh; f_equal; auto.
  - f_equal; apply IHT; auto.
Qed.

Lemma close_tm_open : forall t k sigma theta x v,
  ~ In x (term_names t) ->
  (forall y, locally_closed_tm (theta y)) ->
  close_tm sigma (set_tm theta x v) (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k v (close_tm sigma theta t).
Proof.
  induction t; intros k sigma theta x v Hfresh Hclosed;
    simpl in *; auto.
  - destruct (Nat.eqb k n); simpl; auto.
    unfold set_tm; now rewrite Nat.eqb_refl.
  - unfold set_tm; destruct (Nat.eqb x a) eqn:Hxa.
    + apply Nat.eqb_eq in Hxa; subst; exfalso; apply Hfresh; auto.
    + symmetry; apply open_tm_closed; apply Hclosed.
  - apply not_in_app in Hfresh; destruct Hfresh; f_equal; auto.
  - apply not_in_app in Hfresh; destruct Hfresh; f_equal; auto.
  - f_equal; auto.
  - apply not_in_app in Hfresh; destruct Hfresh; f_equal; auto.
  - apply not_in_app in Hfresh as [H1 H23].
    apply not_in_app in H23 as [H2 H3]. f_equal; auto.
  - f_equal; auto.
  - apply not_in_app in Hfresh as [H1 H23].
    apply not_in_app in H23 as [H2 H3]. f_equal; auto.
  - apply not_in_app in Hfresh; destruct Hfresh; f_equal; auto.
Qed.

Lemma close_tm_ty_open : forall t k sigma theta x U,
  ~ In x (term_names t) ->
  (forall y, locally_closed_ty (sigma y)) ->
  (forall y, locally_closed_tm (theta y)) ->
  close_tm (set_ty sigma x U) theta
    (open_tm_ty_rec k (Ty_FVar x) t) =
  open_tm_ty_rec k U (close_tm sigma theta t).
Proof.
  induction t; intros k sigma theta x U Hfresh Hsigma Htheta;
    simpl in *; auto.
  - symmetry; apply open_tm_ty_closed; apply Htheta.
  - apply not_in_app in Hfresh; destruct Hfresh; simpl; f_equal;
      auto using close_ty_open.
  - apply not_in_app in Hfresh; destruct Hfresh; f_equal; auto.
  - f_equal; auto.
  - apply not_in_app in Hfresh; destruct Hfresh; f_equal;
      auto using close_ty_open.
  - apply not_in_app in Hfresh as [H1 H23].
    apply not_in_app in H23 as [H2 H3]. f_equal; auto.
  - f_equal; auto.
  - apply not_in_app in Hfresh as [H1 H23].
    apply not_in_app in H23 as [H2 H3]. f_equal; auto.
  - apply not_in_app in Hfresh; destruct Hfresh; f_equal; auto.
Qed.

Lemma numeral_value : forall n, value (numeral n).
Proof. intros; constructor; apply numeric_numeral. Qed.

Lemma numeral_closed : forall n, locally_closed_tm (numeral n).
Proof. induction n; simpl; constructor; assumption. Qed.

Lemma value_closed : forall v, value v -> locally_closed_tm v.
Proof.
  intros v H; destruct H; auto; unfold locally_closed_tm.
  - constructor.
  - constructor.
  - induction H; simpl; constructor; auto.
Qed.

Lemma multi_trans : forall a b c, a -->* b -> b -->* c -> a -->* c.
Proof.
  intros a b c H; induction H; intros Hbc; auto.
  eapply multi_step; eauto.
Qed.

Lemma multi_app_left : forall a b u,
  a -->* b -> locally_closed_tm u ->
  tm_app a u -->* tm_app b u.
Proof.
  intros a b u H; induction H; intros Hu; [constructor|].
  eapply multi_step; [apply ST_App1; eauto|auto].
Qed.

Lemma multi_app_right : forall a b v,
  a -->* b -> value v ->
  tm_app v a -->* tm_app v b.
Proof.
  intros a b v H; induction H; intros Hv; [constructor|].
  eapply multi_step; [apply ST_App2; eauto|auto].
Qed.

Lemma multi_tapp : forall a b U,
  a -->* b -> locally_closed_ty U ->
  tm_tapp a U -->* tm_tapp b U.
Proof.
  intros a b U H; induction H; intros HU; [constructor|].
  eapply multi_step; [apply ST_TApp; eauto|auto].
Qed.

Lemma multi_succ : forall a b,
  a -->* b -> tm_succ a -->* tm_succ b.
Proof.
  intros a b H; induction H; [constructor|].
  eapply multi_step; [apply ST_Succ; eauto|auto].
Qed.

Lemma multi_if : forall a b u v,
  a -->* b -> locally_closed_tm u -> locally_closed_tm v ->
  tm_if a u v -->* tm_if b u v.
Proof.
  intros a b u v H; induction H; intros Hu Hv; [constructor|].
  eapply multi_step; [apply ST_If; eauto|auto].
Qed.

Lemma multi_rec_arg : forall a b u v,
  a -->* b -> locally_closed_tm u -> locally_closed_tm v ->
  tm_natrec a u v -->* tm_natrec b u v.
Proof.
  intros a b u v H; induction H; intros Hu Hv; [constructor|].
  eapply multi_step; [apply ST_RecArg; eauto|auto].
Qed.

Lemma multi_rec_base : forall a b n s,
  a -->* b -> numeric_value n -> locally_closed_tm s ->
  tm_natrec n a s -->* tm_natrec n b s.
Proof.
  intros a b n s H; induction H; intros Hn Hs; [constructor|].
  eapply multi_step; [apply ST_RecBase; eauto|auto].
Qed.

Lemma multi_rec_step : forall a b n u,
  a -->* b -> numeric_value n -> value u ->
  tm_natrec n u a -->* tm_natrec n u b.
Proof.
  intros a b n u H; induction H; intros Hn Hu; [constructor|].
  eapply multi_step; [apply ST_RecStep; eauto|auto].
Qed.

Lemma relates_fresh : forall T x rho eta R v w,
  ~ In x (type_names T) ->
  (relates T rho eta v w <-> relates T rho (set_rel eta x R) v w).
Proof.
  induction T; intros x rho eta R v w Hx; simpl in *; try tauto.
  - unfold set_rel; destruct (Nat.eqb x a) eqn:E; [|tauto].
    apply Nat.eqb_eq in E; subst; exfalso; apply Hx; auto.
  - apply not_in_app in Hx as [H1 H2].
    split; intros [Hv [Hw H]]; repeat split; auto; intros a b Hab;
      apply (proj2 (IHT1 x rho eta R a b H1)) in Hab +
        apply (proj1 (IHT1 x rho eta R a b H1)) in Hab;
      destruct (H a b Hab) as [c [d [Hc [Hd Hcd]]]];
      exists c, d; repeat split; auto;
      apply (proj1 (IHT2 x rho eta R c d H2)) in Hcd +
        apply (proj2 (IHT2 x rho eta R c d H2)) in Hcd; assumption.
  - split; intros [Hv [Hw H]]; repeat split; auto;
      intros U V Q HU HV HQ;
      destruct (H U V Q HU HV HQ) as [c [d [Hc [Hd Hcd]]]];
      exists c, d; repeat split; auto;
      apply (proj1 (IHT x (extend_bound Q rho) eta R c d Hx)) in Hcd +
        apply (proj2 (IHT x (extend_bound Q rho) eta R c d Hx)) in Hcd;
      assumption.
Qed.

Fixpoint context_names (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (_, T) :: rest => type_names T ++ context_names rest
  end.

Lemma lookup_names : forall Gamma x T y,
  lookup_context x Gamma = Some T -> In y (type_names T) ->
  In y (context_names Gamma).
Proof.
  induction Gamma as [|[z A] Gamma IH]; intros x T y Hlookup Hy;
    simpl in *; [discriminate|].
  destruct (Nat.eqb x z) eqn:E.
  - inversion Hlookup; subst; apply in_or_app; auto.
  - apply in_or_app; right; eapply IH; eauto.
Qed.

Definition good_relations (rho : bound_relations) (eta : free_relations) :=
  (forall i a b, rho i a b -> value a /\ value b) /\
  (forall x a b, eta x a b -> value a /\ value b).

Definition good_environment (Gamma : context)
    (rho : bound_relations) (eta : free_relations)
    (sigma tau : atom -> ty) (theta psi : atom -> tm) :=
  good_relations rho eta /\
  (forall x, locally_closed_ty (sigma x)) /\
  (forall x, locally_closed_ty (tau x)) /\
  (forall x, locally_closed_tm (theta x)) /\
  (forall x, locally_closed_tm (psi x)) /\
  (forall x T, lookup_context x Gamma = Some T ->
     relates T rho eta (theta x) (psi x)).

Lemma env_sigma_lc : forall Gamma rho eta sigma tau theta psi,
  good_environment Gamma rho eta sigma tau theta psi ->
  forall x, locally_closed_ty (sigma x).
Proof.
  intros ? ? ? ? ? ? ? [_ [H _]]; exact H.
Qed.

Lemma env_tau_lc : forall Gamma rho eta sigma tau theta psi,
  good_environment Gamma rho eta sigma tau theta psi ->
  forall x, locally_closed_ty (tau x).
Proof.
  intros ? ? ? ? ? ? ? [_ [_ [H _]]]; exact H.
Qed.

Lemma env_theta_lc : forall Gamma rho eta sigma tau theta psi,
  good_environment Gamma rho eta sigma tau theta psi ->
  forall x, locally_closed_tm (theta x).
Proof. intros ? ? ? ? ? ? ? [_ [_ [_ [H _]]]]; exact H. Qed.

Lemma env_psi_lc : forall Gamma rho eta sigma tau theta psi,
  good_environment Gamma rho eta sigma tau theta psi ->
  forall x, locally_closed_tm (psi x).
Proof. intros ? ? ? ? ? ? ? [_ [_ [_ [_ [H _]]]]]; exact H. Qed.

Lemma relates_closed_inputs : forall T rho eta v w,
  good_relations rho eta -> relates T rho eta v w ->
  value v /\ value w.
Proof.
  intros T rho eta v w [Hb Hf] H.
  exact (relates_value T rho eta v w Hb Hf H).
Qed.

Lemma expression_left : forall T rho eta a b v w,
  a -->* v -> b -->* w -> relates T rho eta v w ->
  expression_relation T rho eta a b.
Proof. intros; exists v, w; auto. Qed.

Lemma good_bound : forall R rho eta,
  good_relations rho eta ->
  (forall a b, R a b -> value a /\ value b) ->
  good_relations (extend_bound R rho) eta.
Proof.
  intros R rho eta [Hb Hf] HR; split; auto.
  intros [|i] a b H; simpl in H; eauto.
Qed.

Lemma good_free : forall x R rho eta,
  good_relations rho eta ->
  (forall a b, R a b -> value a /\ value b) ->
  good_relations rho (set_rel eta x R).
Proof.
  intros x R rho eta [Hb Hf] HR; split; auto.
  intros y a b H; unfold set_rel in H;
    destruct (Nat.eqb x y); eauto.
Qed.

Lemma environment_term : forall Gamma rho eta sigma tau theta psi x T a b,
  good_environment Gamma rho eta sigma tau theta psi ->
  relates T rho eta a b ->
  good_environment ((x, T) :: Gamma) rho eta sigma tau
    (set_tm theta x a) (set_tm psi x b).
Proof.
  intros Gamma rho eta sigma tau theta psi x T a b
    [Hrel [Hs [Ht [Htheta [Hpsi Hgamma]]]]] Hab.
  pose proof (relates_closed_inputs T rho eta a b Hrel Hab) as [Ha Hb].
  unfold good_environment; repeat (split; [assumption|]).
  split.
  - intros y; unfold set_tm; destruct (Nat.eqb x y); auto using value_closed.
  - split.
    + intros y; unfold set_tm; destruct (Nat.eqb x y); auto using value_closed.
    + intros y A Hlookup; simpl in Hlookup.
      destruct (Nat.eqb y x) eqn:E.
      * apply Nat.eqb_eq in E; subst. inversion Hlookup; subst.
        unfold set_tm; now rewrite Nat.eqb_refl.
      * apply Nat.eqb_neq in E.
        assert (E' : Nat.eqb x y = false).
        { apply Nat.eqb_neq; congruence. }
        unfold set_tm; rewrite E'; apply Hgamma; assumption.
Qed.

Lemma environment_type : forall Gamma rho eta sigma tau theta psi x U V R,
  good_environment Gamma rho eta sigma tau theta psi ->
  ~ In x (context_names Gamma) ->
  locally_closed_ty U -> locally_closed_ty V ->
  (forall a b, R a b -> value a /\ value b) ->
  good_environment Gamma rho (set_rel eta x R)
    (set_ty sigma x U) (set_ty tau x V) theta psi.
Proof.
  intros Gamma rho eta sigma tau theta psi x U V R
    [Hrel [Hs [Ht [Htheta [Hpsi Hgamma]]]]] Hfresh HU HV HR.
  unfold good_environment; split; [eapply good_free; eauto|].
  split; [|split; [|split; [exact Htheta|split; [exact Hpsi|]]]].
  - intros y; unfold set_ty; destruct (Nat.eqb x y); auto.
  - intros y; unfold set_ty; destruct (Nat.eqb x y); auto.
  - intros y A Hlookup.
    assert (HfreshA : ~ In x (type_names A)).
    { intros HIn; apply Hfresh; eapply lookup_names; eauto. }
    apply (proj1 (relates_fresh A x rho eta R (theta y) (psi y) HfreshA)).
    apply Hgamma; assumption.
Qed.

Lemma rec_related : forall n T rho eta b1 b2 s1 s2,
  good_relations rho eta ->
  relates T rho eta b1 b2 ->
  relates (Ty_Arrow Ty_Nat (Ty_Arrow T T)) rho eta s1 s2 ->
  expression_relation T rho eta
    (tm_natrec (numeral n) b1 s1)
    (tm_natrec (numeral n) b2 s2).
Proof.
  induction n; intros T rho eta b1 b2 s1 s2 Hgood Hb Hs.
  - simpl. pose proof (relates_closed_inputs _ _ _ _ _ Hgood Hb) as [Hb1 Hb2].
    destruct Hs as [Hs1 [Hs2 _]].
    exists b1, b2; split.
    + apply multi_step with (y := b1);
        [apply ST_RecZero; assumption|constructor].
    + split; [apply multi_step with (y := b2);
        [apply ST_RecZero; assumption|constructor]|assumption].
  - pose proof (relates_closed_inputs _ _ _ _ _ Hgood Hb) as [Hb1 Hb2].
    destruct Hs as [Hs1 [Hs2 Hfn]].
    assert (Hn : relates Ty_Nat rho eta (numeral n) (numeral n)).
    { simpl; exists n; auto. }
    destruct (Hfn _ _ Hn) as [f1 [f2 [Hf1 [Hf2 Hf]]]].
    pose proof (relates_closed_inputs _ _ _ _ _ Hgood Hf) as [Hfv1 Hfv2].
    destruct (IHn T rho eta b1 b2 s1 s2 Hgood Hb
      (conj Hs1 (conj Hs2 Hfn))) as [r1 [r2 [Hr1 [Hr2 Hr]]]].
    destruct Hf as [_ [_ Happly]].
    destruct (Happly _ _ Hr) as [c1 [c2 [Hc1 [Hc2 Hc]]]].
    exists c1, c2; repeat split; auto.
    + eapply multi_step.
      * apply ST_RecSucc; auto using numeric_numeral.
      * eapply multi_trans.
        -- apply multi_app_left; [exact Hf1|].
           apply lc_tm_rec; [apply numeral_closed|apply value_closed; exact Hb1|
             apply value_closed; exact Hs1].
        -- eapply multi_trans.
           ++ apply multi_app_right; eauto.
           ++ exact Hc1.
    + eapply multi_step.
      * apply ST_RecSucc; auto using numeric_numeral.
      * eapply multi_trans.
        -- apply multi_app_left; [exact Hf2|].
           apply lc_tm_rec; [apply numeral_closed|apply value_closed; exact Hb2|
             apply value_closed; exact Hs2].
        -- eapply multi_trans.
           ++ apply multi_app_right; eauto.
           ++ exact Hc2.
Qed.

Lemma relates_extend_zero : forall T rho eta R v w,
  lc_ty_at 1 T ->
  relates T (overwrite_bound 0 R rho) eta v w <->
  relates T (extend_bound R rho) eta v w.
Proof.
  intros T rho eta R v w HT.
  apply relates_below with (k := 1); auto.
  intros [|i] a b Hi; simpl; [tauto|lia].
Qed.

Lemma lc_ty_open : forall T k U,
  lc_ty_at (S k) T -> locally_closed_ty U ->
  lc_ty_at k (open_ty_rec k U T).
Proof.
  induction T; intros k U Hlc HU; inversion Hlc; subst; simpl;
    try (constructor; eauto; fail).
  destruct (Nat.eqb k n) eqn:E.
  - eapply lc_ty_weaken; [exact HU|lia].
  - apply lc_ty_bvar; apply Nat.eqb_neq in E; lia.
Qed.

Lemma typing_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_ty T.
Proof.
  intros Delta Gamma t T H; induction H; unfold locally_closed_ty in *.
  - eapply wf_ty_lc; eauto.
  - apply lc_ty_arrow; [eapply wf_ty_lc; eauto|].
    apply (H1 (fresh_name L) (fresh_name_not_in L)).
  - inversion IHhas_type1; subst; assumption.
  - apply lc_ty_all. eapply lc_ty_open_inv.
    apply (H0 (fresh_name L) (fresh_name_not_in L)).
  - inversion IHhas_type; subst.
    eapply lc_ty_open; eauto using wf_ty_lc.
  - constructor.
  - constructor.
  - exact IHhas_type2.
  - constructor.
  - constructor.
  - exact IHhas_type2.
  - exact IHhas_type1.
Qed.

Theorem fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall rho eta sigma tau theta psi,
    good_environment Gamma rho eta sigma tau theta psi ->
    expression_relation T rho eta
      (close_tm sigma theta t) (close_tm tau psi t).
Proof.
  intros Delta Gamma t T Htype; induction Htype;
    intros rho eta sigma tau theta psi Henv.
  - destruct Henv as [_ [_ [_ [_ [_ Hgamma]]]]].
    exists (theta x), (psi x); simpl; repeat split; auto using multi_refl.
  - pose (x := fresh_name (L ++ term_names t2)).
    assert (Hx : ~ In x L /\ ~ In x (term_names t2)).
    { unfold x; apply not_in_app; apply fresh_name_not_in. }
    destruct Hx as [HxL Hxt].
    pose proof (env_sigma_lc _ _ _ _ _ _ _ Henv) as Hsigma.
    pose proof (env_tau_lc _ _ _ _ _ _ _ Henv) as Htau.
    pose proof (env_theta_lc _ _ _ _ _ _ _ Henv) as Htheta.
    pose proof (env_psi_lc _ _ _ _ _ _ _ Henv) as Hpsi.
    assert (Hraw : has_type Delta Gamma (tm_abs T1 t2) (Ty_Arrow T1 T2)).
    { apply T_Abs with (L := L); auto. }
    assert (Hl : locally_closed_tm (close_tm sigma theta (tm_abs T1 t2))).
    { eapply typing_closed; eauto. }
    assert (Hr : locally_closed_tm (close_tm tau psi (tm_abs T1 t2))).
    { eapply typing_closed; eauto. }
    simpl in Hl, Hr |- *.
    exists (tm_abs (close_ty sigma T1) (close_tm sigma theta t2)),
           (tm_abs (close_ty tau T1) (close_tm tau psi t2)).
    split; [constructor|]. split; [constructor|]. simpl.
    split; [apply v_abs; exact Hl|].
    split; [apply v_abs; exact Hr|].
    intros a b Hab.
      pose proof (proj1 Henv) as Hgood.
      pose proof (relates_closed_inputs _ _ _ _ _ Hgood Hab) as [Ha Hb].
      assert (Henv' : good_environment ((x,T1)::Gamma) rho eta sigma tau
          (set_tm theta x a) (set_tm psi x b)).
      { eapply environment_term; eauto. }
      destruct (H1 x HxL rho eta sigma tau
        (set_tm theta x a) (set_tm psi x b) Henv')
        as [c [d [Hc [Hd Hcd]]]].
      exists c, d; split.
      * eapply multi_step; [apply ST_AppAbs; auto|].
        unfold open_tm in *.
        rewrite <- (close_tm_open t2 0 sigma theta x a Hxt Htheta).
        exact Hc.
      * split.
        -- eapply multi_step; [apply ST_AppAbs; auto|].
           unfold open_tm in *.
           rewrite <- (close_tm_open t2 0 tau psi x b Hxt Hpsi).
           exact Hd.
        -- exact Hcd.
  - destruct (IHHtype1 rho eta sigma tau theta psi Henv)
      as [f1 [f2 [Hf1 [Hf2 Hf]]]].
    destruct (IHHtype2 rho eta sigma tau theta psi Henv)
      as [a1 [a2 [Ha1 [Ha2 Ha]]]].
    destruct Hf as [Hfv1 [Hfv2 Happly]].
    destruct (Happly _ _ Ha) as [c1 [c2 [Hc1 [Hc2 Hc]]]].
    pose proof (relates_closed_inputs _ _ _ _ _ (proj1 Henv) Ha)
      as [Hav1 Hav2].
    assert (Harg1 : locally_closed_tm (close_tm sigma theta t2)).
    { eapply typing_closed; eauto using env_sigma_lc, env_theta_lc. }
    assert (Harg2 : locally_closed_tm (close_tm tau psi t2)).
    { eapply typing_closed; eauto using env_tau_lc, env_psi_lc. }
    exists c1, c2; split.
    + eapply multi_trans.
      * apply multi_app_left; eauto.
      * eapply multi_trans; [apply multi_app_right; eauto|exact Hc1].
    + split; [|exact Hc].
      eapply multi_trans.
      * apply multi_app_left; eauto.
      * eapply multi_trans; [apply multi_app_right; eauto|exact Hc2].
  - pose (X := fresh_name
      (L ++ term_names t ++ type_names T ++ context_names Gamma)).
    assert (HX : ~ In X L /\ ~ In X (term_names t) /\
      ~ In X (type_names T) /\ ~ In X (context_names Gamma)).
    { pose proof (fresh_name_not_in
        (L ++ term_names t ++ type_names T ++ context_names Gamma)) as Hfresh.
      fold X in Hfresh.
      apply not_in_app in Hfresh as [HXL Hrest].
      apply not_in_app in Hrest as [HXt Hrest].
      apply not_in_app in Hrest as [HXT HXGamma].
      repeat split; assumption. }
    destruct HX as [HXL [HXt [HXT HXGamma]]].
    pose proof (env_sigma_lc _ _ _ _ _ _ _ Henv) as Hsigma.
    pose proof (env_tau_lc _ _ _ _ _ _ _ Henv) as Htau.
    pose proof (env_theta_lc _ _ _ _ _ _ _ Henv) as Htheta.
    pose proof (env_psi_lc _ _ _ _ _ _ _ Henv) as Hpsi.
    assert (Hraw : has_type Delta Gamma (tm_tabs t) (Ty_All T)).
    { apply T_TAbs with (L := L); exact H. }
    assert (Hl : locally_closed_tm (close_tm sigma theta (tm_tabs t))).
    { eapply typing_closed; eauto. }
    assert (Hr : locally_closed_tm (close_tm tau psi (tm_tabs t))).
    { eapply typing_closed; eauto. }
    assert (HT : lc_ty_at 1 T).
    { eapply lc_ty_open_inv.
      eapply typing_type_lc; apply H; exact HXL. }
    simpl in Hl, Hr |- *.
    exists (tm_tabs (close_tm sigma theta t)),
           (tm_tabs (close_tm tau psi t)).
    split; [constructor|]. split; [constructor|]. simpl.
    split; [apply v_tabs; exact Hl|].
    split; [apply v_tabs; exact Hr|].
    intros U V R HU HV HR.
    assert (Henv' : good_environment Gamma rho (set_rel eta X R)
       (set_ty sigma X U) (set_ty tau X V) theta psi).
    { eapply environment_type; eauto. }
    destruct (H0 X HXL rho (set_rel eta X R)
      (set_ty sigma X U) (set_ty tau X V) theta psi Henv')
      as [c [d [Hc [Hd Hcd]]]].
    exists c, d; split.
    + eapply multi_step; [apply ST_TAppTabs; eauto|].
      unfold open_tm_ty in *.
      rewrite <- (close_tm_ty_open t 0 sigma theta X U HXt Hsigma Htheta).
      exact Hc.
    + split.
      * eapply multi_step; [apply ST_TAppTabs; eauto|].
        unfold open_tm_ty in *.
        rewrite <- (close_tm_ty_open t 0 tau psi X V HXt Htau Hpsi).
        exact Hd.
      * apply (proj1 (relates_extend_zero T rho eta R c d HT)).
        assert (Hopen := relates_open T 0 rho eta
          (set_rel eta X R) (Ty_FVar X) R c d).
        apply Hopen.
        -- constructor.
        -- intros a b; simpl; unfold set_rel; rewrite Nat.eqb_refl; tauto.
        -- intros y Hy a b; unfold set_rel.
           assert (E : Nat.eqb X y = false).
           { apply Nat.eqb_neq; intros <-; auto. }
           now rewrite E.
        -- exact Hcd.
  - destruct (IHHtype rho eta sigma tau theta psi Henv)
      as [f1 [f2 [Hf1 [Hf2 Hf]]]].
    pose proof (env_sigma_lc _ _ _ _ _ _ _ Henv) as Hsigma.
    pose proof (env_tau_lc _ _ _ _ _ _ _ Henv) as Htau.
    assert (HU1 : locally_closed_ty (close_ty sigma U)).
    { apply close_ty_lc; [eapply wf_ty_lc; eauto|exact Hsigma]. }
    assert (HU2 : locally_closed_ty (close_ty tau U)).
    { apply close_ty_lc; [eapply wf_ty_lc; eauto|exact Htau]. }
    assert (HT : lc_ty_at 1 T).
    { pose proof (typing_type_lc _ _ _ _ Htype) as Hty.
      inversion Hty; assumption. }
    destruct Hf as [_ [_ Hall]].
    destruct (Hall _ _ (relates U rho eta) HU1 HU2
      (fun a b Hab => relates_closed_inputs U rho eta a b
        (proj1 Henv) Hab)) as [c1 [c2 [Hc1 [Hc2 Hc]]]].
    exists c1, c2; split.
    + eapply multi_trans; [apply multi_tapp; eauto|exact Hc1].
    + split.
      * eapply multi_trans; [apply multi_tapp; eauto|exact Hc2].
      * apply (proj1 (relates_open T 0 rho eta eta U
          (relates U rho eta) c1 c2
          (wf_ty_lc _ _ H) (fun a b => iff_refl _)
          (fun y Hy a b => iff_refl _))).
        apply (proj2 (relates_extend_zero T rho eta
          (relates U rho eta) c1 c2 HT)); exact Hc.
  - exists tm_true, tm_true; simpl; repeat split; auto using multi_refl.
  - exists tm_false, tm_false; simpl; repeat split; auto using multi_refl.
  - destruct (IHHtype1 rho eta sigma tau theta psi Henv)
      as [q1 [q2 [Hq1 [Hq2 Hq]]]].
    destruct (IHHtype2 rho eta sigma tau theta psi Henv)
      as [a1 [a2 [Ha1 [Ha2 Ha]]]].
    destruct (IHHtype3 rho eta sigma tau theta psi Henv)
      as [b1 [b2 [Hb1 [Hb2 Hb]]]].
    assert (Hthen1 : locally_closed_tm (close_tm sigma theta t2)).
    { eapply typing_closed; eauto using env_sigma_lc, env_theta_lc. }
    assert (Hthen2 : locally_closed_tm (close_tm tau psi t2)).
    { eapply typing_closed; eauto using env_tau_lc, env_psi_lc. }
    assert (Helse1 : locally_closed_tm (close_tm sigma theta t3)).
    { eapply typing_closed; eauto using env_sigma_lc, env_theta_lc. }
    assert (Helse2 : locally_closed_tm (close_tm tau psi t3)).
    { eapply typing_closed; eauto using env_tau_lc, env_psi_lc. }
    destruct Hq as [[-> ->]|[-> ->]].
    + exists a1, a2; split.
      * eapply multi_trans; [apply multi_if; eauto|].
        eapply multi_step; [apply ST_IfTrue; auto|exact Ha1].
      * split; [|exact Ha].
        eapply multi_trans; [apply multi_if; eauto|].
        eapply multi_step; [apply ST_IfTrue; auto|exact Ha2].
    + exists b1, b2; split.
      * eapply multi_trans; [apply multi_if; eauto|].
        eapply multi_step; [apply ST_IfFalse; auto|exact Hb1].
      * split; [|exact Hb].
        eapply multi_trans; [apply multi_if; eauto|].
        eapply multi_step; [apply ST_IfFalse; auto|exact Hb2].
  - exists tm_zero, tm_zero; simpl; repeat split; auto using multi_refl.
    exists 0; auto.
  - destruct (IHHtype rho eta sigma tau theta psi Henv)
      as [a [b [Ha [Hb Hn]]]].
    destruct Hn as [count [-> ->]].
    exists (numeral (S count)), (numeral (S count)).
    split; [apply multi_succ; exact Ha|].
    split; [apply multi_succ; exact Hb|].
    simpl; exists (S count); auto.
  - destruct (IHHtype1 rho eta sigma tau theta psi Henv)
      as [n1 [n2 [Hn1 [Hn2 Hn]]]].
    destruct (IHHtype2 rho eta sigma tau theta psi Henv)
      as [b1 [b2 [Hb1 [Hb2 Hb]]]].
    destruct (IHHtype3 rho eta sigma tau theta psi Henv)
      as [s1 [s2 [Hs1 [Hs2 Hs]]]].
    destruct Hn as [count [-> ->]].
    pose proof (relates_closed_inputs _ _ _ _ _ (proj1 Henv) Hb)
      as [Hbv1 Hbv2].
    pose proof (relates_closed_inputs _ _ _ _ _ (proj1 Henv) Hs)
      as [Hsv1 Hsv2].
    assert (Hbase1 : locally_closed_tm (close_tm sigma theta b)).
    { eapply typing_closed; eauto using env_sigma_lc, env_theta_lc. }
    assert (Hbase2 : locally_closed_tm (close_tm tau psi b)).
    { eapply typing_closed; eauto using env_tau_lc, env_psi_lc. }
    assert (Hstep1 : locally_closed_tm (close_tm sigma theta s)).
    { eapply typing_closed; eauto using env_sigma_lc, env_theta_lc. }
    assert (Hstep2 : locally_closed_tm (close_tm tau psi s)).
    { eapply typing_closed; eauto using env_tau_lc, env_psi_lc. }
    destruct (rec_related count T rho eta b1 b2 s1 s2
      (proj1 Henv) Hb Hs) as [r1 [r2 [Hr1 [Hr2 Hr]]]].
    exists r1, r2; split.
    + eapply multi_trans; [apply multi_rec_arg; eauto|].
      eapply multi_trans; [apply multi_rec_base; eauto using numeric_numeral|].
      eapply multi_trans; [apply multi_rec_step; eauto using numeric_numeral|exact Hr1].
    + split; [|exact Hr].
      eapply multi_trans; [apply multi_rec_arg; eauto|].
      eapply multi_trans; [apply multi_rec_base; eauto using numeric_numeral|].
      eapply multi_trans; [apply multi_rec_step; eauto using numeric_numeral|exact Hr2].
  - destruct (IHHtype1 rho eta sigma tau theta psi Henv)
      as [a [b [Ha [Hb Hab]]]].
    assert (Hleft1 : locally_closed_tm (close_tm sigma theta t1)).
    { eapply typing_closed; eauto using env_sigma_lc, env_theta_lc. }
    assert (Hleft2 : locally_closed_tm (close_tm tau psi t1)).
    { eapply typing_closed; eauto using env_tau_lc, env_psi_lc. }
    assert (Hright1 : locally_closed_tm (close_tm sigma theta t2)).
    { eapply typing_closed; eauto using env_sigma_lc, env_theta_lc. }
    assert (Hright2 : locally_closed_tm (close_tm tau psi t2)).
    { eapply typing_closed; eauto using env_tau_lc, env_psi_lc. }
    exists a, b; split.
    + eapply multi_step; [apply ST_ChoiceLeft; eauto|exact Ha].
    + split; [eapply multi_step; [apply ST_ChoiceLeft; eauto|exact Hb]|exact Hab].
Qed.

Lemma type_name_open : forall T k x y,
  In x (type_names T) ->
  In x (type_names (open_ty_rec k (Ty_FVar y) T)).
Proof.
  induction T; intros k x y H; simpl in *; auto;
    repeat rewrite in_app_iff in *; firstorder eauto.
Qed.

Lemma term_name_open : forall t k x y,
  In x (term_names t) ->
  In x (term_names (open_tm_rec k (tm_fvar y) t)).
Proof.
  induction t; intros k x y H; simpl in *; auto;
    repeat rewrite in_app_iff in *; firstorder eauto.
Qed.

Lemma term_name_ty_open : forall t k x y,
  In x (term_names t) ->
  In x (term_names (open_tm_ty_rec k (Ty_FVar y) t)).
Proof.
  induction t; intros k x y H; simpl in *; auto;
    repeat rewrite in_app_iff in *; firstorder eauto using type_name_open.
Qed.

Lemma wf_names : forall Delta T x,
  wf_ty Delta T -> In x (type_names T) -> In x Delta.
Proof.
  intros Delta T x H; induction H; simpl; intros Hname;
    try contradiction; try (rewrite in_app_iff in Hname; intuition).
  - destruct Hname as [->|[]]; assumption.
  - pose (y := fresh_name (x :: L)).
    assert (Hy : ~ In y L /\ y <> x).
    { pose proof (fresh_name_not_in (x::L)) as Hfresh.
      change (~ In y (x::L)) in Hfresh.
      split; [intro HyL; apply Hfresh; right; exact HyL|
        intro E; apply Hfresh; left; symmetry; exact E]. }
    destruct Hy as [HyL Hyx].
    pose proof (H0 y HyL
      (type_name_open T 0 x y Hname)) as Hmember.
    destruct Hmember as [E|Hmember]; [congruence|assumption].
Qed.

Lemma typing_names : forall Delta Gamma t T x,
  has_type Delta Gamma t T ->
  In x (term_names t) ->
  In x Delta \/ exists A, lookup_context x Gamma = Some A.
Proof.
  intros Delta Gamma t T x H; induction H; simpl; intros Hname;
    try contradiction.
  - destruct Hname as [->|[]]; right; eauto.
  - apply in_app_iff in Hname as [Hname|Hname].
    + left; eapply wf_names; eauto.
    + pose (y := fresh_name (x :: L)).
      assert (Hy : ~ In y L /\ y <> x).
      { pose proof (fresh_name_not_in (x::L)) as Hfresh.
        change (~ In y (x::L)) in Hfresh.
        split; [intro HyL; apply Hfresh; right; exact HyL|
          intro E; apply Hfresh; left; symmetry; exact E]. }
      destruct Hy as [HyL Hyx].
      specialize (H1 y HyL (term_name_open t2 0 x y Hname)).
      destruct H1 as [HDelta|[A Hlookup]]; [left; assumption|].
      right; exists A; simpl in Hlookup.
      assert (Nat.eqb x y = false) as E.
      { apply Nat.eqb_neq; congruence. }
      now rewrite E in Hlookup.
  - apply in_app_iff in Hname as [Hname|Hname].
    + apply IHhas_type1; assumption.
    + apply IHhas_type2; assumption.
  - pose (y := fresh_name (x :: L)).
    assert (Hy : ~ In y L /\ y <> x).
    { pose proof (fresh_name_not_in (x::L)) as Hfresh.
      change (~ In y (x::L)) in Hfresh.
      split; [intro HyL; apply Hfresh; right; exact HyL|
        intro E; apply Hfresh; left; symmetry; exact E]. }
    destruct Hy as [HyL Hyx].
    specialize (H0 y HyL (term_name_ty_open t 0 x y Hname)).
    destruct H0 as [[E|HDelta]|Hgamma].
    + congruence.
    + left; exact HDelta.
    + right; exact Hgamma.
  - apply in_app_iff in Hname as [Hname|Hname].
    + apply IHhas_type; assumption.
    + left; eapply wf_names; eauto.
  - apply in_app_iff in Hname as [Hname|Hname].
    + apply IHhas_type1; assumption.
    + apply in_app_iff in Hname as [Hname|Hname];
        [apply IHhas_type2|apply IHhas_type3]; assumption.
  - apply IHhas_type; assumption.
  - apply in_app_iff in Hname as [Hname|Hname].
    + apply IHhas_type1; assumption.
    + apply in_app_iff in Hname as [Hname|Hname];
        [apply IHhas_type2|apply IHhas_type3]; assumption.
  - apply in_app_iff in Hname as [Hname|Hname].
    + apply IHhas_type1; assumption.
    + apply IHhas_type2; assumption.
Qed.

Lemma closed_term_names : forall t T,
  has_type [] empty t T -> term_names t = [].
Proof.
  intros t T H; destruct (term_names t) as [|x xs] eqn:E; auto.
  exfalso; pose proof (typing_names [] empty t T x H) as Hsupport.
  assert (HIn : In x (term_names t)) by (rewrite E; simpl; auto).
  specialize (Hsupport HIn).
  destruct Hsupport as [HDelta|[A Hlookup]];
    [contradiction|discriminate].
Qed.

Lemma close_ty_without_names : forall T sigma,
  type_names T = [] -> close_ty sigma T = T.
Proof.
  induction T; intros sigma H; simpl in *; auto.
  - discriminate.
  - apply app_eq_nil in H as [H1 H2]; f_equal; auto.
  - f_equal; auto.
Qed.

Lemma close_tm_without_names : forall t sigma theta,
  term_names t = [] -> close_tm sigma theta t = t.
Proof.
  induction t; intros sigma theta H; simpl in *; auto.
  - discriminate.
  - apply app_eq_nil in H as [H1 H2]; f_equal;
      auto using close_ty_without_names.
  - apply app_eq_nil in H as [H1 H2]; f_equal; auto.
  - f_equal; auto.
  - apply app_eq_nil in H as [H1 H2]; f_equal;
      auto using close_ty_without_names.
  - apply app_eq_nil in H as [H1 Hrest].
    apply app_eq_nil in Hrest as [H2 H3]. f_equal; auto.
  - f_equal; auto.
  - apply app_eq_nil in H as [H1 Hrest].
    apply app_eq_nil in Hrest as [H2 H3]. f_equal; auto.
  - apply app_eq_nil in H as [H1 H2]; f_equal; auto.
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
  intros t Htype U v HU Hv Hvt.
  pose (rho := ((fun (_ : nat) (_ _ : tm) => False) : bound_relations)).
  pose (eta := ((fun (_ : atom) (_ _ : tm) => False) : free_relations)).
  pose (sigma := ((fun (_ : atom) => Ty_Bool) : atom -> ty)).
  pose (theta := ((fun (_ : atom) => tm_true) : atom -> tm)).
  assert (Henv : good_environment empty rho eta sigma sigma theta theta).
  { unfold good_environment, good_relations, rho, eta, sigma, theta;
      repeat split; intros; try contradiction; try discriminate; constructor. }
  pose proof (fundamental [] empty t
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) Htype
    rho eta sigma sigma theta theta Henv) as Hfund.
  pose proof (closed_term_names t _ Htype) as Hnames.
  rewrite (close_tm_without_names t sigma theta Hnames) in Hfund.
  destruct Hfund as [f1 [f2 [Hf1 [_ Hf]]]].
  simpl in Hf.
  destruct Hf as [_ [_ Hall]].
  pose (R := ((fun a b => a = v /\ b = v) : value_relation)).
  destruct (Hall U U R (wf_ty_lc _ _ HU) (wf_ty_lc _ _ HU)
    (fun a b Hab => match Hab with conj Ha Hb =>
      conj (eq_rect _ value Hv _ (eq_sym Ha))
           (eq_rect _ value Hv _ (eq_sym Hb)) end))
    as [g1 [g2 [Hg1 [_ Hg]]]].
  simpl in Hg.
  destruct Hg as [_ [_ Happ]].
  destruct (Happ v v (conj eq_refl eq_refl))
    as [z1 [z2 [Hz1 [_ Hz]]]].
  destruct Hz as [-> _].
  eapply multi_trans.
  - apply multi_app_left.
    + apply multi_tapp; [exact Hf1|eapply wf_ty_lc; eauto].
    + apply value_closed; exact Hv.
  - eapply multi_trans.
    + apply multi_app_left; [exact Hg1|apply value_closed; exact Hv].
    + exact Hz1.
Qed.

End SystemFParametricityIfNondeterminismRecursionHardTask.
