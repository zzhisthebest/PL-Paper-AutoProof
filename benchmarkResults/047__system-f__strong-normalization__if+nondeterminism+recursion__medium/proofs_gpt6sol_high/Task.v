(** System F CBV strong-normalization benchmark, Medium variant.
    Features: if-nondeterminism-recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFNormalizationIfNondeterminismRecursionMediumTask.

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

Inductive strongly_normalizing : tm -> Prop :=
  | SN_intro : forall t,
      (forall u, t --> u -> strongly_normalizing u) -> strongly_normalizing t.

Hint Constructors lc_ty_at lc_tm_at value : core.

Definition type_substitution := atom -> ty.

Definition term_substitution := atom -> tm.

Fixpoint instantiate_ty (theta : type_substitution) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => theta X
  | Ty_Arrow T1 T2 =>
      Ty_Arrow (instantiate_ty theta T1) (instantiate_ty theta T2)
  | Ty_All T1 => Ty_All (instantiate_ty theta T1)
  | Ty_Bool => Ty_Bool
  | Ty_Nat => Ty_Nat
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
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (instantiate theta gamma t1) (instantiate theta gamma t2) (instantiate theta gamma t3)
  | tm_zero => tm_zero
  | tm_succ t => tm_succ (instantiate theta gamma t)
  | tm_natrec n b s => tm_natrec (instantiate theta gamma n) (instantiate theta gamma b) (instantiate theta gamma s)
  | tm_choice t1 t2 => tm_choice (instantiate theta gamma t1) (instantiate theta gamma t2)
  end.

Definition type_substitution_closed (theta : type_substitution) : Prop :=
  forall X : atom, locally_closed_ty (theta X).

Definition term_substitution_closed (gamma : term_substitution) : Prop :=
  forall x : atom, locally_closed_tm (gamma x).

Definition relation := tm -> Prop.
Record value_candidate := {
  candidate_relation : relation;
  candidate_values : forall v, candidate_relation v -> value v
}.
Definition relation_env := atom -> option value_candidate.
Definition relation_update (rho : relation_env) (X : atom) (a : value_candidate) :=
  fun Y => if Nat.eqb X Y then Some a else rho Y.

Definition expression_lifting (R : relation) (t : tm) : Prop :=
  locally_closed_tm t /\ strongly_normalizing t /\
  forall v, t -->* v -> value v -> R v.

Fixpoint value_relation (eta : list value_candidate) (rho : relation_env)
    (T : ty) (v : tm) : Prop :=
  match T with
  | Ty_BVar i =>
      match nth_error eta i with Some a => a.(candidate_relation) v | None => False end
  | Ty_FVar X =>
      match rho X with Some a => a.(candidate_relation) v | None => False end
  | Ty_Arrow T1 T2 =>
      value v /\ exists U body, v = tm_abs U body /\
      forall arg, value_relation eta rho T1 arg ->
        expression_lifting (value_relation eta rho T2) (open_tm body arg)
  | Ty_All T =>
      value v /\ exists body, v = tm_tabs body /\
      forall (U : ty) (a : value_candidate), locally_closed_ty U ->
        expression_lifting (value_relation (a :: eta) rho T) (open_tm_ty body U)
  | Ty_Bool => value v /\ (v = tm_true \/ v = tm_false)
  | Ty_Nat => value v /\ numeric_value v
  end.

Definition expression_relation eta rho T t :=
  expression_lifting (value_relation eta rho T) t.

Definition related_substitution (rho : relation_env) (Gamma : context)
    (gamma : term_substitution) : Prop :=
  forall x T, lookup_context x Gamma = Some T -> value_relation [] rho T (gamma x).

Lemma lc_numeric_value : forall n, numeric_value n -> locally_closed_tm n.
Proof.
  intros n H; induction H; unfold locally_closed_tm in *; eauto.
Qed.

Lemma value_locally_closed : forall v, value v -> locally_closed_tm v.
Proof.
  intros v H; inversion H; subst; eauto using lc_numeric_value.
  all: unfold locally_closed_tm; eauto.
Qed.

Lemma numeric_value_no_step : forall n u,
  numeric_value n -> ~ n --> u.
Proof.
  intros n u Hn; revert u; induction Hn; intros u Hstep;
    inversion Hstep; subst; eauto.
  eapply IHHn; eauto.
Qed.

Lemma value_no_step : forall v u, value v -> ~ v --> u.
Proof.
  intros v u Hv Hstep; inversion Hv; subst.
  - inversion Hstep.
  - inversion Hstep.
  - inversion Hstep.
  - inversion Hstep.
  - eapply numeric_value_no_step; eauto.
Qed.

Lemma value_strongly_normalizing : forall v, value v -> strongly_normalizing v.
Proof.
  intros v Hv; constructor; intros u Hu;
    exfalso; eapply value_no_step; eauto.
Qed.

Lemma multi_trans : forall t u v, t -->* u -> u -->* v -> t -->* v.
Proof.
  intros t u v Htu Huv; induction Htu; eauto using multi.
Qed.

Lemma sn_step : forall t u,
  strongly_normalizing t -> t --> u -> strongly_normalizing u.
Proof.
  intros t u Hsn Hstep; inversion Hsn; eauto.
Qed.

Lemma sn_multi : forall t u,
  strongly_normalizing t -> t -->* u -> strongly_normalizing u.
Proof.
  intros t u Hsn Hmulti; induction Hmulti; eauto using sn_step.
Qed.

Lemma expression_lifting_step : forall R t u,
  expression_lifting R t -> t --> u ->
  strongly_normalizing u /\
  (forall v, u -->* v -> value v -> R v).
Proof.
  intros R t u [_ [Hsn HR]] Hstep; split.
  - eauto using sn_step.
  - intros v Hmulti Hv; apply HR with (v := v); eauto using multi.
Qed.

Definition fresh_atom (L : list atom) : atom :=
  S (fold_right Nat.max 0 L).

Lemma in_le_list_max : forall L x, In x L -> x <= fold_right Nat.max 0 L.
Proof.
  induction L as [|y L IH]; intros x H; simpl in *.
  - contradiction.
  - destruct H as [H | H]; subst.
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; exact H | apply Nat.le_max_r].
Qed.

Lemma fresh_atom_not_in : forall L, ~ In (fresh_atom L) L.
Proof.
  intros L H; unfold fresh_atom in H.
  pose proof (in_le_list_max L _ H); lia.
Qed.

Lemma lc_ty_open_inv : forall T k X,
  lc_ty_at k (open_ty_rec k (Ty_FVar X) T) -> lc_ty_at (S k) T.
Proof.
  induction T; intros k X H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E; inversion H; subst;
      apply lc_ty_bvar; try apply Nat.eqb_eq in E; lia.
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
  - destruct (Nat.eqb k n) eqn:E; inversion H; subst;
      apply lc_tm_bvar; try apply Nat.eqb_eq in E; lia.
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

Lemma lc_tm_ty_open_inv : forall t K k X,
  lc_tm_at K k (open_tm_ty_rec K (Ty_FVar X) t) ->
  lc_tm_at (S K) k t.
Proof.
  induction t; intros K k X H; simpl in H.
  - inversion H; subst; constructor; assumption.
  - constructor.
  - inversion H; subst; constructor; eauto using lc_ty_open_inv.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto using lc_ty_open_inv.
  - constructor.
  - constructor.
  - inversion H; subst; constructor; eauto.
  - constructor.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
Qed.

Lemma wf_ty_locally_closed : forall Delta T,
  wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H; induction H; unfold locally_closed_ty in *;
    eauto using lc_ty_at.
  - pose (X := fresh_atom L).
    specialize (H X (fresh_atom_not_in L)).
    specialize (H0 X (fresh_atom_not_in L)).
    unfold open_ty in H0.
    eapply lc_ty_open_inv in H0.
    constructor; exact H0.
Qed.

Lemma typing_locally_closed : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T H; induction H; unfold locally_closed_tm in *;
    eauto using lc_tm_at, wf_ty_locally_closed.
  - pose (x := fresh_atom L).
    specialize (H0 x (fresh_atom_not_in L)).
    specialize (H1 x (fresh_atom_not_in L)).
    unfold open_tm in H1.
    apply lc_tm_abs; [exact (wf_ty_locally_closed Delta T1 H) |].
    eapply lc_tm_open_inv; exact H1.
  - pose (X := fresh_atom L).
    specialize (H X (fresh_atom_not_in L)).
    specialize (H0 X (fresh_atom_not_in L)).
    unfold open_tm_ty in H0.
    apply lc_tm_tabs; eapply lc_tm_ty_open_inv; exact H0.
  - eapply lc_tm_tapp; [exact IHhas_type | exact (wf_ty_locally_closed Delta U H0)].
Qed.

Lemma lc_ty_at_weaken : forall T k j,
  lc_ty_at k T -> k <= j -> lc_ty_at j T.
Proof.
  intros T k j H; revert j; induction H; intros j Hj.
  - apply lc_ty_bvar; lia.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; eauto.
  - apply lc_ty_all; apply IHlc_ty_at; lia.
  - apply lc_ty_bool.
  - apply lc_ty_nat.
Qed.

Lemma lc_tm_at_weaken : forall t K k J j,
  lc_tm_at K k t -> K <= J -> k <= j -> lc_tm_at J j t.
Proof.
  intros t K k J j H; revert J j; induction H; intros J j HJ Hj.
  - apply lc_tm_bvar; lia.
  - apply lc_tm_fvar.
  - apply lc_tm_abs; [eapply lc_ty_at_weaken; eauto | apply IHlc_tm_at; lia].
  - apply lc_tm_app; eauto.
  - apply lc_tm_tabs; apply IHlc_tm_at; lia.
  - apply lc_tm_tapp; [apply IHlc_tm_at; lia | eapply lc_ty_at_weaken; eauto].
  - apply lc_tm_true.
  - apply lc_tm_false.
  - apply lc_tm_if; eauto.
  - apply lc_tm_zero.
  - apply lc_tm_succ; eauto.
  - apply lc_tm_rec; eauto.
  - apply lc_tm_choice; eauto.
Qed.

Lemma instantiate_ty_lc_at : forall T K theta,
  lc_ty_at K T -> type_substitution_closed theta ->
  lc_ty_at K (instantiate_ty theta T).
Proof.
  intros T K theta H; induction H; intros Htheta; simpl.
  - apply lc_ty_bvar; assumption.
  - unfold type_substitution_closed, locally_closed_ty in Htheta.
    eapply lc_ty_at_weaken; [apply Htheta | lia].
  - apply lc_ty_arrow; eauto.
  - apply lc_ty_all; eauto.
  - apply lc_ty_bool.
  - apply lc_ty_nat.
Qed.

Lemma instantiate_lc_at : forall t K k theta gamma,
  lc_tm_at K k t ->
  type_substitution_closed theta -> term_substitution_closed gamma ->
  lc_tm_at K k (instantiate theta gamma t).
Proof.
  intros t K k theta gamma H; induction H; intros Htheta Hgamma; simpl.
  - apply lc_tm_bvar; assumption.
  - unfold term_substitution_closed, locally_closed_tm in Hgamma.
    eapply lc_tm_at_weaken; [apply Hgamma | lia | lia].
  - apply lc_tm_abs; eauto using instantiate_ty_lc_at.
  - apply lc_tm_app; eauto.
  - apply lc_tm_tabs; eauto.
  - apply lc_tm_tapp; eauto using instantiate_ty_lc_at.
  - apply lc_tm_true.
  - apply lc_tm_false.
  - apply lc_tm_if; eauto.
  - apply lc_tm_zero.
  - apply lc_tm_succ; eauto.
  - apply lc_tm_rec; eauto.
  - apply lc_tm_choice; eauto.
Qed.

Lemma instantiate_lc : forall theta gamma t,
  type_substitution_closed theta -> term_substitution_closed gamma ->
  locally_closed_tm t -> locally_closed_tm (instantiate theta gamma t).
Proof.
  intros theta gamma t Htheta Hgamma Hlc.
  exact (instantiate_lc_at t 0 0 theta gamma Hlc Htheta Hgamma).
Qed.

Lemma value_relation_value : forall T eta rho v,
  value_relation eta rho T v -> value v.
Proof.
  induction T; intros eta rho v H; simpl in H; try tauto.
  - destruct (nth_error eta n) as [a|] eqn:E; [eapply candidate_values; eauto|contradiction].
  - destruct (rho a) as [r|] eqn:E; [eapply candidate_values; eauto|contradiction].
Qed.

Lemma value_relation_lc : forall T eta rho v,
  value_relation eta rho T v -> locally_closed_tm v.
Proof.
  intros T eta rho v H; apply value_locally_closed.
  eapply value_relation_value; eauto.
Qed.

Fixpoint ty_fvars (T : ty) : list atom :=
  match T with
  | Ty_FVar X => [X]
  | Ty_Arrow A B => ty_fvars A ++ ty_fvars B
  | Ty_All A => ty_fvars A
  | _ => []
  end.

Fixpoint tm_fvars (t : tm) : list atom :=
  match t with
  | tm_fvar x => [x]
  | tm_abs _ b | tm_tabs b | tm_tapp b _ | tm_succ b => tm_fvars b
  | tm_app a b | tm_choice a b => tm_fvars a ++ tm_fvars b
  | tm_if a b c | tm_natrec a b c =>
      tm_fvars a ++ tm_fvars b ++ tm_fvars c
  | _ => []
  end.

Fixpoint tm_ty_fvars (t : tm) : list atom :=
  match t with
  | tm_abs T b => ty_fvars T ++ tm_ty_fvars b
  | tm_tabs b | tm_succ b => tm_ty_fvars b
  | tm_tapp b T => tm_ty_fvars b ++ ty_fvars T
  | tm_app a b | tm_choice a b => tm_ty_fvars a ++ tm_ty_fvars b
  | tm_if a b c | tm_natrec a b c =>
      tm_ty_fvars a ++ tm_ty_fvars b ++ tm_ty_fvars c
  | _ => []
  end.

Fixpoint context_ty_fvars (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (_, T) :: rest => ty_fvars T ++ context_ty_fvars rest
  end.

Definition term_update (gamma : term_substitution) (x : atom) (v : tm) :=
  fun y => if Nat.eqb x y then v else gamma y.

Definition type_update (theta : type_substitution) (X : atom) (U : ty) :=
  fun Y => if Nat.eqb X Y then U else theta Y.

Lemma not_in_app : forall (A : Type) (x : A) l1 l2,
  ~ In x (l1 ++ l2) -> ~ In x l1 /\ ~ In x l2.
Proof.
  intros A x l1 l2 H; rewrite in_app_iff in H; tauto.
Qed.

Lemma term_update_closed : forall gamma x v,
  term_substitution_closed gamma -> locally_closed_tm v ->
  term_substitution_closed (term_update gamma x v).
Proof.
  intros gamma x v Hgamma Hv y; unfold term_update.
  destruct (Nat.eqb x y); auto.
Qed.

Lemma type_update_closed : forall theta X U,
  type_substitution_closed theta -> locally_closed_ty U ->
  type_substitution_closed (type_update theta X U).
Proof.
  intros theta X U Htheta HU Y; unfold type_update.
  destruct (Nat.eqb X Y); auto.
Qed.

Lemma instantiate_ty_update_irrel : forall T theta X U,
  ~ In X (ty_fvars T) ->
  instantiate_ty (type_update theta X U) T = instantiate_ty theta T.
Proof.
  induction T; intros theta X U Hfresh; simpl in *; try reflexivity.
  - unfold type_update. assert (X <> a) by (intro E; subst; apply Hfresh; auto).
    apply Nat.eqb_neq in H; rewrite H; reflexivity.
  - apply not_in_app in Hfresh as [H1 H2].
    rewrite IHT1 by exact H1; rewrite IHT2 by exact H2; reflexivity.
  - rewrite IHT by exact Hfresh; reflexivity.
Qed.

Lemma instantiate_term_update_irrel : forall t theta gamma x v,
  ~ In x (tm_fvars t) ->
  instantiate theta (term_update gamma x v) t = instantiate theta gamma t.
Proof.
  induction t; intros theta gamma x v Hfresh; simpl in *; try reflexivity;
    try (rewrite IHt by exact Hfresh; reflexivity);
    try (apply not_in_app in Hfresh as [H1 H2];
      rewrite IHt1 by exact H1; rewrite IHt2 by exact H2; reflexivity);
    try (repeat (apply not_in_app in Hfresh as [H1 Hfresh]);
      rewrite IHt1 by exact H1;
      rewrite IHt2 by (apply not_in_app in Hfresh; tauto);
      rewrite IHt3 by (apply not_in_app in Hfresh; tauto); reflexivity).
  unfold term_update.
  assert (x <> a) by (intro E; subst; apply Hfresh; auto).
  apply Nat.eqb_neq in H; rewrite H; reflexivity.
Qed.

Lemma instantiate_type_update_irrel : forall t theta gamma X U,
  ~ In X (tm_ty_fvars t) ->
  instantiate (type_update theta X U) gamma t = instantiate theta gamma t.
Proof.
  induction t; intros theta gamma X U Hfresh; simpl in *; try reflexivity;
    try (rewrite IHt by exact Hfresh; reflexivity);
    try (apply not_in_app in Hfresh as [H1 H2];
      rewrite IHt1 by exact H1; rewrite IHt2 by exact H2; reflexivity).
  - apply not_in_app in Hfresh as [H1 H2].
    rewrite instantiate_ty_update_irrel by exact H1.
    rewrite IHt by exact H2; reflexivity.
  - apply not_in_app in Hfresh as [H1 H2].
    rewrite IHt by exact H1.
    rewrite instantiate_ty_update_irrel by exact H2; reflexivity.
  - repeat (apply not_in_app in Hfresh as [H1 Hfresh]).
    rewrite IHt1 by exact H1.
    rewrite IHt2 by (apply not_in_app in Hfresh; tauto).
    rewrite IHt3 by (apply not_in_app in Hfresh; tauto).
    reflexivity.
  - repeat (apply not_in_app in Hfresh as [H1 Hfresh]).
    rewrite IHt1 by exact H1.
    rewrite IHt2 by (apply not_in_app in Hfresh; tauto).
    rewrite IHt3 by (apply not_in_app in Hfresh; tauto).
    reflexivity.
Qed.

Lemma open_ty_rec_lc_id : forall T K k U,
  lc_ty_at K T -> K <= k -> open_ty_rec k U T = T.
Proof.
  intros T K k U H; revert k U; induction H; intros j U Hj; simpl;
    try reflexivity.
  - assert (Nat.eqb j i = false) as E by (apply Nat.eqb_neq; lia).
    rewrite E; reflexivity.
  - rewrite IHlc_ty_at1 by lia; rewrite IHlc_ty_at2 by lia; reflexivity.
  - rewrite IHlc_ty_at by lia; reflexivity.
Qed.

Lemma open_tm_rec_lc_id : forall t K k j u,
  lc_tm_at K k t -> k <= j -> open_tm_rec j u t = t.
Proof.
  intros t K k j u H; revert j u; induction H; intros j u Hj; simpl;
    try reflexivity.
  - assert (Nat.eqb j i = false) as E by (apply Nat.eqb_neq; lia).
    rewrite E; reflexivity.
  - rewrite IHlc_tm_at by lia; reflexivity.
  - rewrite IHlc_tm_at1 by lia; rewrite IHlc_tm_at2 by lia; reflexivity.
  - rewrite IHlc_tm_at by lia; reflexivity.
  - rewrite IHlc_tm_at by lia; reflexivity.
  - rewrite IHlc_tm_at1 by lia; rewrite IHlc_tm_at2 by lia;
      rewrite IHlc_tm_at3 by lia; reflexivity.
  - rewrite IHlc_tm_at by lia; reflexivity.
  - rewrite IHlc_tm_at1 by lia; rewrite IHlc_tm_at2 by lia;
      rewrite IHlc_tm_at3 by lia; reflexivity.
  - rewrite IHlc_tm_at1 by lia; rewrite IHlc_tm_at2 by lia; reflexivity.
Qed.

Lemma open_tm_ty_rec_lc_id : forall t K k j U,
  lc_tm_at K k t -> K <= j -> open_tm_ty_rec j U t = t.
Proof.
  intros t K k j U H; revert j U; induction H; intros j U Hj; simpl;
    try reflexivity.
  - rewrite (open_ty_rec_lc_id T K j U H Hj).
    rewrite IHlc_tm_at by lia; reflexivity.
  - rewrite IHlc_tm_at1 by lia; rewrite IHlc_tm_at2 by lia; reflexivity.
  - rewrite IHlc_tm_at by lia; reflexivity.
  - rewrite IHlc_tm_at by lia.
    rewrite (open_ty_rec_lc_id T K j U H0 Hj); reflexivity.
  - rewrite IHlc_tm_at1 by lia; rewrite IHlc_tm_at2 by lia;
      rewrite IHlc_tm_at3 by lia; reflexivity.
  - rewrite IHlc_tm_at by lia; reflexivity.
  - rewrite IHlc_tm_at1 by lia; rewrite IHlc_tm_at2 by lia;
      rewrite IHlc_tm_at3 by lia; reflexivity.
  - rewrite IHlc_tm_at1 by lia; rewrite IHlc_tm_at2 by lia; reflexivity.
Qed.

Lemma instantiate_open_tm_rec : forall t k x theta gamma,
  term_substitution_closed gamma ->
  instantiate theta gamma (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k (gamma x) (instantiate theta gamma t).
Proof.
  induction t; intros k x theta gamma Hgamma; simpl;
    try reflexivity;
    try (rewrite IHt by exact Hgamma; reflexivity);
    try (rewrite IHt1 by exact Hgamma; rewrite IHt2 by exact Hgamma;
      reflexivity);
    try (rewrite IHt1 by exact Hgamma; rewrite IHt2 by exact Hgamma;
      rewrite IHt3 by exact Hgamma; reflexivity).
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry; apply open_tm_rec_lc_id with (K := 0) (k := 0);
      [apply Hgamma | lia].
Qed.

Lemma instantiate_ty_open_update : forall T k X U theta,
  type_substitution_closed theta -> ~ In X (ty_fvars T) ->
  instantiate_ty (type_update theta X U)
    (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k U (instantiate_ty theta T).
Proof.
  induction T; intros k X U theta Htheta Hfresh; simpl in *;
    try reflexivity.
  - destruct (Nat.eqb k n) eqn:E; simpl.
    + unfold type_update; rewrite Nat.eqb_refl; reflexivity.
    + reflexivity.
  - unfold type_update.
    assert (X <> a) by (intro E; subst; apply Hfresh; auto).
    apply Nat.eqb_neq in H; rewrite H.
    symmetry; eapply open_ty_rec_lc_id; [apply Htheta | lia].
  - apply not_in_app in Hfresh as [H1 H2].
    rewrite IHT1 by assumption; rewrite IHT2 by assumption; reflexivity.
  - rewrite IHT by assumption; reflexivity.
Qed.

Lemma instantiate_open_tm_ty_update : forall t k X U theta gamma,
  type_substitution_closed theta -> term_substitution_closed gamma ->
  ~ In X (tm_ty_fvars t) ->
  instantiate (type_update theta X U) gamma
    (open_tm_ty_rec k (Ty_FVar X) t) =
  open_tm_ty_rec k U (instantiate theta gamma t).
Proof.
  induction t; intros k X U theta gamma Htheta Hgamma Hfresh;
    simpl in *; try reflexivity;
    try (rewrite IHt by assumption; reflexivity);
    try (apply not_in_app in Hfresh as [H1 H2];
      rewrite IHt1 by assumption; rewrite IHt2 by assumption; reflexivity).
  - symmetry; eapply open_tm_ty_rec_lc_id; [apply Hgamma | lia].
  - apply not_in_app in Hfresh as [H1 H2].
    rewrite instantiate_ty_open_update by assumption.
    rewrite IHt by assumption; reflexivity.
  - apply not_in_app in Hfresh as [H1 H2].
    rewrite IHt by assumption.
    rewrite instantiate_ty_open_update by assumption; reflexivity.
  - repeat (apply not_in_app in Hfresh as [H1 Hfresh]).
    rewrite IHt1 by assumption.
    rewrite IHt2 by (apply not_in_app in Hfresh; tauto).
    rewrite IHt3 by (apply not_in_app in Hfresh; tauto).
    reflexivity.
  - repeat (apply not_in_app in Hfresh as [H1 Hfresh]).
    rewrite IHt1 by assumption.
    rewrite IHt2 by (apply not_in_app in Hfresh; tauto).
    rewrite IHt3 by (apply not_in_app in Hfresh; tauto).
    reflexivity.
Qed.

Lemma expression_lifting_iff : forall R S t,
  (forall v, R v <-> S v) ->
  expression_lifting R t <-> expression_lifting S t.
Proof.
  intros R S t H; unfold expression_lifting; split.
  - intros [Hlc [Hsn Hrel]]; split; [exact Hlc|]; split; [exact Hsn|].
    intros v Hmulti Hv; apply (proj1 (H v)); exact (Hrel v Hmulti Hv).
  - intros [Hlc [Hsn Hrel]]; split; [exact Hlc|]; split; [exact Hsn|].
    intros v Hmulti Hv; apply (proj2 (H v)); exact (Hrel v Hmulti Hv).
Qed.

Lemma arrow_semantic_iff : forall (A B C D : relation) v,
  (forall x, A x <-> C x) -> (forall x, B x <-> D x) ->
  (value v /\ exists U body, v = tm_abs U body /\
    forall arg, A arg -> expression_lifting B (open_tm body arg)) <->
  (value v /\ exists U body, v = tm_abs U body /\
    forall arg, C arg -> expression_lifting D (open_tm body arg)).
Proof.
  intros A B C D v HA HB; split.
  - intros [Hv [U [body [E Hfun]]]]; split; [exact Hv|].
    exists U, body; split; [exact E|]; intros arg Harg.
    apply (proj1 (expression_lifting_iff B D _ HB));
      apply Hfun; apply (proj2 (HA arg)); exact Harg.
  - intros [Hv [U [body [E Hfun]]]]; split; [exact Hv|].
    exists U, body; split; [exact E|]; intros arg Harg.
    apply (proj2 (expression_lifting_iff B D _ HB));
      apply Hfun; apply (proj1 (HA arg)); exact Harg.
Qed.

Lemma all_semantic_iff : forall
    (R S : ty -> value_candidate -> relation) v,
  (forall U a w, locally_closed_ty U -> R U a w <-> S U a w) ->
  (value v /\ exists body, v = tm_tabs body /\
    forall U a, locally_closed_ty U ->
      expression_lifting (R U a) (open_tm_ty body U)) <->
  (value v /\ exists body, v = tm_tabs body /\
    forall U a, locally_closed_ty U ->
      expression_lifting (S U a) (open_tm_ty body U)).
Proof.
  intros R S v HR; split.
  - intros [Hv [body [E Hfun]]]; split; [exact Hv|].
    exists body; split; [exact E|]; intros U a HU.
    apply (proj1 (expression_lifting_iff (R U a) (S U a) _
      (fun w => HR U a w HU))); exact (Hfun U a HU).
  - intros [Hv [body [E Hfun]]]; split; [exact Hv|].
    exists body; split; [exact E|]; intros U a HU.
    apply (proj2 (expression_lifting_iff (R U a) (S U a) _
      (fun w => HR U a w HU))); exact (Hfun U a HU).
Qed.

Lemma nth_error_app_single : forall (A : Type) (eta : list A) a i,
  nth_error (eta ++ [a]) i =
  if Nat.eqb i (length eta) then Some a else nth_error eta i.
Proof.
  intros A eta; induction eta as [|b eta IH]; intros a i.
  - destruct i; simpl; [reflexivity | rewrite nth_error_nil; reflexivity].
  - destruct i; simpl; [reflexivity | apply IH].
Qed.

Lemma value_relation_eta_suffix : forall T k eta suffix rho v,
  lc_ty_at k T -> length eta = k ->
  value_relation eta rho T v <->
  value_relation (eta ++ suffix) rho T v.
Proof.
  intros T k eta suffix rho v Hlc; revert eta suffix rho v;
    induction Hlc; intros eta suffix rho v Hlen; simpl.
  - rewrite nth_error_app1 by lia; reflexivity.
  - reflexivity.
  - apply arrow_semantic_iff.
    + intros x; apply IHHlc1; exact Hlen.
    + intros x; apply IHHlc2; exact Hlen.
  - apply all_semantic_iff; intros U a w HU.
    change (value_relation (a :: eta) rho T w <->
      value_relation (a :: eta ++ suffix) rho T w).
    apply (IHHlc (a :: eta) suffix rho w); simpl; lia.
  - reflexivity.
  - reflexivity.
Qed.

Lemma value_relation_eta_irrel : forall U eta rho v,
  locally_closed_ty U ->
  value_relation [] rho U v <-> value_relation eta rho U v.
Proof.
  intros U eta rho v HU.
  exact (value_relation_eta_suffix U 0 [] eta rho v HU eq_refl).
Qed.

Lemma value_relation_open_fvar : forall T k eta rho X cand v,
  length eta = k -> ~ In X (ty_fvars T) ->
  value_relation eta (relation_update rho X cand)
    (open_ty_rec k (Ty_FVar X) T) v <->
  value_relation (eta ++ [cand]) rho T v.
Proof.
  induction T; intros k eta rho X cand v Hlen Hfresh; simpl in *.
  - destruct (Nat.eqb k n) eqn:E; simpl.
    + apply Nat.eqb_eq in E; subst.
      unfold relation_update; rewrite Nat.eqb_refl.
      rewrite nth_error_app_single, Nat.eqb_refl; reflexivity.
    + rewrite nth_error_app_single, Hlen.
      rewrite Nat.eqb_sym, E; reflexivity.
  - assert (X <> a) by (intro Heq; subst; apply Hfresh; auto).
    unfold relation_update; apply Nat.eqb_neq in H; rewrite H; reflexivity.
  - apply not_in_app in Hfresh as [H1 H2].
    apply arrow_semantic_iff.
    + intros w; apply IHT1; assumption.
    + intros w; apply IHT2; assumption.
  - apply all_semantic_iff; intros U b w HU.
    change (value_relation (b :: eta) (relation_update rho X cand)
      (open_ty_rec (S k) (Ty_FVar X) T) w <->
      value_relation ((b :: eta) ++ [cand]) rho T w).
    apply IHT; [simpl; lia | exact Hfresh].
  - reflexivity.
  - reflexivity.
Qed.

Lemma value_relation_open_ty : forall T k eta rho U cand v,
  length eta = k -> locally_closed_ty U ->
  (forall w, candidate_relation cand w <-> value_relation [] rho U w) ->
  value_relation eta rho (open_ty_rec k U T) v <->
  value_relation (eta ++ [cand]) rho T v.
Proof.
  induction T; intros k eta rho U cand v Hlen HU Ha; simpl.
  - destruct (Nat.eqb k n) eqn:E; simpl.
    + apply Nat.eqb_eq in E; subst.
      rewrite nth_error_app_single, Nat.eqb_refl.
      transitivity (value_relation [] rho U v).
      * symmetry; apply value_relation_eta_irrel; exact HU.
      * symmetry; apply Ha.
    + rewrite nth_error_app_single, Hlen.
      rewrite Nat.eqb_sym, E; reflexivity.
  - reflexivity.
  - apply arrow_semantic_iff.
    + intros w; apply IHT1; assumption.
    + intros w; apply IHT2; assumption.
  - apply all_semantic_iff; intros V b w HV.
    change (value_relation (b :: eta) rho (open_ty_rec (S k) U T) w <->
      value_relation ((b :: eta) ++ [cand]) rho T w).
    apply IHT; [simpl; lia | exact HU | exact Ha].
  - reflexivity.
  - reflexivity.
Qed.

Lemma value_relation_rho_update_irrel : forall T eta rho X cand v,
  ~ In X (ty_fvars T) ->
  value_relation eta (relation_update rho X cand) T v <->
  value_relation eta rho T v.
Proof.
  induction T; intros eta rho X cand v Hfresh; simpl in *;
    try reflexivity.
  - assert (X <> a) by (intro E; subst; apply Hfresh; auto).
    unfold relation_update; apply Nat.eqb_neq in H; rewrite H; reflexivity.
  - apply not_in_app in Hfresh as [H1 H2].
    apply arrow_semantic_iff.
    + intros w; apply IHT1; exact H1.
    + intros w; apply IHT2; exact H2.
  - apply all_semantic_iff; intros U b w HU.
    apply IHT; exact Hfresh.
Qed.

Lemma lookup_context_type_fvars : forall Gamma x T X,
  lookup_context x Gamma = Some T ->
  In X (ty_fvars T) -> In X (context_ty_fvars Gamma).
Proof.
  induction Gamma as [|[y U] Gamma IH]; intros x T X Hlookup Hin;
    simpl in *; try discriminate.
  destruct (Nat.eqb x y) eqn:E.
  - inversion Hlookup; subst; apply in_or_app; left; exact Hin.
  - apply in_or_app; right; eapply IH; eauto.
Qed.

Lemma related_substitution_rho_update : forall rho Gamma gamma X cand,
  related_substitution rho Gamma gamma ->
  ~ In X (context_ty_fvars Gamma) ->
  related_substitution (relation_update rho X cand) Gamma gamma.
Proof.
  intros rho Gamma gamma X cand Hrelated Hfresh x T Hlookup.
  assert (Hnot : ~ In X (ty_fvars T)).
  { intro Hin; apply Hfresh; eapply lookup_context_type_fvars; eauto. }
  apply (proj2 (value_relation_rho_update_irrel T [] rho X cand (gamma x) Hnot)).
  exact (Hrelated x T Hlookup).
Qed.

Lemma open_ty_rec_lc : forall T K U,
  lc_ty_at (S K) T -> lc_ty_at K U ->
  lc_ty_at K (open_ty_rec K U T).
Proof.
  induction T; intros K U Hlc HU; simpl in *.
  - inversion Hlc; subst.
    destruct (Nat.eqb K n) eqn:E; [exact HU|].
    apply lc_ty_bvar; apply Nat.eqb_neq in E; lia.
  - apply lc_ty_fvar.
  - inversion Hlc; subst; apply lc_ty_arrow; eauto.
  - inversion Hlc; subst; apply lc_ty_all.
    apply IHT; [assumption | eapply lc_ty_at_weaken; eauto; lia].
  - apply lc_ty_bool.
  - apply lc_ty_nat.
Qed.

Lemma open_tm_rec_lc : forall t K k u,
  lc_tm_at K (S k) t -> lc_tm_at K 0 u ->
  lc_tm_at K k (open_tm_rec k u t).
Proof.
  induction t; intros K k u Hlc Hu; simpl in *.
  - inversion Hlc; subst.
    destruct (Nat.eqb k n) eqn:E.
    + eapply lc_tm_at_weaken; [exact Hu | lia | lia].
    + apply lc_tm_bvar; apply Nat.eqb_neq in E; lia.
  - apply lc_tm_fvar.
  - inversion Hlc; subst; apply lc_tm_abs; eauto.
  - inversion Hlc; subst; apply lc_tm_app; eauto.
  - inversion Hlc; subst; apply lc_tm_tabs.
    apply IHt; [assumption | eapply lc_tm_at_weaken; eauto; lia].
  - inversion Hlc; subst; apply lc_tm_tapp; eauto.
  - apply lc_tm_true.
  - apply lc_tm_false.
  - inversion Hlc; subst; apply lc_tm_if; eauto.
  - apply lc_tm_zero.
  - inversion Hlc; subst; apply lc_tm_succ; eauto.
  - inversion Hlc; subst; apply lc_tm_rec; eauto.
  - inversion Hlc; subst; apply lc_tm_choice; eauto.
Qed.

Lemma open_tm_ty_rec_lc : forall t K k U,
  lc_tm_at (S K) k t -> lc_ty_at K U ->
  lc_tm_at K k (open_tm_ty_rec K U t).
Proof.
  induction t; intros K k U Hlc HU; simpl in *.
  - inversion Hlc; subst; apply lc_tm_bvar; assumption.
  - apply lc_tm_fvar.
  - inversion Hlc; subst; apply lc_tm_abs; eauto using open_ty_rec_lc.
  - inversion Hlc; subst; apply lc_tm_app; eauto.
  - inversion Hlc; subst; apply lc_tm_tabs.
    apply IHt; [assumption | eapply lc_ty_at_weaken; eauto; lia].
  - inversion Hlc; subst; apply lc_tm_tapp; eauto using open_ty_rec_lc.
  - apply lc_tm_true.
  - apply lc_tm_false.
  - inversion Hlc; subst; apply lc_tm_if; eauto.
  - apply lc_tm_zero.
  - inversion Hlc; subst; apply lc_tm_succ; eauto.
  - inversion Hlc; subst; apply lc_tm_rec; eauto.
  - inversion Hlc; subst; apply lc_tm_choice; eauto.
Qed.

Lemma step_preserves_lc : forall t u,
  t --> u -> locally_closed_tm t -> locally_closed_tm u.
Proof.
  intros t u Hstep; induction Hstep; intros Hlc;
    unfold locally_closed_tm in *; inversion Hlc; subst;
    eauto using lc_tm_at, value_locally_closed, lc_numeric_value.
  - inversion H; subst.
    eapply open_tm_rec_lc; [eassumption |].
    apply value_locally_closed; exact H0.
  - inversion H; subst.
    eapply open_tm_ty_rec_lc; [eassumption | exact H0].
  - apply lc_tm_app.
    + apply lc_tm_app.
      * eapply value_locally_closed; eauto.
      * exact (lc_numeric_value n H).
    + apply lc_tm_rec; [exact (lc_numeric_value n H) | exact H8 | exact H9].
Qed.

Lemma expression_lifting_down : forall R t u,
  expression_lifting R t -> t --> u -> expression_lifting R u.
Proof.
  intros R t u [Hlc [Hsn Hrel]] Hstep.
  split; [eapply step_preserves_lc; eauto|].
  split; [eapply sn_step; eauto|].
  intros v Hmulti Hv; apply Hrel with (v := v); eauto using multi.
Qed.

Lemma expression_lifting_from_steps : forall R t,
  locally_closed_tm t ->
  (forall u, t --> u -> expression_lifting R u) ->
  (value t -> R t) -> expression_lifting R t.
Proof.
  intros R t Hlc Hsteps Hvalue; split; [exact Hlc|].
  split.
  - constructor; intros u Hstep; destruct (Hsteps u Hstep) as [_ [Hsn _]];
      exact Hsn.
  - intros v Hmulti Hv; inversion Hmulti; subst.
    + apply Hvalue; exact Hv.
    + destruct (Hsteps _ H) as [_ [_ Hrel]].
      apply Hrel with (v := v); assumption.
Qed.

Lemma expression_lifting_of_value : forall R v,
  value v -> R v -> expression_lifting R v.
Proof.
  intros R v Hv HR.
  apply expression_lifting_from_steps.
  - apply value_locally_closed; exact Hv.
  - intros u Hstep; exfalso; eapply value_no_step; eauto.
  - intros _; exact HR.
Qed.

Lemma numeric_value_dec : forall n,
  {numeric_value n} + {~ numeric_value n}.
Proof.
  induction n; try (solve [right; intro H; inversion H]).
  - left; constructor.
  - destruct IHn as [H | H].
    + left; constructor; exact H.
    + right; intro Hv; inversion Hv; subst; contradiction.
Qed.

Lemma value_dec_lc : forall t,
  locally_closed_tm t -> {value t} + {~ value t}.
Proof.
  intros t Hlc; destruct t;
    try (solve [right; intro Hv; inversion Hv; subst;
      match goal with Hn : numeric_value _ |- _ => inversion Hn end]).
  - left; apply v_abs; exact Hlc.
  - left; apply v_tabs; exact Hlc.
  - left; apply v_true.
  - left; apply v_false.
  - left; apply v_nat; constructor.
  - destruct (numeric_value_dec t) as [Hn | Hn].
    + left; apply v_nat; constructor; exact Hn.
    + right; intro Hv; inversion Hv; subst;
        inversion H; subst; contradiction.
Qed.

Lemma expression_lifting_bind : forall R S (f : tm -> tm) t,
  (forall u, locally_closed_tm u -> locally_closed_tm (f u)) ->
  (forall u, value (f u) -> value u) ->
  (forall u w, locally_closed_tm u -> ~ value u -> f u --> w ->
    exists u', u --> u' /\ w = f u') ->
  expression_lifting R t ->
  (forall v, R v -> expression_lifting S (f v)) ->
  expression_lifting S (f t).
Proof.
  intros R S f t Hf_lc Hf_value Hf_step [Hlc [Hsn Hrel]] Hcont.
  revert Hlc Hrel; induction Hsn as [t Hstep IH]; intros Hlc Hrel.
  destruct (value_dec_lc t Hlc) as [Hv | Hnv].
  - apply Hcont. apply Hrel with (v := t); [constructor | exact Hv].
  - apply expression_lifting_from_steps.
    + apply Hf_lc; exact Hlc.
    + intros w Hfw.
      destruct (Hf_step t w Hlc Hnv Hfw) as [u [Htu ->]].
      apply IH with (u := u).
      * exact Htu.
      * eapply step_preserves_lc; eauto.
      * intros v Hmulti Hv; apply Hrel with (v := v);
          [eapply multi_step; eauto | exact Hv].
    + intro Hfv; exfalso; apply Hnv; apply Hf_value; exact Hfv.
Qed.

Lemma expression_lifting_single_step : forall R t u,
  locally_closed_tm t ->
  (forall w, t --> w -> w = u) ->
  ~ value t -> expression_lifting R u -> expression_lifting R t.
Proof.
  intros R t u Hlc Hunique Hnv Hu.
  apply expression_lifting_from_steps.
  - exact Hlc.
  - intros w Hstep; rewrite (Hunique w Hstep); exact Hu.
  - intro Hv; contradiction.
Qed.

Lemma expression_lifting_app_beta : forall R U body arg,
  value (tm_abs U body) -> value arg ->
  expression_lifting R (open_tm body arg) ->
  expression_lifting R (tm_app (tm_abs U body) arg).
Proof.
  intros R U body arg Habs Harg Hbody.
  apply expression_lifting_single_step with (u := open_tm body arg).
  - apply lc_tm_app; apply value_locally_closed; assumption.
  - intros w Hstep; inversion Hstep; subst; try reflexivity.
    + exfalso; eapply (value_no_step (tm_abs U body) t1'); eauto.
    + exfalso; exact (value_no_step arg t2' Harg H3).
  - intro Hv; inversion Hv; subst; inversion H.
  - exact Hbody.
Qed.

Lemma expression_lifting_tapp_beta : forall R body U,
  value (tm_tabs body) -> locally_closed_ty U ->
  expression_lifting R (open_tm_ty body U) ->
  expression_lifting R (tm_tapp (tm_tabs body) U).
Proof.
  intros R body U Htabs HU Hbody.
  apply expression_lifting_single_step with (u := open_tm_ty body U).
  - apply lc_tm_tapp; [apply value_locally_closed; exact Htabs | exact HU].
  - intros w Hstep; inversion Hstep; subst; try reflexivity.
    exfalso; eapply value_no_step; eauto.
  - intro Hv; inversion Hv; subst; inversion H.
  - exact Hbody.
Qed.

Lemma expression_lifting_if_true : forall R t1 t2,
  expression_lifting R t1 -> locally_closed_tm t2 ->
  expression_lifting R (tm_if tm_true t1 t2).
Proof.
  intros R t1 t2 H1 H2.
  apply expression_lifting_single_step with (u := t1).
  - apply lc_tm_if; [apply lc_tm_true | exact (proj1 H1) | exact H2].
  - intros w Hstep; inversion Hstep; subst; try reflexivity.
    exfalso; exact (value_no_step tm_true t1' v_true H4).
  - intro Hv; inversion Hv; subst; inversion H.
  - exact H1.
Qed.

Lemma expression_lifting_if_false : forall R t1 t2,
  locally_closed_tm t1 -> expression_lifting R t2 ->
  expression_lifting R (tm_if tm_false t1 t2).
Proof.
  intros R t1 t2 H1 H2.
  apply expression_lifting_single_step with (u := t2).
  - apply lc_tm_if; [apply lc_tm_false | exact H1 | exact (proj1 H2)].
  - intros w Hstep; inversion Hstep; subst; try reflexivity.
    exfalso; exact (value_no_step tm_false t1' v_false H4).
  - intro Hv; inversion Hv; subst; inversion H.
  - exact H2.
Qed.

Lemma expression_relation_app : forall eta rho A B t1 t2,
  expression_relation eta rho (Ty_Arrow A B) t1 ->
  expression_relation eta rho A t2 ->
  expression_relation eta rho B (tm_app t1 t2).
Proof.
  intros eta rho A B t1 t2 H1 H2.
  pose proof (proj1 H2) as Hlc2.
  unfold expression_relation in *.
  eapply expression_lifting_bind with
    (f := fun u => tm_app u t2) (R := value_relation eta rho (Ty_Arrow A B)).
  - intros u Hu; apply lc_tm_app; assumption.
  - intros u Hv; inversion Hv; subst; inversion H.
  - intros u w Hu Hnv Hstep; inversion Hstep; subst.
    + exfalso; apply Hnv; apply v_abs; assumption.
    + eexists; split; eauto.
    + exfalso; apply Hnv; assumption.
  - exact H1.
  - intros v1 Hrel1.
    destruct Hrel1 as [Hv1 [U [body [Heq Hfun]]]].
    subst v1.
    eapply expression_lifting_bind with
      (f := fun u => tm_app (tm_abs U body) u)
      (R := value_relation eta rho A).
    + intros u Hu; apply lc_tm_app;
        [apply value_locally_closed; exact Hv1 | exact Hu].
    + intros u Hv; inversion Hv; subst; inversion H.
    + intros u w Hu Hnv Hstep; inversion Hstep; subst.
      * exfalso; apply Hnv; assumption.
      * exfalso; eapply value_no_step; [exact Hv1 | eassumption].
      * eexists; split; eauto.
    + exact H2.
    + intros v2 Hrel2.
      apply expression_lifting_app_beta.
      * exact Hv1.
      * eapply value_relation_value; exact Hrel2.
      * apply Hfun; exact Hrel2.
Qed.

Definition semantic_candidate (rho : relation_env) (T : ty) : value_candidate.
Proof.
  refine {| candidate_relation := value_relation [] rho T |}.
  intros v Hv; eapply value_relation_value; exact Hv.
Defined.

Lemma expression_relation_tapp : forall rho T t Usem Ucon,
  expression_relation [] rho (Ty_All T) t ->
  locally_closed_ty Usem -> locally_closed_ty Ucon ->
  expression_relation [] rho (open_ty T Usem) (tm_tapp t Ucon).
Proof.
  intros rho T t Usem Ucon Ht HUsem HUcon.
  unfold expression_relation in *.
  eapply expression_lifting_bind with
    (f := fun v => tm_tapp v Ucon) (R := value_relation [] rho (Ty_All T)).
  - intros v Hv; apply lc_tm_tapp; assumption.
  - intros v Hv; inversion Hv; subst; inversion H.
  - intros v w Hlc Hnv Hstep; inversion Hstep; subst.
    + exfalso; apply Hnv; apply v_tabs; assumption.
    + eexists; split; eauto.
  - exact Ht.
  - intros v Hrel.
    destruct Hrel as [Hv [body [Heq Hbody]]].
    subst v.
    apply expression_lifting_tapp_beta; [exact Hv | exact HUcon |].
    pose (a := semantic_candidate rho Usem).
    specialize (Hbody Ucon a HUcon).
    assert (Heq : forall w,
      value_relation [] rho (open_ty T Usem) w <-> value_relation [a] rho T w).
    { intros w; unfold open_ty.
      apply (value_relation_open_ty T 0 [] rho Usem a w eq_refl HUsem).
      intros z; reflexivity. }
    exact (proj2 (expression_lifting_iff _ _ _ Heq) Hbody).
Qed.

Lemma related_substitution_term_update : forall rho Gamma gamma x T v,
  related_substitution rho Gamma gamma ->
  value_relation [] rho T v ->
  related_substitution rho (update Gamma x T) (term_update gamma x v).
Proof.
  intros rho Gamma gamma x T v Hgamma Hv y U Hlookup.
  unfold update in Hlookup; simpl in Hlookup.
  unfold term_update; destruct (Nat.eqb x y) eqn:E.
  - rewrite (Nat.eqb_sym y x), E in Hlookup.
    inversion Hlookup; subst; exact Hv.
  - rewrite (Nat.eqb_sym y x), E in Hlookup.
    apply Hgamma; exact Hlookup.
Qed.

Lemma expression_relation_if : forall eta rho T c t1 t2,
  expression_relation eta rho Ty_Bool c ->
  expression_relation eta rho T t1 ->
  expression_relation eta rho T t2 ->
  expression_relation eta rho T (tm_if c t1 t2).
Proof.
  intros eta rho T c t1 t2 Hc H1 H2.
  unfold expression_relation in *.
  eapply expression_lifting_bind with
    (f := fun u => tm_if u t1 t2) (R := value_relation eta rho Ty_Bool).
  - intros u Hu; apply lc_tm_if; [exact Hu | exact (proj1 H1) | exact (proj1 H2)].
  - intros u Hv; inversion Hv; subst; inversion H.
  - intros u w Hu Hnv Hstep; inversion Hstep; subst.
    + exfalso; apply Hnv; apply v_true.
    + exfalso; apply Hnv; apply v_false.
    + eexists; split; eauto.
  - exact Hc.
  - intros v [Hv [Heq | Heq]]; subst v.
    + apply expression_lifting_if_true; [exact H1 | exact (proj1 H2)].
    + apply expression_lifting_if_false; [exact (proj1 H1) | exact H2].
Qed.

Lemma expression_relation_choice : forall eta rho T t1 t2,
  expression_relation eta rho T t1 ->
  expression_relation eta rho T t2 ->
  expression_relation eta rho T (tm_choice t1 t2).
Proof.
  intros eta rho T t1 t2 H1 H2; unfold expression_relation in *.
  apply expression_lifting_from_steps.
  - apply lc_tm_choice; [exact (proj1 H1) | exact (proj1 H2)].
  - intros u Hstep; inversion Hstep; subst; assumption.
  - intro Hv; inversion Hv; subst; inversion H.
Qed.

Lemma expression_relation_succ : forall eta rho n,
  expression_relation eta rho Ty_Nat n ->
  expression_relation eta rho Ty_Nat (tm_succ n).
Proof.
  intros eta rho n Hn; unfold expression_relation in *.
  eapply expression_lifting_bind with
    (f := tm_succ) (R := value_relation eta rho Ty_Nat).
  - intros u Hu; apply lc_tm_succ; exact Hu.
  - intros u Hv; inversion Hv; subst; inversion H; subst.
    apply v_nat; assumption.
  - intros u w Hu Hnv Hstep; inversion Hstep; subst;
      eexists; split; eauto.
  - exact Hn.
  - intros v [Hv Hnumeric].
    apply expression_lifting_of_value.
    + apply v_nat; apply nv_succ; exact Hnumeric.
    + simpl; split.
      * apply v_nat; apply nv_succ; exact Hnumeric.
      * apply nv_succ; exact Hnumeric.
Qed.

Lemma expression_relation_rec_values : forall eta rho T n b s,
  numeric_value n ->
  value_relation eta rho T b ->
  value_relation eta rho (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  expression_relation eta rho T (tm_natrec n b s).
Proof.
  intros eta rho T n b s Hnum Hb Hs.
  induction Hnum.
  - unfold expression_relation.
    apply expression_lifting_single_step with (u := b).
    + apply lc_tm_rec.
      * apply lc_tm_zero.
      * eapply value_relation_lc; exact Hb.
      * eapply value_relation_lc; exact Hs.
    + intros w Hstep; inversion Hstep; subst; try reflexivity.
      all: exfalso; first
        [ eapply (numeric_value_no_step tm_zero);
            [constructor | eassumption]
        | eapply (value_no_step b);
            [eapply value_relation_value; exact Hb | eassumption]
        | eapply (value_no_step s);
            [eapply value_relation_value; exact Hs | eassumption] ].
    + intro Hv; inversion Hv; subst; inversion H.
    + apply expression_lifting_of_value.
      * eapply value_relation_value; exact Hb.
      * exact Hb.
  - unfold expression_relation.
    apply expression_lifting_single_step with
      (u := tm_app (tm_app s n) (tm_natrec n b s)).
    + apply lc_tm_rec.
      * exact (lc_numeric_value _ (nv_succ n Hnum)).
      * eapply value_relation_lc; exact Hb.
      * eapply value_relation_lc; exact Hs.
    + intros w Hstep; inversion Hstep; subst; try reflexivity.
      all: exfalso; first
        [ eapply (numeric_value_no_step (tm_succ n));
            [constructor; exact Hnum | eassumption]
        | eapply (value_no_step b);
            [eapply value_relation_value; exact Hb | eassumption]
        | eapply (value_no_step s);
            [eapply value_relation_value; exact Hs | eassumption] ].
    + intro Hv; inversion Hv; subst; inversion H.
    + eapply expression_relation_app.
      * eapply expression_relation_app.
        -- apply expression_lifting_of_value.
           ++ eapply value_relation_value; exact Hs.
           ++ exact Hs.
        -- apply expression_lifting_of_value.
           ++ apply v_nat; exact Hnum.
           ++ simpl; split; [apply v_nat; exact Hnum | exact Hnum].
      * exact IHHnum.
Qed.

Lemma expression_relation_rec : forall eta rho T n b s,
  expression_relation eta rho Ty_Nat n ->
  expression_relation eta rho T b ->
  expression_relation eta rho (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  expression_relation eta rho T (tm_natrec n b s).
Proof.
  intros eta rho T n b s Hn Hb Hs.
  unfold expression_relation in *.
  eapply expression_lifting_bind with
    (f := fun u => tm_natrec u b s) (R := value_relation eta rho Ty_Nat).
  - intros u Hu; apply lc_tm_rec;
      [exact Hu | exact (proj1 Hb) | exact (proj1 Hs)].
  - intros u Hv; inversion Hv; subst; inversion H.
  - intros u w Hu Hnv Hstep; inversion Hstep; subst;
      try solve [exfalso; apply Hnv; eauto using value, numeric_value].
    eexists; split; eauto.
  - exact Hn.
  - intros nv [Hvn Hnum].
    eapply expression_lifting_bind with
      (f := fun u => tm_natrec nv u s) (R := value_relation eta rho T).
    + intros u Hu; apply lc_tm_rec;
        [exact (lc_numeric_value nv Hnum) | exact Hu | exact (proj1 Hs)].
    + intros u Hv; inversion Hv; subst; inversion H.
    + intros u w Hu Hnv_b Hstep; inversion Hstep; subst;
        try solve [exfalso; apply Hnv_b; eauto using value];
        try solve [exfalso; eapply value_no_step; [exact Hvn | eassumption]].
      eexists; split; eauto.
    + exact Hb.
    + intros bv Hbv.
      pose proof (value_relation_value T eta rho bv Hbv) as Hvb.
      eapply expression_lifting_bind with
        (f := fun u => tm_natrec nv bv u)
        (R := value_relation eta rho (Ty_Arrow Ty_Nat (Ty_Arrow T T))).
      * intros u Hu; apply lc_tm_rec;
          [exact (lc_numeric_value nv Hnum) |
           apply value_locally_closed; exact Hvb | exact Hu].
      * intros u Hv; inversion Hv; subst; inversion H.
      * intros u w Hu Hnv_s Hstep; inversion Hstep; subst;
          try solve [exfalso; apply Hnv_s; eauto using value];
          try solve [exfalso; eapply value_no_step; [exact Hvn | eassumption]];
          try solve [exfalso; eapply value_no_step; [exact Hvb | eassumption]].
        eexists; split; eauto.
      * exact Hs.
      * intros sv Hsv; apply expression_relation_rec_values; assumption.
Qed.

Theorem fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall theta gamma rho,
    type_substitution_closed theta ->
    term_substitution_closed gamma ->
    related_substitution rho Gamma gamma ->
    expression_relation [] rho T (instantiate theta gamma t).
Proof.
  intros Delta Gamma t T Hty; induction Hty;
    intros theta gamma rho Htheta Hgamma Hrelated; simpl.
  - unfold expression_relation.
    pose proof (Hrelated x T H) as Hrel.
    apply expression_lifting_of_value.
    + eapply value_relation_value; exact Hrel.
    + exact Hrel.
  - assert (Htyped : has_type Delta Gamma (tm_abs T1 t2) (Ty_Arrow T1 T2)).
    { eapply T_Abs with (L := L); eauto. }
    pose proof (typing_locally_closed _ _ _ _ Htyped) as Hlc.
    pose proof (instantiate_lc theta gamma _ Htheta Hgamma Hlc) as Hinstlc.
    assert (Hval : value (tm_abs (instantiate_ty theta T1)
      (instantiate theta gamma t2))) by (apply v_abs; exact Hinstlc).
    unfold expression_relation.
    apply expression_lifting_of_value; [exact Hval|].
    simpl; split; [exact Hval|].
    exists (instantiate_ty theta T1), (instantiate theta gamma t2).
    split; [reflexivity|]; intros arg Harg.
    pose (x := fresh_atom (L ++ tm_fvars t2)).
    assert (Hfresh : ~ In x L /\ ~ In x (tm_fvars t2)).
    { unfold x; apply not_in_app; apply fresh_atom_not_in. }
    destruct Hfresh as [HfreshL Hfresht].
    pose (gamma' := term_update gamma x arg).
    assert (Hgamma' : term_substitution_closed gamma').
    { unfold gamma'; apply term_update_closed; [exact Hgamma|].
      eapply value_relation_lc; exact Harg. }
    assert (Hrelated' : related_substitution rho (update Gamma x T1) gamma').
    { unfold gamma'; apply related_substitution_term_update;
        [exact Hrelated | exact Harg]. }
    pose proof (H1 x HfreshL theta gamma' rho
      Htheta Hgamma' Hrelated') as Hbody.
    unfold open_tm in Hbody.
    rewrite (instantiate_open_tm_rec t2 0 x theta gamma' Hgamma') in Hbody.
    unfold gamma' in Hbody.
    replace (term_update gamma x arg x) with arg in Hbody
      by (unfold term_update; rewrite Nat.eqb_refl; reflexivity).
    rewrite (instantiate_term_update_irrel t2 theta gamma x arg Hfresht) in Hbody.
    exact Hbody.
  - eapply expression_relation_app; eauto.
  - assert (Htyped : has_type Delta Gamma (tm_tabs t) (Ty_All T)).
    { eapply T_TAbs with (L := L); eauto. }
    pose proof (typing_locally_closed _ _ _ _ Htyped) as Hlc.
    pose proof (instantiate_lc theta gamma _ Htheta Hgamma Hlc) as Hinstlc.
    assert (Hval : value (tm_tabs (instantiate theta gamma t)))
      by (apply v_tabs; exact Hinstlc).
    unfold expression_relation.
    apply expression_lifting_of_value; [exact Hval|].
    simpl; split; [exact Hval|].
    exists (instantiate theta gamma t); split; [reflexivity|].
    intros U cand HU.
    pose (X := fresh_atom
      (L ++ tm_ty_fvars t ++ ty_fvars T ++ context_ty_fvars Gamma)).
    assert (Hfresh : ~ In X L /\ ~ In X (tm_ty_fvars t) /\
      ~ In X (ty_fvars T) /\ ~ In X (context_ty_fvars Gamma)).
    { unfold X; pose proof (fresh_atom_not_in
        (L ++ tm_ty_fvars t ++ ty_fvars T ++ context_ty_fvars Gamma)) as Hf.
      repeat rewrite in_app_iff in Hf; tauto. }
    destruct Hfresh as [HfreshL [Hfresht [HfreshT HfreshGamma]]].
    pose (theta' := type_update theta X U).
    pose (rho' := relation_update rho X cand).
    assert (Htheta' : type_substitution_closed theta').
    { unfold theta'; apply type_update_closed; assumption. }
    assert (Hrelated' : related_substitution rho' Gamma gamma).
    { unfold rho'; apply related_substitution_rho_update; assumption. }
    pose proof (H0 X HfreshL theta' gamma rho'
      Htheta' Hgamma Hrelated') as Hbody.
    unfold expression_relation, open_tm_ty in Hbody.
    unfold theta' in Hbody.
    rewrite (instantiate_open_tm_ty_update t 0 X U theta gamma
      Htheta Hgamma Hfresht) in Hbody.
    assert (Heq : forall v,
      value_relation [] rho' (open_ty T (Ty_FVar X)) v <->
      value_relation [cand] rho T v).
    { intros v; unfold rho', open_ty.
      apply (value_relation_open_fvar T 0 [] rho X cand v eq_refl HfreshT). }
    exact (proj1 (expression_lifting_iff _ _ _ Heq) Hbody).
  - eapply expression_relation_tapp.
    + apply IHHty; assumption.
    + exact (wf_ty_locally_closed Delta U H).
    + apply instantiate_ty_lc_at; [exact (wf_ty_locally_closed Delta U H) | exact Htheta].
  - unfold expression_relation; apply expression_lifting_of_value.
    + apply v_true.
    + simpl; split; [apply v_true | left; reflexivity].
  - unfold expression_relation; apply expression_lifting_of_value.
    + apply v_false.
    + simpl; split; [apply v_false | right; reflexivity].
  - eapply expression_relation_if; eauto.
  - unfold expression_relation; apply expression_lifting_of_value.
    + apply v_nat; apply nv_zero.
    + simpl; split; [apply v_nat; apply nv_zero | apply nv_zero].
  - eapply expression_relation_succ; eauto.
  - eapply expression_relation_rec; eauto.
  - eapply expression_relation_choice; eauto.
Qed.

Lemma instantiate_ty_identity : forall T,
  instantiate_ty (fun X => Ty_FVar X) T = T.
Proof.
  induction T; simpl; congruence.
Qed.

Lemma instantiate_identity : forall t,
  instantiate (fun X => Ty_FVar X) (fun x => tm_fvar x) t = t.
Proof.
  induction t; simpl; try rewrite instantiate_ty_identity;
    try rewrite IHt; try rewrite IHt1; try rewrite IHt2;
    try rewrite IHt3; reflexivity.
Qed.

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  intros t T Hty.
  pose proof (fundamental [] empty t T Hty
    (fun X => Ty_FVar X) (fun x => tm_fvar x)
    (fun _ => None)) as Hfund.
  assert (Htheta : type_substitution_closed (fun X => Ty_FVar X)).
  { intro X; unfold locally_closed_ty; apply lc_ty_fvar. }
  assert (Hgamma : term_substitution_closed (fun x => tm_fvar x)).
  { intro x; unfold locally_closed_tm; apply lc_tm_fvar. }
  assert (Hrelated : related_substitution (fun _ => None) empty
    (fun x => tm_fvar x)).
  { intros x U Hlookup; discriminate Hlookup. }
  specialize (Hfund Htheta Hgamma Hrelated).
  rewrite instantiate_identity in Hfund.
  destruct Hfund as [_ [Hsn _]]; exact Hsn.
Qed.

End SystemFNormalizationIfNondeterminismRecursionMediumTask.
