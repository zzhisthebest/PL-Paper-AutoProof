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

(** Some elementary finite-support infrastructure.  The definitions below are
    deliberately kept separate from the typing relation: they are only used
    to choose names for the locally-nameless binders. *)
Fixpoint tm_fvars (t : tm) : list atom :=
  match t with
  | tm_bvar _ => [] | tm_fvar x => [x]
  | tm_abs _ t1 => tm_fvars t1
  | tm_app t1 t2 => tm_fvars t1 ++ tm_fvars t2
  | tm_tabs t1 => tm_fvars t1
  | tm_tapp t1 _ => tm_fvars t1
  | tm_true | tm_false | tm_zero => []
  | tm_if t1 t2 t3 => tm_fvars t1 ++ tm_fvars t2 ++ tm_fvars t3
  | tm_succ t1 => tm_fvars t1
  | tm_natrec n b s => tm_fvars n ++ tm_fvars b ++ tm_fvars s
  | tm_choice t1 t2 => tm_fvars t1 ++ tm_fvars t2
  end.

Fixpoint ty_fvars (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => [] | Ty_FVar X => [X]
  | Ty_Arrow T1 T2 => ty_fvars T1 ++ ty_fvars T2
  | Ty_All T1 => ty_fvars T1
  | Ty_Bool | Ty_Nat => []
  end.

Fixpoint context_fvars (Gamma : context) : list atom :=
  match Gamma with
  | [] => [] | (x, _) :: Gamma' => x :: context_fvars Gamma'
  end.

Definition fresh_of (l : list atom) : atom :=
  S (fold_right Nat.max 0 l).

Lemma le_fold_max : forall l x, In x l -> x <= fold_right Nat.max 0 l.
Proof.
  induction l as [|a l IH]; intros x H; simpl in *.
  - contradiction.
  - destruct H as [<-|H].
    + lia.
    + specialize (IH x H). lia.
Qed.

Lemma fresh_of_not_in : forall l, ~ In (fresh_of l) l.
Proof.
  intros l H.
  cbv [fresh_of] in H.
  pose proof (le_fold_max l (S (fold_right Nat.max 0 l)) H).
  lia.
Qed.

Definition id_type_substitution : type_substitution := fun X => Ty_FVar X.
Definition subst_tm (gamma : term_substitution) (t : tm) : tm :=
  instantiate id_type_substitution gamma t.

Lemma lc_ty_weaken : forall K T, lc_ty_at K T -> lc_ty_at (S K) T.
Proof.
  intros K T H; induction H; eauto using lc_ty_at; try lia.
Qed.

Lemma lc_ty_weaken_n : forall K n T, lc_ty_at K T -> lc_ty_at (K+n) T.
Proof.
  intros K n T H; induction n as [|n IH].
  - rewrite Nat.add_0_r; assumption.
  - simpl. replace (K + S n) with (S (K+n)) by lia.
    apply lc_ty_weaken; assumption.
Qed.

Lemma lc_ty_open : forall K U T,
  locally_closed_ty U -> lc_ty_at (S K) T ->
  lc_ty_at K (open_ty_rec K U T).
Proof.
  intros K U T Hu HT.
  revert K U Hu HT.
  induction T as [i|X|T1 IH1 T2 IH2|T IH| | ];
    intros K U Hu H; simpl in *.
  - inversion H; subst. destruct (Nat.eqb K i) eqn:E.
    + apply Nat.eqb_eq in E; subst. unfold locally_closed_ty in Hu.
      replace i with (0+i) by lia. apply lc_ty_weaken_n; exact Hu.
    + apply lc_ty_bvar. apply Nat.eqb_neq in E. lia.
  - constructor.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst. constructor. all: eauto using lc_ty_weaken.
  - constructor.
  - constructor.
Qed.

Lemma lc_tm_weaken_one : forall K k t,
  lc_tm_at K k t -> lc_tm_at K (S k) t.
Proof.
  intros K k t H; induction H; eauto using lc_tm_at; try lia.
Qed.

Lemma lc_tm_weaken_K_one : forall K k t,
  lc_tm_at K k t -> lc_tm_at (S K) k t.
Proof.
  intros K k t H; induction H; eauto using lc_tm_at, lc_ty_weaken; try lia.
Qed.

Lemma lc_tm_weaken_K : forall K k n t,
  lc_tm_at K k t -> lc_tm_at (K+n) k t.
Proof.
  intros K k n t H; induction n as [|n IH].
  - rewrite Nat.add_0_r; assumption.
  - replace (K + S n) with (S (K+n)) by lia.
    apply lc_tm_weaken_K_one; assumption.
Qed.

Lemma lc_tm_weaken_k : forall K k n t,
  lc_tm_at K k t -> lc_tm_at K (k+n) t.
Proof.
  intros K k n t H; induction n as [|n IH].
  - rewrite Nat.add_0_r; assumption.
  - replace (k + S n) with (S (k+n)) by lia.
    apply lc_tm_weaken_one; assumption.
Qed.

Lemma lc_tm_open : forall K k u t,
  lc_tm_at K k u -> lc_tm_at K (S k) t ->
  lc_tm_at K k (open_tm_rec k u t).
Proof.
  intros K k u t Hu HT.
  revert K k u Hu HT.
  induction t as [i|x|T t IH|t1 IH1 t2 IH2|t IH|t IH| | |t1 IH1 t2 IH2 t3 IH3| |t IH|n IHn b IHb s IHs|t1 IH1 t2 IH2];
    intros K k u Hu H; simpl in *.
  - inversion H; subst. destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E; subst; assumption.
    + apply lc_tm_bvar. apply Nat.eqb_neq in E. lia.
  - constructor.
  - inversion H; subst. constructor.
    + assumption.
    + eapply IH with (K:=K) (k:=S k) (u:=u). replace (S k) with (k+1) by lia.
      apply lc_tm_weaken_k with (n:=1). exact Hu. assumption.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst. constructor.
    apply IH. replace (S K) with (K+1) by lia.
    apply lc_tm_weaken_K with (n:=1). exact Hu. assumption.
  - inversion H; subst; constructor; eauto.
  - constructor.
  - constructor.
  - inversion H; subst; constructor; eauto.
  - constructor.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
Qed.

Lemma lc_ty_open_inv : forall K U T,
  lc_ty_at K U -> lc_ty_at K (open_ty_rec K U T) -> lc_ty_at (S K) T.
Proof.
  intros K U T HU.
  revert K U HU.
  induction T as [i|X|T1 IH1 T2 IH2|T IH| | ];
    intros K U HU H; simpl in *.
  - destruct i as [|i].
    + apply lc_ty_bvar; lia.
    + destruct (Nat.eqb K (S i)) eqn:E.
      * apply Nat.eqb_eq in E; apply lc_ty_bvar; lia.
      * apply Nat.eqb_neq in E. simpl in H. inversion H; apply lc_ty_bvar; lia.
  - constructor.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst. apply lc_ty_all.
    apply (IH (S K) U).
    + apply lc_ty_weaken; assumption.
    + assumption.
  - constructor.
  - constructor.
Qed.

Lemma lc_ty_open_inv0 : forall U T,
  lc_ty_at 0 U -> lc_ty_at 0 (open_ty T U) -> lc_ty_at 1 T.
Proof.
  intros U T HU H. apply lc_ty_open_inv with (K:=0) (U:=U) (T:=T); assumption.
Qed.

Lemma lc_tm_open_inv : forall K k u t,
  lc_tm_at K k u -> lc_tm_at K k (open_tm_rec k u t) ->
  lc_tm_at K (S k) t.
Proof.
  intros K k u t Hu.
  revert K k u Hu.
  induction t as [i|x|T t IH|t1 IH1 t2 IH2|t IH|t IH| | |t1 IH1 t2 IH2 t3 IH3| |t IH|n IHn b IHb s IHs|t1 IH1 t2 IH2];
    intros K k u Hu H; simpl in *.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E; subst. apply lc_tm_bvar; lia.
    + apply Nat.eqb_neq in E. inversion H; apply lc_tm_bvar; lia.
  - constructor.
  - inversion H; subst. constructor.
    + assumption.
    + eapply IH with (K:=K) (k:=S k) (u:=u). replace (S k) with (k+1) by lia.
      apply lc_tm_weaken_k with (n:=1); exact Hu.
      assumption.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst. constructor.
    eapply IH with (K:=S K) (k:=k) (u:=u).
    + replace (S K) with (K+1) by lia. apply lc_tm_weaken_K with (n:=1); exact Hu.
    + assumption.
  - inversion H; subst. constructor.
    + eapply IH with (K:=K) (k:=k) (u:=u); assumption.
    + assumption.
  - constructor.
  - constructor.
  - inversion H; subst; constructor; eauto.
  - constructor.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
Qed.

Lemma open_tm_lc_rec : forall K k u t,
  lc_tm_at K k t -> open_tm_rec k u t = t.
Proof.
  intros K k u t H; revert K k u H.
  induction t as [i|x|T t IH|t1 IH1 t2 IH2|t IH|t IH| | |t1 IH1 t2 IH2 t3 IH3| |t IH|n IHn b IHb s IHs|t1 IH1 t2 IH2];
    intros K k u H; simpl in *.
  - inversion H; subst. destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E; lia.
    + reflexivity.
  - reflexivity.
  - inversion H; subst. f_equal. eapply IH with (K:=K) (k:=S k) (u:=u); eauto.
  - inversion H; subst. f_equal; [eapply IH1 with (K:=K) (k:=k) (u:=u) | eapply IH2 with (K:=K) (k:=k) (u:=u)]; eauto.
  - inversion H; subst. f_equal. eapply IH with (K:=S K) (k:=k) (u:=u); eauto.
  - inversion H; subst. f_equal. eapply IH with (K:=K) (k:=k) (u:=u); eauto.
  - reflexivity.
  - reflexivity.
  - inversion H; subst. f_equal; [eapply IH1 with (K:=K) (k:=k) (u:=u) | eapply IH2 with (K:=K) (k:=k) (u:=u) | eapply IH3 with (K:=K) (k:=k) (u:=u)]; eauto.
  - reflexivity.
  - inversion H; subst. f_equal. eapply IH with (K:=K) (k:=k) (u:=u); eauto.
  - inversion H; subst. f_equal; [eapply IHn with (K:=K) (k:=k) (u:=u) | eapply IHb with (K:=K) (k:=k) (u:=u) | eapply IHs with (K:=K) (k:=k) (u:=u)]; eauto.
  - inversion H; subst. f_equal; [eapply IH1 with (K:=K) (k:=k) (u:=u) | eapply IH2 with (K:=K) (k:=k) (u:=u)]; eauto.
Qed.

Lemma not_in_app_l : forall (A : Type) (x : A) l r,
  ~ In x (l ++ r) -> ~ In x l.
Proof.
  intros A x l r H Hin. apply H. apply (proj2 (in_app_iff l r x)); left; exact Hin.
Qed.

Lemma not_in_app_r : forall (A : Type) (x : A) l r,
  ~ In x (l ++ r) -> ~ In x r.
Proof.
  intros A x l r H Hin. apply H. apply (proj2 (in_app_iff l r x)); right; exact Hin.
Qed.

Lemma subst_open : forall gamma x s t k,
  (forall y, locally_closed_tm (gamma y)) ->
  ~ In x (tm_fvars t) ->
  subst_tm (fun y => if Nat.eqb x y then s else gamma y)
    (open_tm_rec k (tm_fvar x) t) = open_tm_rec k s (subst_tm gamma t).
Proof.
  intros gamma x s t k Hgamma.
  unfold subst_tm, instantiate, id_type_substitution.
  revert gamma x s k Hgamma.
  induction t as [i|y|T t IH|t1 IH1 t2 IH2|t IH|t IH| | |t1 IH1 t2 IH2 t3 IH3| |t IH|n IHn b IHb q IHq|t1 IH1 t2 IH2];
    intros gamma x s k Hgamma H; simpl in *.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E; subst. destruct i; simpl; try rewrite (Nat.eqb_refl x); reflexivity.
    + reflexivity.
  - destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst y. exfalso. apply H. simpl. left; reflexivity.
    + symmetry. apply (open_tm_lc_rec 0 k s (gamma y)).
      apply (lc_tm_weaken_k 0 0 k (gamma y)). unfold locally_closed_tm in Hgamma. apply Hgamma.
  - f_equal. eapply IH with (gamma:=gamma) (x:=x) (s:=s) (k:=S k); eauto.
  - f_equal.
    + eapply IH1 with (gamma:=gamma) (x:=x) (s:=s) (k:=k).
      * exact Hgamma.
      * intro Hin; apply H; apply in_or_app; left; exact Hin.
    + eapply IH2 with (gamma:=gamma) (x:=x) (s:=s) (k:=k).
      * exact Hgamma.
      * intro Hin; apply H; apply in_or_app; right; exact Hin.
  - f_equal. eapply IH with (gamma:=gamma) (x:=x) (s:=s) (k:=k).
    + exact Hgamma.
    + exact H.
  - f_equal. eapply IH with (gamma:=gamma) (x:=x) (s:=s) (k:=k); eauto.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + eapply IH1 with (gamma:=gamma) (x:=x) (s:=s) (k:=k).
      * exact Hgamma.
      * intro Hin; apply H. apply (proj2 (in_app_iff (tm_fvars t1) (tm_fvars t2 ++ tm_fvars t3) x)); left; exact Hin.
    + eapply IH2 with (gamma:=gamma) (x:=x) (s:=s) (k:=k).
      * exact Hgamma.
      * intro Hin; apply H. apply (proj2 (in_app_iff (tm_fvars t1) (tm_fvars t2 ++ tm_fvars t3) x)); right. apply (proj2 (in_app_iff (tm_fvars t2) (tm_fvars t3) x)); left; exact Hin.
    + eapply IH3 with (gamma:=gamma) (x:=x) (s:=s) (k:=k).
      * exact Hgamma.
      * intro Hin; apply H. apply (proj2 (in_app_iff (tm_fvars t1) (tm_fvars t2 ++ tm_fvars t3) x)); right. apply (proj2 (in_app_iff (tm_fvars t2) (tm_fvars t3) x)); right; exact Hin.
  - reflexivity.
  - f_equal. eapply IH with (gamma:=gamma) (x:=x) (s:=s) (k:=k); eauto.
  - f_equal.
    + eapply IHn with (gamma:=gamma) (x:=x) (s:=s) (k:=k); eauto using not_in_app_l.
    + eapply IHb with (gamma:=gamma) (x:=x) (s:=s) (k:=k).
      * exact Hgamma.
      * apply not_in_app_l with (l:=tm_fvars b) (r:=tm_fvars q).
        apply not_in_app_r with (l:=tm_fvars n) (r:=tm_fvars b ++ tm_fvars q); exact H.
    + eapply IHq with (gamma:=gamma) (x:=x) (s:=s) (k:=k).
      * exact Hgamma.
      * apply (not_in_app_r atom x (tm_fvars b) (tm_fvars q)).
        apply (not_in_app_r atom x (tm_fvars n) (tm_fvars b ++ tm_fvars q)); exact H.
  - f_equal.
    + eapply IH1 with (gamma:=gamma) (x:=x) (s:=s) (k:=k); eauto using not_in_app_l.
    + eapply IH2 with (gamma:=gamma) (x:=x) (s:=s) (k:=k); eauto using not_in_app_r.
Qed.

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  (* Fundamental reducibility and the associated compatibility lemmas are
     still required here. *)
Qed.

End SystemFNormalizationIfNondeterminismRecursionMediumTask.
