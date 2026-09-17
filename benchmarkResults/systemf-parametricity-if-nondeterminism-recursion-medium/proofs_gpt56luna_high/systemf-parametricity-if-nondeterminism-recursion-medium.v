(** System F parametricity benchmark, Medium variant.
    Features: if-nondeterminism-recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFParametricityIfNondeterminismRecursionMediumTask.

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

Inductive evaluates : tm -> tm -> Prop :=
  | EvalValue : forall v, value v -> evaluates v v
  | EvalApp : forall f arg U body v result,
      evaluates f (tm_abs U body) -> evaluates arg v ->
      evaluates (open_tm body v) result -> evaluates (tm_app f arg) result
  | EvalTApp : forall f U body result,
      evaluates f (tm_tabs body) -> locally_closed_ty U ->
      evaluates (open_tm_ty body U) result -> evaluates (tm_tapp f U) result
  | EvalIfTrue : forall c t u v,
      evaluates c tm_true -> evaluates t v -> locally_closed_tm u ->
      evaluates (tm_if c t u) v
  | EvalIfFalse : forall c t u v,
      evaluates c tm_false -> locally_closed_tm t -> evaluates u v ->
      evaluates (tm_if c t u) v
  | EvalSucc : forall t n,
      evaluates t n -> numeric_value n -> evaluates (tm_succ t) (tm_succ n)
  | EvalRecZero : forall n b s vb vs,
      evaluates n tm_zero -> evaluates b vb -> evaluates s vs ->
      evaluates (tm_natrec n b s) vb
  | EvalRecSucc : forall n b s k vb vs result,
      evaluates n (tm_succ k) -> numeric_value k ->
      evaluates b vb -> evaluates s vs ->
      evaluates (tm_app (tm_app vs k) (tm_natrec k vb vs)) result ->
      evaluates (tm_natrec n b s) result
  | EvalChoiceLeft : forall t1 t2 v,
      evaluates t1 v -> locally_closed_tm t2 -> evaluates (tm_choice t1 t2) v
  | EvalChoiceRight : forall t1 t2 v,
      locally_closed_tm t1 -> evaluates t2 v -> evaluates (tm_choice t1 t2) v.

Definition binary_relation := tm -> tm -> Prop.

Record binary_candidate := {
  candidate_relation : binary_relation;
  candidate_values : forall v1 v2, candidate_relation v1 v2 -> value v1 /\ value v2
}.

Definition binary_env := atom -> option binary_candidate.
Definition relation_update (rho : binary_env) (X : atom) (a : binary_candidate) :=
  fun Y => if Nat.eqb X Y then Some a else rho Y.

Definition results_match (R : binary_relation) (t1 t2 : tm) : Prop :=
  exists v1 v2,
    evaluates t1 v1 /\ evaluates t2 v2 /\ R v1 v2.

Definition expression_lifting (R : binary_relation) (t1 t2 : tm) : Prop :=
  locally_closed_tm t1 /\ locally_closed_tm t2 /\ results_match R t1 t2.

Fixpoint value_relation (eta : list binary_candidate) (rho : binary_env)
    (T : ty) (v1 v2 : tm) : Prop :=
  match T with
  | Ty_BVar i =>
      match nth_error eta i with Some a => a.(candidate_relation) v1 v2 | None => False end
  | Ty_FVar X =>
      match rho X with Some a => a.(candidate_relation) v1 v2 | None => False end
  | Ty_Arrow T1 T2 =>
      value v1 /\ value v2 /\
      exists U1 body1 U2 body2,
        v1 = tm_abs U1 body1 /\ v2 = tm_abs U2 body2 /\
        forall arg1 arg2, value_relation eta rho T1 arg1 arg2 ->
          expression_lifting (value_relation eta rho T2)
            (open_tm body1 arg1) (open_tm body2 arg2)
  | Ty_All T =>
      value v1 /\ value v2 /\
      exists body1 body2,
        v1 = tm_tabs body1 /\ v2 = tm_tabs body2 /\
        forall (U1 U2 : ty) (a : binary_candidate),
          locally_closed_ty U1 -> locally_closed_ty U2 ->
          expression_lifting (value_relation (a :: eta) rho T)
            (open_tm_ty body1 U1) (open_tm_ty body2 U2)
  | Ty_Bool => (v1 = tm_true /\ v2 = tm_true) \/ (v1 = tm_false /\ v2 = tm_false)
  | Ty_Nat => v1 = v2 /\ numeric_value v1
  end.

Definition expression_relation eta rho T t1 t2 :=
  expression_lifting (value_relation eta rho T) t1 t2.

(* Some small pieces of infrastructure for the logical-relations proof. *)
Fixpoint ty_fv (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow T1 T2 => ty_fv T1 ++ ty_fv T2
  | Ty_All T1 => ty_fv T1
  | Ty_Bool | Ty_Nat => []
  end.

Fixpoint tm_fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs _ t1 => tm_fv t1
  | tm_app t1 t2 => tm_fv t1 ++ tm_fv t2
  | tm_tabs t1 => tm_fv t1
  | tm_tapp t1 _ => tm_fv t1
  | tm_true | tm_false | tm_zero => []
  | tm_if t1 t2 t3 => tm_fv t1 ++ tm_fv t2 ++ tm_fv t3
  | tm_succ t1 => tm_fv t1
  | tm_natrec n b s => tm_fv n ++ tm_fv b ++ tm_fv s
  | tm_choice t1 t2 => tm_fv t1 ++ tm_fv t2
  end.

Fixpoint subst_ctx (Gamma : context) (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x =>
      match lookup_context x Gamma with
      | Some _ => sigma x
      | None => tm_fvar x
      end
  | tm_abs T t1 => tm_abs T (subst_ctx Gamma sigma t1)
  | tm_app t1 t2 => tm_app (subst_ctx Gamma sigma t1) (subst_ctx Gamma sigma t2)
  | tm_tabs t1 => tm_tabs (subst_ctx Gamma sigma t1)
  | tm_tapp t1 T => tm_tapp (subst_ctx Gamma sigma t1) T
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (subst_ctx Gamma sigma t1)
                         (subst_ctx Gamma sigma t2) (subst_ctx Gamma sigma t3)
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (subst_ctx Gamma sigma t1)
  | tm_natrec n b s => tm_natrec (subst_ctx Gamma sigma n)
                                  (subst_ctx Gamma sigma b)
                                  (subst_ctx Gamma sigma s)
  | tm_choice t1 t2 => tm_choice (subst_ctx Gamma sigma t1)
                                (subst_ctx Gamma sigma t2)
  end.

Definition extend_subst (x : atom) (a : tm) (sigma : atom -> tm) : atom -> tm :=
  fun y => if Nat.eqb x y then a else sigma y.

Fixpoint ctx_dom (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (x,_) :: Gamma' => x :: ctx_dom Gamma'
  end.

Lemma not_in_app_l : forall (x : atom) l1 l2,
  ~ In x (l1 ++ l2) -> ~ In x l1.
Proof. intros; intro; apply H; apply in_or_app; auto. Qed.

Lemma not_in_app_r : forall (x : atom) l1 l2,
  ~ In x (l1 ++ l2) -> ~ In x l2.
Proof. intros; intro; apply H; apply in_or_app; auto. Qed.

Definition rel_env (eta : list binary_candidate) (rho : binary_env)
    (Gamma : context) (sigma1 sigma2 : atom -> tm) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    value_relation eta rho T (sigma1 x) (sigma2 x).

Lemma numeric_lc : forall n, numeric_value n -> locally_closed_tm n.
Proof. intros n H; induction H; constructor; auto. Qed.

Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof.
  intros v H; induction H.
  - assumption.
  - assumption.
  - constructor.
  - constructor.
  - apply numeric_lc; assumption.
Qed.

Lemma open_tm_rec_shift_lc : forall K k t,
  lc_tm_at K k t -> forall j u, open_tm_rec (j+k) u t = t.
Proof.
  intros K k t H; induction H; intros; simpl.
  - destruct (Nat.eqb (j + k) i) eqn:E; [apply Nat.eqb_eq in E; lia | reflexivity].
  - reflexivity.
  - f_equal. replace (S (j + k)) with (j + S k) by lia. apply IHlc_tm_at.
  - f_equal; [apply IHlc_tm_at1 | apply IHlc_tm_at2].
  - f_equal. apply IHlc_tm_at.
  - f_equal. apply IHlc_tm_at.
  - reflexivity.
  - reflexivity.
  - f_equal; [apply IHlc_tm_at1 | apply IHlc_tm_at2 | apply IHlc_tm_at3].
  - reflexivity.
  - f_equal. apply IHlc_tm_at.
  - f_equal; [apply IHlc_tm_at1 | apply IHlc_tm_at2 | apply IHlc_tm_at3].
  - f_equal; [apply IHlc_tm_at1 | apply IHlc_tm_at2].
Qed.

Lemma rel_env_update : forall eta rho Gamma sigma1 sigma2 x T a1 a2,
  rel_env eta rho Gamma sigma1 sigma2 ->
  value_relation eta rho T a1 a2 ->
  rel_env eta rho ((x,T)::Gamma) (extend_subst x a1 sigma1)
    (extend_subst x a2 sigma2).
Proof.
  unfold rel_env, extend_subst; intros.
  simpl in H1. destruct (Nat.eqb x0 x) eqn:E.
  - apply Nat.eqb_eq in E. subst x0. inversion H1; subst.
    rewrite Nat.eqb_refl. exact H0.
  - assert (E' : (x =? x0) = false).
    { destruct (Nat.eqb x x0) eqn:Q; auto.
      apply Nat.eqb_eq in Q. subst x0. rewrite Nat.eqb_refl in E. discriminate. }
    rewrite E'. simpl. apply H with (x := x0) (T := T0). exact H1.
Qed.

Lemma subst_ctx_open_rec : forall t Gamma sigma x a k,
  ~ In x (ctx_dom Gamma) -> ~ In x (tm_fv t) ->
  (forall y T, lookup_context y Gamma = Some T -> locally_closed_tm (sigma y)) ->
  subst_ctx ((x, Ty_Bool) :: Gamma) (extend_subst x a sigma)
    (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k a (subst_ctx Gamma sigma t).
Proof.
  induction t; simpl; intros; try reflexivity.
  - destruct (Nat.eqb k n); simpl; try (unfold extend_subst; rewrite Nat.eqb_refl); reflexivity.
  - destruct (Nat.eqb x a) eqn:E; simpl in *.
    + apply Nat.eqb_eq in E. subst a. exfalso. apply H0. simpl; auto.
    + unfold extend_subst. rewrite E. simpl.
      assert (E' : (a =? x) = false).
      { destruct (Nat.eqb a x) eqn:Q; auto.
        apply Nat.eqb_eq in Q. subst a. rewrite Nat.eqb_refl in E. discriminate. }
      rewrite E'. destruct (lookup_context a Gamma) eqn:Q; try reflexivity.
      pose proof (open_tm_rec_shift_lc 0 0 (sigma a) (H1 a t Q) k a0) as Z1.
      pose proof (open_tm_rec_shift_lc 0 0 (sigma a) (H1 a t Q) 0 a0) as Z0.
      replace (k + 0) with k in Z1 by lia.
      simpl in Z0. rewrite Z1.
      reflexivity.
  - f_equal. eapply IHt; eauto.
  - assert (H01 := not_in_app_l x (tm_fv t1) (tm_fv t2) H0).
    assert (H02 := not_in_app_r x (tm_fv t1) (tm_fv t2) H0).
    f_equal; [eapply IHt1; eauto | eapply IHt2; eauto].
  - f_equal. eapply IHt; eauto.
  - f_equal. eapply IHt; eauto.
  - rewrite app_assoc in H0.
    assert (H012 := not_in_app_l x (tm_fv t1 ++ tm_fv t2) (tm_fv t3) H0).
    assert (H03 := not_in_app_r x (tm_fv t1 ++ tm_fv t2) (tm_fv t3) H0).
    assert (H01 := not_in_app_l x (tm_fv t1) (tm_fv t2) H012).
    assert (H02 := not_in_app_r x (tm_fv t1) (tm_fv t2) H012).
    f_equal; [eapply IHt1; eauto | eapply IHt2; eauto | eapply IHt3; eauto].
  - f_equal. eapply IHt; eauto.
  - rewrite app_assoc in H0.
    assert (H012 := not_in_app_l x (tm_fv t1 ++ tm_fv t2) (tm_fv t3) H0).
    assert (H03 := not_in_app_r x (tm_fv t1 ++ tm_fv t2) (tm_fv t3) H0).
    assert (H01 := not_in_app_l x (tm_fv t1) (tm_fv t2) H012).
    assert (H02 := not_in_app_r x (tm_fv t1) (tm_fv t2) H012).
    f_equal; [eapply IHt1; eauto | eapply IHt2; eauto | eapply IHt3; eauto].
  - assert (H01 := not_in_app_l x (tm_fv t1) (tm_fv t2) H0).
    assert (H02 := not_in_app_r x (tm_fv t1) (tm_fv t2) H0).
    f_equal; [eapply IHt1; eauto | eapply IHt2; eauto].
Qed.

Lemma subst_ctx_open : forall t Gamma sigma x a,
  ~ In x (ctx_dom Gamma) -> ~ In x (tm_fv t) ->
  (forall y T, lookup_context y Gamma = Some T -> locally_closed_tm (sigma y)) ->
  subst_ctx ((x, Ty_Bool) :: Gamma) (extend_subst x a sigma)
    (open_tm t (tm_fvar x)) = open_tm (subst_ctx Gamma sigma t) a.
Proof.
  intros; apply subst_ctx_open_rec; assumption.
Qed.

Fixpoint list_max (l : list nat) : nat :=
  match l with [] => 0 | x :: l' => Nat.max x (list_max l') end.

Lemma in_list_max : forall x l, In x l -> x <= list_max l.
Proof.
  induction l as [|a l IH].
  - intros H. simpl in H. contradiction.
  - intros H. simpl in H. destruct H as [->|H].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; exact H | apply Nat.le_max_r].
Qed.

Lemma fresh_from : forall l : list nat, exists x, ~ In x l.
Proof.
  intro l. exists (S (list_max l)).
  intro H. pose proof (in_list_max _ _ H). lia.
Qed.

Lemma lc_tm_weaken : forall K k t, lc_tm_at K k t -> lc_tm_at K (S k) t.
Proof.
  intros K k t H; induction H.
  - apply lc_tm_bvar; lia.
  - constructor.
  - apply lc_tm_abs; [exact H | apply IHlc_tm_at].
  - apply lc_tm_app; [apply IHlc_tm_at1 | apply IHlc_tm_at2].
  - apply lc_tm_tabs; exact IHlc_tm_at.
  - apply lc_tm_tapp; [exact IHlc_tm_at | exact H0].
  - constructor.
  - constructor.
  - apply lc_tm_if; [apply IHlc_tm_at1 | apply IHlc_tm_at2 | apply IHlc_tm_at3].
  - constructor.
  - apply lc_tm_succ; exact IHlc_tm_at.
  - apply lc_tm_rec; [apply IHlc_tm_at1 | apply IHlc_tm_at2 | apply IHlc_tm_at3].
  - apply lc_tm_choice; [apply IHlc_tm_at1 | apply IHlc_tm_at2].
Qed.

Lemma lc_ty_type_weaken : forall K T, lc_ty_at K T -> lc_ty_at (S K) T.
Proof.
  intros K T H; induction H.
  - apply lc_ty_bvar; lia.
  - constructor.
  - apply lc_ty_arrow; assumption.
  - apply lc_ty_all; exact IHlc_ty_at.
  - constructor.
  - constructor.
Qed.

Lemma lc_tm_type_weaken : forall K k t, lc_tm_at K k t -> lc_tm_at (S K) k t.
Proof.
  intros K k t H; induction H.
  - constructor; exact H.
  - constructor.
  - apply lc_tm_abs; [apply lc_ty_type_weaken; exact H | exact IHlc_tm_at].
  - apply lc_tm_app; assumption.
  - apply lc_tm_tabs; exact IHlc_tm_at.
  - apply lc_tm_tapp; [exact IHlc_tm_at | apply lc_ty_type_weaken; exact H0].
  - constructor.
  - constructor.
  - apply lc_tm_if; assumption.
  - constructor.
  - apply lc_tm_succ; exact IHlc_tm_at.
  - apply lc_tm_rec; assumption.
  - apply lc_tm_choice; assumption.
Qed.

Lemma lc_tm_open_inv : forall K k t u,
  lc_tm_at K k u ->
  lc_tm_at K k (open_tm_rec k u t) ->
  lc_tm_at K (S k) t.
Proof.
  intros K k t u; revert K k u; induction t; intros K k u Hu Hop; simpl in Hop.
  - destruct (Nat.eqb k n) eqn:E.
    + apply lc_tm_bvar. apply Nat.eqb_eq in E. lia.
    + inversion Hop; subst. apply lc_tm_bvar. lia.
  - constructor.
  - inversion Hop; subst. apply lc_tm_abs.
    + assumption.
    + apply IHt with (K := K) (k := S k) (u := u).
      * apply lc_tm_weaken; exact Hu.
      * exact H4.
  - inversion Hop; subst. apply lc_tm_app.
    + apply IHt1 with (u := u); assumption.
    + apply IHt2 with (u := u); assumption.
  - inversion Hop; subst. apply lc_tm_tabs.
    apply IHt with (K := S K) (k := k) (u := u).
    + apply lc_tm_type_weaken; exact Hu.
    + exact H2.
  - inversion Hop; subst. apply lc_tm_tapp.
    + apply IHt with (u := u); assumption.
    + assumption.
  - constructor.
  - constructor.
  - inversion Hop; subst. apply lc_tm_if.
    + apply IHt1 with (u := u); assumption.
    + apply IHt2 with (u := u); assumption.
    + apply IHt3 with (u := u); assumption.
  - constructor.
  - inversion Hop; subst. apply lc_tm_succ.
    apply IHt with (u := u); assumption.
  - inversion Hop; subst. apply lc_tm_rec.
    + apply IHt1 with (u := u); assumption.
    + apply IHt2 with (u := u); assumption.
    + apply IHt3 with (u := u); assumption.
  - inversion Hop; subst. apply lc_tm_choice.
    + apply IHt1 with (u := u); assumption.
    + apply IHt2 with (u := u); assumption.
Qed.

Lemma lc_ty_open_inv : forall K T X,
  lc_ty_at K (open_ty_rec K (Ty_FVar X) T) ->
  lc_ty_at (S K) T.
Proof.
  intros K T X; revert K; induction T; intros K H; simpl in H.
  - destruct (Nat.eqb K n) eqn:E.
    + apply lc_ty_bvar. apply Nat.eqb_eq in E. lia.
    + inversion H; subst. apply lc_ty_bvar. lia.
  - constructor.
  - inversion H; subst. apply lc_ty_arrow; [apply IHT1 | apply IHT2]; assumption.
  - inversion H; subst. apply lc_ty_all. apply IHT. assumption.
  - constructor.
  - constructor.
Qed.

Lemma lc_ty_open_inv_strong : forall K T X,
  lc_ty_at (S K) (open_ty_rec K (Ty_FVar X) T) ->
  lc_ty_at (S K) T.
Proof.
  intros K T X; revert K; induction T; intros K H; simpl in H.
  - destruct (Nat.eqb K n) eqn:E.
    + apply lc_ty_bvar. apply Nat.eqb_eq in E. lia.
    + inversion H; subst. apply lc_ty_bvar; lia.
  - constructor.
  - inversion H; subst. apply lc_ty_arrow; [apply IHT1 | apply IHT2]; assumption.
  - inversion H; subst. apply lc_ty_all. apply IHT. assumption.
  - constructor.
  - constructor.
Qed.

Lemma lc_ty_open : forall K T U,
  lc_ty_at (S K) T -> lc_ty_at K U ->
  lc_ty_at K (open_ty_rec K U T).
Proof.
  intros K T U HT HU; revert K U HT HU; induction T; intros K U HT HU; simpl.
  - destruct (Nat.eqb K n) eqn:E.
    + exact HU.
    + inversion HT; subst. apply lc_ty_bvar. apply Nat.eqb_neq in E. lia.
  - constructor.
  - inversion HT; subst. apply lc_ty_arrow; [apply IHT1 | apply IHT2]; assumption.
  - inversion HT; subst. apply lc_ty_all. apply IHT.
    + assumption.
    + apply lc_ty_type_weaken; exact HU.
  - constructor.
  - constructor.
Qed.

Lemma lc_tm_ty_open_inv : forall K k t X,
  lc_tm_at (S K) k (open_tm_ty_rec K (Ty_FVar X) t) ->
  lc_tm_at (S K) k t.
Proof.
  intros K k t X; revert K k; induction t; intros K k H; simpl in H.
  - constructor; inversion H; assumption.
  - constructor.
  - inversion H; subst. apply lc_tm_abs.
    + apply lc_ty_open_inv_strong with (X := X); assumption.
    + apply IHt; assumption.
  - inversion H; subst. apply lc_tm_app; [apply IHt1 | apply IHt2]; assumption.
  - inversion H; subst. apply lc_tm_tabs. apply IHt; assumption.
  - inversion H; subst. apply lc_tm_tapp.
    + apply IHt; assumption.
    + apply lc_ty_open_inv_strong with (X := X); assumption.
  - constructor.
  - constructor.
  - inversion H; subst. apply lc_tm_if; [apply IHt1 | apply IHt2 | apply IHt3]; assumption.
  - constructor.
  - inversion H; subst. apply lc_tm_succ. apply IHt; assumption.
  - inversion H; subst. apply lc_tm_rec; [apply IHt1 | apply IHt2 | apply IHt3]; assumption.
  - inversion H; subst. apply lc_tm_choice; [apply IHt1 | apply IHt2]; assumption.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  fix W 3. intros Delta T H. destruct H.
  - constructor.
  - apply lc_ty_arrow; [exact (W _ _ H) | exact (W _ _ H0)].
  - apply lc_ty_all. destruct (fresh_from L) as [X HX].
    apply lc_ty_open_inv with (X := X).
    apply (W _ _ (H X HX)).
  - constructor.
  - constructor.
Qed.

Lemma has_type_lc : forall Delta Gamma t T, has_type Delta Gamma t T ->
  locally_closed_ty T /\ locally_closed_tm t.
Proof.
  fix W 5. intros Delta Gamma t T D. destruct D.
  - split; [exact (wf_ty_lc _ _ H0) | constructor].
  - destruct (fresh_from L) as [x Hx].
    destruct (W _ _ _ _ (H0 x Hx)) as [HT Ht].
    split; [apply lc_ty_arrow; [exact (wf_ty_lc _ _ H) | exact HT] |].
    apply lc_tm_abs; [exact (wf_ty_lc _ _ H) |].
    apply lc_tm_open_inv with (u := tm_fvar x); [constructor | exact Ht].
  - destruct (W _ _ _ _ D1) as [HA hterm1], (W _ _ _ _ D2) as [H2 hterm2].
    inversion HA; subst. split; [assumption | apply lc_tm_app; assumption].
  - destruct (fresh_from L) as [X Hx].
    destruct (W _ _ _ _ (H X Hx)) as [HT Ht].
    split; [apply lc_ty_all; apply lc_ty_open_inv with (X := X); exact HT |].
    apply lc_tm_tabs. apply lc_tm_ty_open_inv with (X := X).
    apply lc_tm_type_weaken; exact Ht.
  - destruct (W _ _ _ _ D) as [HT ht]. inversion HT; subst.
    split; [apply lc_ty_open; [assumption | exact (wf_ty_lc _ _ H)] | apply lc_tm_tapp; [exact ht | exact (wf_ty_lc _ _ H)]].
  - split; [constructor | constructor].
  - split; [constructor | constructor].
  - destruct (W _ _ _ _ D2) as [HT h2], (W _ _ _ _ D3) as [_ h3],
      (W _ _ _ _ D1) as [_ h1].
    split; [exact HT | apply lc_tm_if; assumption].
  - split; [constructor | constructor].
  - destruct (W _ _ _ _ D) as [HT hn]. split; [constructor | apply lc_tm_succ; exact hn].
  - destruct (W _ _ _ _ D1) as [_ hn], (W _ _ _ _ D2) as [HT hb],
      (W _ _ _ _ D3) as [_ hs].
    split; [exact HT | apply lc_tm_rec; assumption].
  - destruct (W _ _ _ _ D1) as [HT h1], (W _ _ _ _ D2) as [_ h2].
    split; [exact HT | apply lc_tm_choice; assumption].
Qed.

Definition candidates_ok (eta : list binary_candidate) (rho : binary_env) : Prop :=
  (forall a, In a eta -> forall x y, candidate_relation a x y -> value x /\ value y) /\
  (forall X a, rho X = Some a -> forall x y, candidate_relation a x y -> value x /\ value y).

Lemma value_relation_values : forall eta rho T v1 v2,
  candidates_ok eta rho -> value_relation eta rho T v1 v2 -> value v1 /\ value v2.
Proof.
  fix W 5. intros eta rho T v1 v2 Hok R. destruct T; simpl in R.
  - destruct (nth_error eta n) eqn:E; [pose proof (nth_error_In eta n E) as Eb; eapply (proj1 Hok); [exact Eb | exact R] | contradiction].
  - destruct (rho a) eqn:E; [exact (proj2 Hok a b E v1 v2 R) | contradiction].
  - destruct R as [R1 [R2 _]]. exact (conj R1 R2).
  - destruct R as [R1 [R2 _]]. exact (conj R1 R2).
  - destruct R as [[-> ->]|[-> ->]]; constructor.
  - destruct R as [-> R]. split; [apply v_nat; exact R | apply v_nat; exact R].
Qed.

Lemma expression_lifting_ext : forall R S t1 t2,
  (forall x y, R x y <-> S x y) ->
  expression_lifting R t1 t2 <-> expression_lifting S t1 t2.
Proof.
  intros; unfold expression_lifting, results_match; split; intros [A [B C]];
  repeat split; try assumption; destruct C as [v1 [v2 [C1 [C2 C3]]]];
  exists v1, v2; repeat split; try assumption; firstorder.
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

End SystemFParametricityIfNondeterminismRecursionMediumTask.
