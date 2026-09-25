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

Lemma numeric_value_closed : forall n,
  numeric_value n -> locally_closed_tm n.
Proof.
  induction 1; constructor; assumption.
Qed.

Lemma value_closed : forall v, value v -> locally_closed_tm v.
Proof.
  intros v Hv; destruct Hv; eauto using numeric_value_closed;
    unfold locally_closed_tm; constructor.
Qed.

Lemma evaluates_value : forall t v, evaluates t v -> value v.
Proof.
  induction 1; eauto using value; constructor; constructor; assumption.
Qed.

Lemma evaluates_closed : forall t v, evaluates t v -> locally_closed_tm t.
Proof.
  induction 1; try solve [apply value_closed; assumption];
    unfold locally_closed_tm in *;
    eauto using value_closed, lc_tm_at.
Qed.

Lemma relation_values : forall eta rho T v1 v2,
  value_relation eta rho T v1 v2 -> value v1 /\ value v2.
Proof.
  intros eta rho T; induction T; simpl; intros v1 v2 H.
  - destruct (nth_error eta n) as [a|]; [exact (candidate_values a _ _ H)|contradiction].
  - destruct (rho a) as [b|]; [exact (candidate_values b _ _ H)|contradiction].
  - tauto.
  - tauto.
  - destruct H as [[-> ->] | [-> ->]]; auto.
  - destruct H as [-> H]; split; constructor; exact H.
Qed.

Lemma open_ty_fvar_closes : forall T k X,
  lc_ty_at k (open_ty_rec k (Ty_FVar X) T) -> lc_ty_at (S k) T.
Proof.
  induction T; intros k X H; simpl in *; try (constructor; auto; fail).
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst; constructor; lia.
    + inversion H; subst; constructor; lia.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
Qed.

Lemma fresh_atom_exists : forall L : list atom, exists X, ~ In X L.
Proof.
  intros L; exists (S (fold_right Nat.max 0 L)).
  assert (forall n, In n L -> n <= fold_right Nat.max 0 L) as Hbound.
  { induction L as [|a rest IH]; simpl; intros n Hn.
    - contradiction.
    - destruct Hn as [<-|Hn]; [apply Nat.le_max_l|].
      eapply Nat.le_trans; [apply IH; exact Hn|apply Nat.le_max_r]. }
  intros Hin; specialize (Hbound _ Hin); lia.
Qed.

Lemma wf_ty_closed : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  induction 1; unfold locally_closed_ty in *; eauto using lc_ty_at.
  destruct (fresh_atom_exists L) as [X HX].
  specialize (H0 X HX); apply open_ty_fvar_closes in H0.
  now constructor.
Qed.

Lemma open_tm_fvar_closes : forall t K k x,
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) -> lc_tm_at K (S k) t.
Proof.
  induction t; intros K k x H; simpl in H;
    try (inversion H; subst; constructor; eauto; fail).
  destruct (Nat.eqb k n) eqn:E.
  - apply Nat.eqb_eq in E; subst; constructor; lia.
  - inversion H; subst; constructor; lia.
Qed.

Lemma open_tm_ty_fvar_closes : forall t K k X,
  lc_tm_at K k (open_tm_ty_rec K (Ty_FVar X) t) ->
  lc_tm_at (S K) k t.
Proof.
  induction t; intros K k X H; simpl in H;
    inversion H; subst; constructor;
    eauto using open_ty_fvar_closes.
Qed.

Lemma typing_closed : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  induction 1; unfold locally_closed_tm in *;
    eauto using lc_tm_at, wf_ty_closed.
  - destruct (fresh_atom_exists L) as [x Hx].
    specialize (H1 x Hx); apply open_tm_fvar_closes in H1.
    constructor; [exact (wf_ty_closed _ _ H)|exact H1].
  - destruct (fresh_atom_exists L) as [X HX].
    specialize (H0 X HX); apply open_tm_ty_fvar_closes in H0.
    now constructor.
  - apply lc_tm_tapp; [assumption|eapply wf_ty_closed; eassumption].
Qed.

Lemma lc_ty_weaken : forall K T, lc_ty_at K T ->
  forall K', K <= K' -> lc_ty_at K' T.
Proof.
  induction 1; intros K' Hle.
  - apply lc_ty_bvar; lia.
  - constructor.
  - apply lc_ty_arrow; eauto.
  - apply lc_ty_all; apply IHlc_ty_at; lia.
  - constructor.
  - constructor.
Qed.

Lemma lc_tm_weaken : forall K k t, lc_tm_at K k t ->
  forall K' k', K <= K' -> k <= k' -> lc_tm_at K' k' t.
Proof.
  induction 1; intros K' k' HK Hk.
  - apply lc_tm_bvar; lia.
  - constructor.
  - apply lc_tm_abs; [eapply lc_ty_weaken; eauto|apply IHlc_tm_at; lia].
  - apply lc_tm_app; eauto.
  - apply lc_tm_tabs; apply IHlc_tm_at; lia.
  - apply lc_tm_tapp; eauto using lc_ty_weaken.
  - constructor.
  - constructor.
  - apply lc_tm_if; eauto.
  - constructor.
  - apply lc_tm_succ; eauto.
  - apply lc_tm_rec; eauto.
  - apply lc_tm_choice; eauto.
Qed.

Lemma open_ty_preserves : forall T K U,
  lc_ty_at (S K) T -> lc_ty_at K U ->
  lc_ty_at K (open_ty_rec K U T).
Proof.
  induction T; intros K U HT HU; simpl in *;
    try (inversion HT; subst; constructor; eauto using lc_ty_weaken; fail).
  destruct (Nat.eqb K n) eqn:E; [assumption|].
  inversion HT; subst; constructor; apply Nat.eqb_neq in E; lia.
Qed.

Lemma open_tm_preserves : forall t K k u,
  lc_tm_at K (S k) t -> lc_tm_at K k u ->
  lc_tm_at K k (open_tm_rec k u t).
Proof.
  induction t; intros K k u HT HU; simpl in *;
    try (inversion HT; subst; constructor;
      eauto using lc_tm_weaken, lc_ty_weaken; fail).
  destruct (Nat.eqb k n) eqn:E; [assumption|].
  inversion HT; subst; constructor; apply Nat.eqb_neq in E; lia.
Qed.

Lemma open_tm_ty_preserves : forall t K k U,
  lc_tm_at (S K) k t -> lc_ty_at K U ->
  lc_tm_at K k (open_tm_ty_rec K U t).
Proof.
  induction t; intros K k U HT HU; simpl in *;
    inversion HT; subst; constructor;
    eauto using open_ty_preserves, lc_ty_weaken.
Qed.

Lemma step_closed : forall t u, t --> u ->
  locally_closed_tm t -> locally_closed_tm u.
Proof.
  induction 1; intros Hlc;
    unfold locally_closed_tm in *;
    inversion Hlc; subst;
    eauto using lc_tm_at, value_closed, numeric_value_closed.
  - eapply open_tm_preserves; eauto using value_closed.
    inversion H; assumption.
  - eapply open_tm_ty_preserves; eauto.
    inversion H; assumption.
  - apply lc_tm_app.
    + apply lc_tm_app; [exact H9|exact (numeric_value_closed _ H)].
    + apply lc_tm_rec; [exact (numeric_value_closed _ H)|exact H8|exact H9].
Qed.

Lemma multi_closed : forall t u, t -->* u ->
  locally_closed_tm t -> locally_closed_tm u.
Proof.
  induction 1; eauto using step_closed.
Qed.

Lemma multi_trans : forall t u v, t -->* u -> u -->* v -> t -->* v.
Proof.
  induction 1; eauto using multi.
Qed.

Lemma multi_app_left : forall f f' arg,
  f -->* f' -> locally_closed_tm arg -> tm_app f arg -->* tm_app f' arg.
Proof.
  induction 1; intros Harg; eauto using multi, step.
Qed.

Lemma multi_app_right : forall f arg arg',
  value f -> arg -->* arg' -> tm_app f arg -->* tm_app f arg'.
Proof.
  intros f arg arg' Hf Hm; induction Hm; eauto using multi, step.
Qed.

Lemma multi_tapp_cong : forall t u T,
  t -->* u -> locally_closed_ty T -> tm_tapp t T -->* tm_tapp u T.
Proof.
  induction 1; intros HT; eauto using multi, step.
Qed.

Lemma multi_if_cond : forall c c' t u,
  c -->* c' -> locally_closed_tm t -> locally_closed_tm u ->
  tm_if c t u -->* tm_if c' t u.
Proof.
  induction 1; intros Ht Hu; eauto using multi, step.
Qed.

Lemma multi_succ_cong : forall t u,
  t -->* u -> tm_succ t -->* tm_succ u.
Proof.
  induction 1; eauto using multi, step.
Qed.

Lemma multi_rec_arg : forall n n' b s,
  n -->* n' -> locally_closed_tm b -> locally_closed_tm s ->
  tm_natrec n b s -->* tm_natrec n' b s.
Proof.
  induction 1; intros Hb Hs; eauto using multi, step.
Qed.

Lemma multi_rec_base : forall n b b' s,
  numeric_value n -> b -->* b' -> locally_closed_tm s ->
  tm_natrec n b s -->* tm_natrec n b' s.
Proof.
  intros n b b' s Hn Hm Hs; induction Hm; eauto using multi, step.
Qed.

Lemma multi_rec_step : forall n b s s',
  numeric_value n -> value b -> s -->* s' ->
  tm_natrec n b s -->* tm_natrec n b s'.
Proof.
  intros n b s s' Hn Hb Hm; induction Hm; eauto using multi, step.
Qed.

Lemma evaluates_multi : forall t v, evaluates t v -> t -->* v.
Proof.
  induction 1.
  - constructor.
  - eapply multi_trans; [eapply multi_app_left; eauto using evaluates_closed|].
    eapply multi_trans; [eapply multi_app_right; eauto using evaluates_value|].
    eapply multi_step; [apply ST_AppAbs; eauto using evaluates_value,
       value_closed, evaluates_closed|assumption].
  - eapply multi_trans; [eapply multi_tapp_cong; eauto|].
    eapply multi_step; [apply ST_TAppTabs; eauto using evaluates_value,
       value_closed|assumption].
  - eapply multi_trans; [eapply multi_if_cond; eauto using evaluates_closed|].
    eapply multi_step; [apply ST_IfTrue; eauto using evaluates_closed|assumption].
  - eapply multi_trans; [eapply multi_if_cond; eauto using evaluates_closed|].
    eapply multi_step; [apply ST_IfFalse; eauto using evaluates_closed|assumption].
  - apply multi_succ_cong; assumption.
  - eapply multi_trans; [eapply multi_rec_arg; eauto using evaluates_closed|].
    eapply multi_trans; [apply multi_rec_base;
      [constructor|exact IHevaluates2|eauto using evaluates_closed]|].
    eapply multi_trans; [apply multi_rec_step;
      [constructor|eauto using evaluates_value|exact IHevaluates3]|].
    eapply multi_step; [apply ST_RecZero; eauto using evaluates_value|constructor].
  - eapply multi_trans; [eapply multi_rec_arg; eauto using evaluates_closed|].
    eapply multi_trans; [apply multi_rec_base;
      [constructor; assumption|exact IHevaluates2|eauto using evaluates_closed]|].
    eapply multi_trans; [apply multi_rec_step;
      [constructor; assumption|eauto using evaluates_value|exact IHevaluates3]|].
    eapply multi_step; [apply ST_RecSucc; eauto using evaluates_value|assumption].
  - eapply multi_step; [apply ST_ChoiceLeft; eauto using evaluates_closed|assumption].
  - eapply multi_step; [apply ST_ChoiceRight; eauto using evaluates_closed|assumption].
Qed.

Lemma expression_application : forall eta rho A B f1 f2 a1 a2,
  expression_relation eta rho (Ty_Arrow A B) f1 f2 ->
  expression_relation eta rho A a1 a2 ->
  expression_relation eta rho B (tm_app f1 a1) (tm_app f2 a2).
Proof.
  intros eta rho A B f1 f2 a1 a2
    [Hf1 [Hf2 [vf1 [vf2 [Ef1 [Ef2 Hf]]]]]]
    [Ha1 [Ha2 [va1 [va2 [Ea1 [Ea2 Ha]]]]]].
  simpl in Hf.
  destruct Hf as [_ [_ [U1 [body1 [U2 [body2 [-> [-> Hbody]]]]]]]].
  specialize (Hbody va1 va2 Ha).
  destruct Hbody as [_ [_ [res1 [res2 [Eb1 [Eb2 Hb]]]]]].
  repeat split; try (unfold locally_closed_tm in *; constructor; assumption).
  exists res1, res2; repeat split; eauto using evaluates.
Qed.

Lemma expression_type_application : forall eta rho T f1 f2 U1 U2 a,
  expression_relation eta rho (Ty_All T) f1 f2 ->
  locally_closed_ty U1 -> locally_closed_ty U2 ->
  expression_lifting (value_relation (a :: eta) rho T)
    (tm_tapp f1 U1) (tm_tapp f2 U2).
Proof.
  intros eta rho T f1 f2 U1 U2 a
    [Hf1 [Hf2 [vf1 [vf2 [Ef1 [Ef2 Hf]]]]]] HU1 HU2.
  simpl in Hf.
  destruct Hf as [_ [_ [body1 [body2 [-> [-> Hbody]]]]]].
  specialize (Hbody U1 U2 a HU1 HU2).
  destruct Hbody as [_ [_ [res1 [res2 [Eb1 [Eb2 Hb]]]]]].
  repeat split; try (unfold locally_closed_tm, locally_closed_ty in *;
    constructor; assumption).
  exists res1, res2; repeat split; eauto using evaluates.
Qed.

Lemma expression_if : forall eta rho T c1 c2 t1 t2 u1 u2,
  expression_relation eta rho Ty_Bool c1 c2 ->
  expression_relation eta rho T t1 t2 ->
  expression_relation eta rho T u1 u2 ->
  expression_relation eta rho T (tm_if c1 t1 u1) (tm_if c2 t2 u2).
Proof.
  intros eta rho T c1 c2 t1 t2 u1 u2
    [Hc1 [Hc2 [vc1 [vc2 [Ec1 [Ec2 Hc]]]]]]
    [Ht1 [Ht2 [vt1 [vt2 [Et1 [Et2 Ht]]]]]]
    [Hu1 [Hu2 [vu1 [vu2 [Eu1 [Eu2 Hu]]]]]].
  repeat split; try (unfold locally_closed_tm in *; constructor; assumption).
  simpl in Hc; destruct Hc as [[-> ->]|[-> ->]].
  - exists vt1, vt2; repeat split; eauto using evaluates.
  - exists vu1, vu2; repeat split; eauto using evaluates.
Qed.

Lemma expression_choice : forall eta rho T t1 t2 u1 u2,
  expression_relation eta rho T t1 t2 ->
  expression_relation eta rho T u1 u2 ->
  expression_relation eta rho T (tm_choice t1 u1) (tm_choice t2 u2).
Proof.
  intros eta rho T t1 t2 u1 u2
    [Ht1 [Ht2 [vt1 [vt2 [Et1 [Et2 Ht]]]]]]
    [Hu1 [Hu2 _]].
  repeat split; try (unfold locally_closed_tm in *; constructor; assumption).
  exists vt1, vt2; repeat split; eauto using evaluates.
Qed.

Lemma expression_true : forall eta rho,
  expression_relation eta rho Ty_Bool tm_true tm_true.
Proof.
  intros; unfold expression_relation, expression_lifting, results_match.
  repeat split; try (unfold locally_closed_tm; constructor).
  exists tm_true, tm_true; repeat split; eauto using evaluates, value.
  left; auto.
Qed.

Lemma expression_false : forall eta rho,
  expression_relation eta rho Ty_Bool tm_false tm_false.
Proof.
  intros; unfold expression_relation, expression_lifting, results_match.
  repeat split; try (unfold locally_closed_tm; constructor).
  exists tm_false, tm_false; repeat split; eauto using evaluates, value.
  right; auto.
Qed.

Lemma expression_zero : forall eta rho,
  expression_relation eta rho Ty_Nat tm_zero tm_zero.
Proof.
  intros; unfold expression_relation, expression_lifting, results_match.
  repeat split; try (unfold locally_closed_tm; constructor).
  exists tm_zero, tm_zero; repeat split; eauto using evaluates, value, numeric_value.
  all: try (apply EvalValue; apply v_nat; constructor).
Qed.

Lemma expression_succ : forall eta rho t1 t2,
  expression_relation eta rho Ty_Nat t1 t2 ->
  expression_relation eta rho Ty_Nat (tm_succ t1) (tm_succ t2).
Proof.
  intros eta rho t1 t2
    [Ht1 [Ht2 [n1 [n2 [En1 [En2 Hn]]]]]].
  simpl in Hn; destruct Hn as [<- Hnv].
  repeat split; try (unfold locally_closed_tm in *; constructor; assumption).
  exists (tm_succ n1), (tm_succ n1); repeat split;
    eauto using evaluates, numeric_value.
Qed.

Lemma expression_value : forall eta rho T v1 v2,
  value_relation eta rho T v1 v2 -> expression_relation eta rho T v1 v2.
Proof.
  intros eta rho T v1 v2 Hr.
  destruct (relation_values _ _ _ _ _ Hr) as [Hv1 Hv2].
  repeat split; eauto using value_closed.
  exists v1, v2; repeat split; eauto using evaluates.
Qed.

Lemma expression_rec_values : forall eta rho T n b1 b2 s1 s2,
  numeric_value n -> value_relation eta rho T b1 b2 ->
  value_relation eta rho (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s1 s2 ->
  expression_relation eta rho T
    (tm_natrec n b1 s1) (tm_natrec n b2 s2).
Proof.
  intros eta rho T n b1 b2 s1 s2 Hn.
  induction Hn as [|n Hn IH]; intros Hb Hs.
  - destruct (relation_values _ _ _ _ _ Hb) as [Hv1 Hv2].
    destruct (relation_values _ _ _ _ _ Hs) as [Hs1 Hs2].
    split; [apply lc_tm_rec; [constructor|exact (value_closed _ Hv1)|exact (value_closed _ Hs1)]|].
    split; [apply lc_tm_rec; [constructor|exact (value_closed _ Hv2)|exact (value_closed _ Hs2)]|].
    exists b1, b2; repeat split; try assumption.
    + eapply EvalRecZero; [apply EvalValue; apply v_nat; constructor|apply EvalValue; exact Hv1|apply EvalValue; exact Hs1].
    + eapply EvalRecZero; [apply EvalValue; apply v_nat; constructor|apply EvalValue; exact Hv2|apply EvalValue; exact Hs2].
  - destruct (relation_values _ _ _ _ _ Hb) as [Hv1 Hv2].
    destruct (relation_values _ _ _ _ _ Hs) as [Hs1 Hs2].
    assert (Hsn : expression_relation eta rho (Ty_Arrow T T)
       (tm_app s1 n) (tm_app s2 n)).
    { eapply expression_application.
      - apply expression_value; exact Hs.
      - apply expression_value; split; [reflexivity|assumption]. }
    specialize (IH Hb Hs).
    assert (Happ : expression_relation eta rho T
       (tm_app (tm_app s1 n) (tm_natrec n b1 s1))
       (tm_app (tm_app s2 n) (tm_natrec n b2 s2))).
    { eapply expression_application; eauto. }
    destruct Happ as [_ [_ [v1 [v2 [Ev1 [Ev2 Hr]]]]]].
    split; [apply lc_tm_rec;
      [apply numeric_value_closed; constructor; exact Hn|exact (value_closed _ Hv1)|exact (value_closed _ Hs1)]|].
    split; [apply lc_tm_rec;
      [apply numeric_value_closed; constructor; exact Hn|exact (value_closed _ Hv2)|exact (value_closed _ Hs2)]|].
    exists v1, v2; repeat split; eauto using evaluates, value, numeric_value.
    + eapply EvalRecSucc; [apply EvalValue; apply v_nat; constructor; exact Hn
      |exact Hn|apply EvalValue; exact Hv1|apply EvalValue; exact Hs1|exact Ev1].
    + eapply EvalRecSucc; [apply EvalValue; apply v_nat; constructor; exact Hn
      |exact Hn|apply EvalValue; exact Hv2|apply EvalValue; exact Hs2|exact Ev2].
Qed.

Lemma numeric_evaluates_self : forall n v,
  numeric_value n -> evaluates n v -> v = n.
Proof.
  intros n v Hn; revert v.
  induction Hn; intros v He; inversion He; subst; auto.
  f_equal; eauto.
Qed.

Lemma value_evaluates_self : forall v w,
  value v -> evaluates v w -> w = v.
Proof.
  intros v w Hv He; destruct Hv.
  - inversion He; reflexivity.
  - inversion He; reflexivity.
  - inversion He; reflexivity.
  - inversion He; reflexivity.
  - eapply numeric_evaluates_self; eauto.
Qed.

Lemma evaluates_rec_compose : forall n n' b b' s s' v,
  evaluates n n' -> evaluates b b' -> evaluates s s' ->
  evaluates (tm_natrec n' b' s') v ->
  evaluates (tm_natrec n b s) v.
Proof.
  intros n n' b b' s s' v En Eb Es Er.
  pose proof (evaluates_value _ _ En) as Hnv.
  pose proof (evaluates_value _ _ Eb) as Hbv.
  pose proof (evaluates_value _ _ Es) as Hsv.
  inversion Er; subst.
  - inversion H; subst; inversion H0.
  - assert (n' = tm_zero) by (symmetry; eapply value_evaluates_self; eauto).
    assert (b' = v) by (symmetry; eapply value_evaluates_self; eauto).
    assert (s' = vs) by (symmetry; eapply value_evaluates_self; eauto).
    subst; eapply EvalRecZero; eauto.
  - assert (n' = tm_succ k) by (symmetry; eapply value_evaluates_self; eauto).
    assert (b' = vb) by (symmetry; eapply value_evaluates_self; eauto).
    assert (s' = vs) by (symmetry; eapply value_evaluates_self; eauto).
    subst; eapply EvalRecSucc; eauto.
Qed.

Lemma expression_rec : forall eta rho T n1 n2 b1 b2 s1 s2,
  expression_relation eta rho Ty_Nat n1 n2 ->
  expression_relation eta rho T b1 b2 ->
  expression_relation eta rho (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s1 s2 ->
  expression_relation eta rho T
    (tm_natrec n1 b1 s1) (tm_natrec n2 b2 s2).
Proof.
  intros eta rho T n1 n2 b1 b2 s1 s2
    [Hn1 [Hn2 [vn1 [vn2 [En1 [En2 Hn]]]]]]
    [Hb1 [Hb2 [vb1 [vb2 [Eb1 [Eb2 Hb]]]]]]
    [Hs1 [Hs2 [vs1 [vs2 [Es1 [Es2 Hs]]]]]].
  destruct Hn as [<- Hnv].
  pose proof (expression_rec_values eta rho T vn1 vb1 vb2 vs1 vs2 Hnv Hb Hs)
    as [_ [_ [v1 [v2 [Er1 [Er2 Hr]]]]]].
  split; [apply lc_tm_rec; assumption|].
  split; [apply lc_tm_rec; assumption|].
  exists v1, v2; repeat split; try assumption.
  - eapply evaluates_rec_compose; eauto.
  - eapply evaluates_rec_compose; eauto.
Qed.

Fixpoint instantiate_ty (sigma : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => sigma X
  | Ty_Arrow A B => Ty_Arrow (instantiate_ty sigma A) (instantiate_ty sigma B)
  | Ty_All A => Ty_All (instantiate_ty sigma A)
  | Ty_Bool => Ty_Bool
  | Ty_Nat => Ty_Nat
  end.

Fixpoint instantiate_tm_ty (sigma : atom -> ty) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T body => tm_abs (instantiate_ty sigma T) (instantiate_tm_ty sigma body)
  | tm_app f arg => tm_app (instantiate_tm_ty sigma f) (instantiate_tm_ty sigma arg)
  | tm_tabs body => tm_tabs (instantiate_tm_ty sigma body)
  | tm_tapp f T => tm_tapp (instantiate_tm_ty sigma f) (instantiate_ty sigma T)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if c l r => tm_if (instantiate_tm_ty sigma c) (instantiate_tm_ty sigma l) (instantiate_tm_ty sigma r)
  | tm_zero => tm_zero
  | tm_succ n => tm_succ (instantiate_tm_ty sigma n)
  | tm_natrec n b s => tm_natrec (instantiate_tm_ty sigma n) (instantiate_tm_ty sigma b) (instantiate_tm_ty sigma s)
  | tm_choice l r => tm_choice (instantiate_tm_ty sigma l) (instantiate_tm_ty sigma r)
  end.

Fixpoint instantiate_tm (theta : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => theta x
  | tm_abs T body => tm_abs T (instantiate_tm theta body)
  | tm_app f arg => tm_app (instantiate_tm theta f) (instantiate_tm theta arg)
  | tm_tabs body => tm_tabs (instantiate_tm theta body)
  | tm_tapp f T => tm_tapp (instantiate_tm theta f) T
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if c l r => tm_if (instantiate_tm theta c) (instantiate_tm theta l) (instantiate_tm theta r)
  | tm_zero => tm_zero
  | tm_succ n => tm_succ (instantiate_tm theta n)
  | tm_natrec n b s => tm_natrec (instantiate_tm theta n) (instantiate_tm theta b) (instantiate_tm theta s)
  | tm_choice l r => tm_choice (instantiate_tm theta l) (instantiate_tm theta r)
  end.

Definition atom_update {A : Type} (sigma : atom -> A) (x : atom) (v : A) : atom -> A :=
  fun y => if Nat.eqb x y then v else sigma y.

Lemma instantiate_ty_closed : forall K T sigma,
  lc_ty_at K T -> (forall X, locally_closed_ty (sigma X)) ->
  lc_ty_at K (instantiate_ty sigma T).
Proof.
  intros K T sigma HT; induction HT; intros Hsigma; simpl;
    eauto using lc_ty_at, lc_ty_weaken.
  eapply lc_ty_weaken; [apply Hsigma|lia].
Qed.

Lemma instantiate_tm_ty_closed : forall K k t sigma,
  lc_tm_at K k t -> (forall X, locally_closed_ty (sigma X)) ->
  lc_tm_at K k (instantiate_tm_ty sigma t).
Proof.
  intros K k t sigma HT; induction HT; intros Hsigma; simpl;
    eauto using lc_tm_at, instantiate_ty_closed.
Qed.

Lemma instantiate_tm_closed : forall K k t theta,
  lc_tm_at K k t -> (forall x, locally_closed_tm (theta x)) ->
  lc_tm_at K k (instantiate_tm theta t).
Proof.
  intros K k t theta HT; induction HT; intros Htheta; simpl;
    eauto using lc_tm_at.
  eapply lc_tm_weaken; [apply Htheta|lia|lia].
Qed.

Definition singleton_candidate (v : tm) (Hv : value v) : binary_candidate :=
  {| candidate_relation := fun v1 v2 => v1 = v /\ v2 = v;
     candidate_values := fun v1 v2 H =>
       match H with conj H1 H2 =>
         conj (eq_ind_r value Hv H1) (eq_ind_r value Hv H2)
       end |}.

Lemma parametric_identity_reduction : forall t U v,
  wf_ty [] U -> value v ->
  expression_relation [] (fun _ => None)
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) t t ->
  tm_app (tm_tapp t U) v -->* v.
Proof.
  intros t U v HU Hv Ht.
  pose (a := singleton_candidate v Hv).
  assert (Harg : expression_relation [a] (fun _ => None)
     (Ty_BVar 0) v v).
  { apply expression_value; simpl; split; reflexivity. }
  pose proof (expression_type_application [] (fun _ => None)
    (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0)) t t U U a Ht
    (wf_ty_closed _ _ HU) (wf_ty_closed _ _ HU)) as Hfun.
  pose proof (expression_application [a] (fun _ => None)
    (Ty_BVar 0) (Ty_BVar 0) (tm_tapp t U) (tm_tapp t U) v v
    Hfun Harg) as Hresult.
  destruct Hresult as [_ [_ [res1 [res2 [Heval [_ Hrelated]]]]]].
  change (candidate_relation a res1 res2) in Hrelated.
  destruct Hrelated as [-> _].
  apply evaluates_multi; exact Heval.
Qed.

Fixpoint ty_atoms (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow A B => ty_atoms A ++ ty_atoms B
  | Ty_All A => ty_atoms A
  | Ty_Bool | Ty_Nat => []
  end.

Fixpoint tm_atoms (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs _ b => tm_atoms b
  | tm_app f a => tm_atoms f ++ tm_atoms a
  | tm_tabs b => tm_atoms b
  | tm_tapp f _ => tm_atoms f
  | tm_true | tm_false | tm_zero => []
  | tm_if c l r => tm_atoms c ++ tm_atoms l ++ tm_atoms r
  | tm_succ n => tm_atoms n
  | tm_natrec n b s => tm_atoms n ++ tm_atoms b ++ tm_atoms s
  | tm_choice l r => tm_atoms l ++ tm_atoms r
  end.

Fixpoint tm_type_atoms (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_fvar _ | tm_true | tm_false | tm_zero => []
  | tm_abs T b => ty_atoms T ++ tm_type_atoms b
  | tm_app f a => tm_type_atoms f ++ tm_type_atoms a
  | tm_tabs b => tm_type_atoms b
  | tm_tapp f T => tm_type_atoms f ++ ty_atoms T
  | tm_if c l r => tm_type_atoms c ++ tm_type_atoms l ++ tm_type_atoms r
  | tm_succ n => tm_type_atoms n
  | tm_natrec n b s => tm_type_atoms n ++ tm_type_atoms b ++ tm_type_atoms s
  | tm_choice l r => tm_type_atoms l ++ tm_type_atoms r
  end.

Lemma open_ty_rec_closed_id : forall K T U,
  lc_ty_at K T -> open_ty_rec K U T = T.
Proof.
  intros K T U H; induction H; simpl;
    try (f_equal; auto; fail); auto.
  destruct (Nat.eqb k i) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
Qed.

Lemma open_tm_rec_closed_id : forall K k t u,
  lc_tm_at K k t -> open_tm_rec k u t = t.
Proof.
  intros K k t u H; induction H; simpl;
    try (f_equal; auto; fail); auto.
  destruct (Nat.eqb k i) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
Qed.

Lemma open_tm_ty_rec_closed_id : forall K k t U,
  lc_tm_at K k t -> open_tm_ty_rec K U t = t.
Proof.
  intros K k t U H; induction H; simpl;
    try (f_equal; auto using open_ty_rec_closed_id; fail); auto.
Qed.

Lemma instantiate_ty_open : forall T sigma k U,
  (forall X, locally_closed_ty (sigma X)) ->
  instantiate_ty sigma (open_ty_rec k U T) =
    open_ty_rec k (instantiate_ty sigma U) (instantiate_ty sigma T).
Proof.
  induction T; intros sigma k U Hsigma; simpl; try (f_equal; eauto).
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry; eapply open_ty_rec_closed_id.
    eapply lc_ty_weaken; [apply Hsigma|lia].
Qed.

Lemma not_in_app : forall (x : atom) left right,
  ~ In x (left ++ right) -> ~ In x left /\ ~ In x right.
Proof.
  intros x left right H; rewrite in_app_iff in H; tauto.
Qed.

Lemma instantiate_ty_update_open : forall T sigma k X U,
  ~ In X (ty_atoms T) ->
  (forall Y, locally_closed_ty (sigma Y)) ->
  instantiate_ty (atom_update sigma X U)
    (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k U (instantiate_ty sigma T).
Proof.
  induction T; intros sigma k X U Hfresh Hsigma; simpl in *;
    try (f_equal; eauto; fail).
  - destruct (Nat.eqb k n); simpl; [unfold atom_update; rewrite Nat.eqb_refl|]; reflexivity.
  - assert (X <> a) by (intro E; subst; apply Hfresh; auto).
    unfold atom_update; apply Nat.eqb_neq in H.
    rewrite H; symmetry; eapply open_ty_rec_closed_id.
    eapply lc_ty_weaken; [apply Hsigma|lia].
  - apply not_in_app in Hfresh as [Hleft Hright].
    rewrite IHT1 by assumption; rewrite IHT2 by assumption; reflexivity.
Qed.

Lemma instantiate_tm_ty_update_open : forall t sigma K X U,
  ~ In X (tm_type_atoms t) ->
  (forall Y, locally_closed_ty (sigma Y)) ->
  instantiate_tm_ty (atom_update sigma X U)
    (open_tm_ty_rec K (Ty_FVar X) t) =
  open_tm_ty_rec K U (instantiate_tm_ty sigma t).
Proof.
  induction t; intros sigma K X U Hfresh Hsigma; simpl in *;
    try (f_equal; eauto; fail).
  - apply not_in_app in Hfresh as [HT Hbody].
    rewrite (instantiate_ty_update_open _ _ _ _ _ HT Hsigma).
    rewrite (IHt _ _ _ _ Hbody Hsigma); reflexivity.
  - apply not_in_app in Hfresh as [Hf Ha].
    rewrite (IHt1 _ _ _ _ Hf Hsigma).
    rewrite (IHt2 _ _ _ _ Ha Hsigma); reflexivity.
  - apply not_in_app in Hfresh as [Hf HT].
    rewrite (IHt _ _ _ _ Hf Hsigma).
    rewrite (instantiate_ty_update_open _ _ _ _ _ HT Hsigma); reflexivity.
  - repeat rewrite in_app_iff in Hfresh.
    assert (~ In X (tm_type_atoms t1) /\
      ~ In X (tm_type_atoms t2) /\ ~ In X (tm_type_atoms t3)) as [H1 [H2 H3]] by tauto.
    rewrite (IHt1 _ _ _ _ H1 Hsigma),
      (IHt2 _ _ _ _ H2 Hsigma), (IHt3 _ _ _ _ H3 Hsigma); reflexivity.
  - repeat rewrite in_app_iff in Hfresh.
    assert (~ In X (tm_type_atoms t1) /\
      ~ In X (tm_type_atoms t2) /\ ~ In X (tm_type_atoms t3)) as [H1 [H2 H3]] by tauto.
    rewrite (IHt1 _ _ _ _ H1 Hsigma),
      (IHt2 _ _ _ _ H2 Hsigma), (IHt3 _ _ _ _ H3 Hsigma); reflexivity.
  - apply not_in_app in Hfresh as [Hleft Hright].
    rewrite (IHt1 _ _ _ _ Hleft Hsigma),
      (IHt2 _ _ _ _ Hright Hsigma); reflexivity.
Qed.

Lemma instantiate_tm_ty_term_open : forall t sigma k x,
  instantiate_tm_ty sigma (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k (tm_fvar x) (instantiate_tm_ty sigma t).
Proof.
  induction t; intros sigma k x; simpl;
    try (f_equal; eauto; fail); auto.
  destruct (Nat.eqb k n); reflexivity.
Qed.

Lemma instantiate_tm_type_open : forall t theta K U,
  (forall x, locally_closed_tm (theta x)) ->
  instantiate_tm theta (open_tm_ty_rec K U t) =
  open_tm_ty_rec K U (instantiate_tm theta t).
Proof.
  induction t; intros theta K U Htheta; simpl;
    try (f_equal; eauto; fail); auto.
  symmetry; apply (open_tm_ty_rec_closed_id K 0).
  eapply lc_tm_weaken; [apply Htheta|lia|lia].
Qed.

Lemma instantiate_tm_update_open : forall t theta k x u,
  ~ In x (tm_atoms t) ->
  (forall y, locally_closed_tm (theta y)) ->
  instantiate_tm (atom_update theta x u)
    (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k u (instantiate_tm theta t).
Proof.
  induction t; intros theta k x u Hfresh Htheta; simpl in *;
    try (f_equal; eauto; fail).
  - destruct (Nat.eqb k n); simpl;
      [unfold atom_update; rewrite Nat.eqb_refl|]; reflexivity.
  - assert (x <> a) by (intro E; subst; apply Hfresh; auto).
    unfold atom_update; apply Nat.eqb_neq in H.
    rewrite H; symmetry; apply (open_tm_rec_closed_id 0 k).
    eapply lc_tm_weaken; [apply Htheta|lia|lia].
  - apply not_in_app in Hfresh as [Hleft Hright].
    rewrite (IHt1 _ _ _ _ Hleft Htheta),
      (IHt2 _ _ _ _ Hright Htheta); reflexivity.
  - repeat rewrite in_app_iff in Hfresh.
    assert (~ In x (tm_atoms t1) /\
      ~ In x (tm_atoms t2) /\ ~ In x (tm_atoms t3)) as [H1 [H2 H3]] by tauto.
    rewrite (IHt1 _ _ _ _ H1 Htheta),
      (IHt2 _ _ _ _ H2 Htheta), (IHt3 _ _ _ _ H3 Htheta); reflexivity.
  - repeat rewrite in_app_iff in Hfresh.
    assert (~ In x (tm_atoms t1) /\
      ~ In x (tm_atoms t2) /\ ~ In x (tm_atoms t3)) as [H1 [H2 H3]] by tauto.
    rewrite (IHt1 _ _ _ _ H1 Htheta),
      (IHt2 _ _ _ _ H2 Htheta), (IHt3 _ _ _ _ H3 Htheta); reflexivity.
  - apply not_in_app in Hfresh as [Hleft Hright].
    rewrite (IHt1 _ _ _ _ Hleft Htheta),
      (IHt2 _ _ _ _ Hright Htheta); reflexivity.
Qed.

Lemma lifting_equiv : forall R S t1 t2,
  (forall v1 v2, R v1 v2 <-> S v1 v2) ->
  (expression_lifting R t1 t2 <-> expression_lifting S t1 t2).
Proof.
  unfold expression_lifting, results_match.
  intros R S t1 t2 H; split; intros [Ht1 [Ht2 [v1 [v2 [E1 [E2 Hr]]]]]];
    repeat split; try assumption; exists v1, v2; repeat split; try assumption;
    apply H; assumption.
Qed.

Lemma relation_rho_update_fresh : forall T X eta rho candidate v1 v2,
  ~ In X (ty_atoms T) ->
  (value_relation eta (relation_update rho X candidate) T v1 v2 <->
   value_relation eta rho T v1 v2).
Proof.
  induction T; intros X eta rho candidate v1 v2 Hfresh; simpl in *; try tauto.
  - unfold relation_update.
    assert (X <> a) by (intro E; subst; apply Hfresh; auto).
    apply Nat.eqb_neq in H; rewrite H; tauto.
  - apply not_in_app in Hfresh as [H1 H2].
    split.
    + intros [Hv1 [Hv2 [U1 [body1 [U2 [body2 [E1 [E2 Hbody]]]]]]]].
      split; [exact Hv1|]; split; [exact Hv2|].
      exists U1, body1, U2, body2.
      split; [exact E1|]; split; [exact E2|].
      intros left_arg right_arg Harg.
      apply (lifting_equiv (value_relation eta (relation_update rho X candidate) T2)
        (value_relation eta rho T2)); [intros; apply IHT2; exact H2|].
      apply Hbody; apply (IHT1 X eta rho candidate); auto.
    + intros [Hv1 [Hv2 [U1 [body1 [U2 [body2 [E1 [E2 Hbody]]]]]]]].
      split; [exact Hv1|]; split; [exact Hv2|].
      exists U1, body1, U2, body2.
      split; [exact E1|]; split; [exact E2|].
      intros left_arg right_arg Harg.
      apply (lifting_equiv (value_relation eta (relation_update rho X candidate) T2)
        (value_relation eta rho T2)); [intros; apply IHT2; exact H2|].
      apply Hbody; apply (IHT1 X eta rho candidate); auto.
  - split.
    + intros [Hv1 [Hv2 [body1 [body2 [E1 [E2 Hbody]]]]]].
      split; [exact Hv1|]; split; [exact Hv2|].
      exists body1, body2; split; [exact E1|]; split; [exact E2|].
      intros U1 U2 inner_candidate HU1 HU2.
      apply (lifting_equiv (value_relation (inner_candidate :: eta)
        (relation_update rho X candidate) T)
        (value_relation (inner_candidate :: eta) rho T));
        [intros; apply IHT; exact Hfresh|].
      eapply Hbody; eauto.
    + intros [Hv1 [Hv2 [body1 [body2 [E1 [E2 Hbody]]]]]].
      split; [exact Hv1|]; split; [exact Hv2|].
      exists body1, body2; split; [exact E1|]; split; [exact E2|].
      intros U1 U2 inner_candidate HU1 HU2.
      apply (lifting_equiv (value_relation (inner_candidate :: eta)
        (relation_update rho X candidate) T)
        (value_relation (inner_candidate :: eta) rho T));
        [intros; apply IHT; exact Hfresh|].
      eapply Hbody; eauto.
Qed.

Lemma relation_eta_prefix : forall K T,
  lc_ty_at K T -> forall eta1 eta2 rho v1 v2,
  firstn K eta1 = firstn K eta2 ->
  (value_relation eta1 rho T v1 v2 <->
   value_relation eta2 rho T v1 v2).
Proof.
  intros K T HT; induction HT; intros eta1 eta2 rho v1 v2 Hprefix;
    simpl; try tauto.
  - assert (nth_error eta1 i = nth_error eta2 i) as Heq.
    { pose proof (nth_error_firstn k eta1 i) as H1.
      pose proof (nth_error_firstn k eta2 i) as H2.
      assert (i <? k = true) as Hi by (apply Nat.ltb_lt; lia).
      rewrite Hi in H1, H2.
      rewrite <- H1, <- H2; exact (f_equal (fun xs => nth_error xs i) Hprefix). }
    now rewrite Heq.
  - split.
    + intros [Hv1 [Hv2 [U1 [body1 [U2 [body2 [E1 [E2 Hbody]]]]]]]].
      split; [exact Hv1|]; split; [exact Hv2|].
      exists U1, body1, U2, body2.
      split; [exact E1|]; split; [exact E2|].
      intros arg1 arg2 Harg.
      apply (lifting_equiv (value_relation eta1 rho T2)
        (value_relation eta2 rho T2)); [intros; apply IHHT2; exact Hprefix|].
      apply Hbody; apply (IHHT1 eta1 eta2 rho); auto.
    + intros [Hv1 [Hv2 [U1 [body1 [U2 [body2 [E1 [E2 Hbody]]]]]]]].
      split; [exact Hv1|]; split; [exact Hv2|].
      exists U1, body1, U2, body2.
      split; [exact E1|]; split; [exact E2|].
      intros arg1 arg2 Harg.
      apply (lifting_equiv (value_relation eta1 rho T2)
        (value_relation eta2 rho T2)); [intros; apply IHHT2; exact Hprefix|].
      apply Hbody; apply (IHHT1 eta1 eta2 rho); auto.
  - split.
    + intros [Hv1 [Hv2 [body1 [body2 [E1 [E2 Hbody]]]]]].
      split; [exact Hv1|]; split; [exact Hv2|].
      exists body1, body2; split; [exact E1|]; split; [exact E2|].
      intros U1 U2 candidate HU1 HU2.
      apply (lifting_equiv (value_relation (candidate :: eta1) rho T)
        (value_relation (candidate :: eta2) rho T));
        [intros; apply IHHT; simpl; now rewrite Hprefix|].
      eapply Hbody; eauto.
    + intros [Hv1 [Hv2 [body1 [body2 [E1 [E2 Hbody]]]]]].
      split; [exact Hv1|]; split; [exact Hv2|].
      exists body1, body2; split; [exact E1|]; split; [exact E2|].
      intros U1 U2 candidate HU1 HU2.
      apply (lifting_equiv (value_relation (candidate :: eta1) rho T)
        (value_relation (candidate :: eta2) rho T));
        [intros; apply IHHT; simpl; now rewrite Hprefix|].
      eapply Hbody; eauto.
Qed.

Lemma relation_open_prefix : forall T K prefix eta rho U candidate v1 v2,
  lc_ty_at (S K) T -> length prefix = K -> locally_closed_ty U ->
  (forall left right,
    candidate_relation candidate left right <->
    value_relation (prefix ++ eta) rho U left right) ->
  (value_relation (prefix ++ candidate :: eta) rho T v1 v2 <->
   value_relation (prefix ++ eta) rho (open_ty_rec K U T) v1 v2).
Proof.
  induction T; intros K prefix eta rho U candidate v1 v2 HT Hlen HU Hcandidate;
    simpl in *; try tauto.
  - inversion HT.
    destruct (Nat.lt_ge_cases n K) as [Hlt|Hge].
    + destruct (Nat.eqb K n) eqn:E; [apply Nat.eqb_eq in E; lia|].
      rewrite nth_error_app1 by lia; simpl;
        rewrite nth_error_app1 by lia; tauto.
    + assert (n = K) by lia; subst.
      rewrite Nat.eqb_refl.
      rewrite nth_error_app2 by lia.
      rewrite Nat.sub_diag; simpl; apply Hcandidate.
  - inversion HT.
    split.
    + intros [Hv1 [Hv2 [U1 [body1 [U2 [body2 [E1 [E2 Hbody]]]]]]]].
      split; [exact Hv1|]; split; [exact Hv2|].
      exists U1, body1, U2, body2.
      split; [exact E1|]; split; [exact E2|].
      intros arg1 arg2 Harg.
      apply (lifting_equiv
        (value_relation (prefix ++ candidate :: eta) rho T2)
        (value_relation (prefix ++ eta) rho (open_ty_rec K U T2)));
        [intros; eapply IHT2; eauto|].
      apply Hbody; apply (IHT1 K prefix eta rho U candidate); eauto.
    + intros [Hv1 [Hv2 [U1 [body1 [U2 [body2 [E1 [E2 Hbody]]]]]]]].
      split; [exact Hv1|]; split; [exact Hv2|].
      exists U1, body1, U2, body2.
      split; [exact E1|]; split; [exact E2|].
      intros arg1 arg2 Harg.
      apply (lifting_equiv
        (value_relation (prefix ++ candidate :: eta) rho T2)
        (value_relation (prefix ++ eta) rho (open_ty_rec K U T2)));
        [intros; eapply IHT2; eauto|].
      apply Hbody; apply (IHT1 K prefix eta rho U candidate); eauto.
  - inversion HT.
    split.
    + intros [Hv1 [Hv2 [body1 [body2 [E1 [E2 Hbody]]]]]].
      split; [exact Hv1|]; split; [exact Hv2|].
      exists body1, body2; split; [exact E1|]; split; [exact E2|].
      intros U1 U2 inner_candidate HU1 HU2.
      apply (lifting_equiv
        (value_relation (inner_candidate :: prefix ++ candidate :: eta) rho T)
        (value_relation (inner_candidate :: prefix ++ eta) rho
          (open_ty_rec (S K) U T)));
        [intros out1 out2;
          apply (IHT (S K) (inner_candidate :: prefix) eta rho U candidate out1 out2);
          [exact H1|simpl; lia|exact HU|]|].
      * intros left right; rewrite Hcandidate.
        symmetry; apply (relation_eta_prefix 0 U HU); reflexivity.
      * eapply Hbody; eauto.
    + intros [Hv1 [Hv2 [body1 [body2 [E1 [E2 Hbody]]]]]].
      split; [exact Hv1|]; split; [exact Hv2|].
      exists body1, body2; split; [exact E1|]; split; [exact E2|].
      intros U1 U2 inner_candidate HU1 HU2.
      apply (lifting_equiv
        (value_relation (inner_candidate :: prefix ++ candidate :: eta) rho T)
        (value_relation (inner_candidate :: prefix ++ eta) rho
          (open_ty_rec (S K) U T)));
        [intros out1 out2;
          apply (IHT (S K) (inner_candidate :: prefix) eta rho U candidate out1 out2);
          [exact H1|simpl; lia|exact HU|]|].
      * intros left right; rewrite Hcandidate.
        symmetry; apply (relation_eta_prefix 0 U HU); reflexivity.
      * eapply Hbody; eauto.
Qed.

Definition semantic_candidate (rho : binary_env) (U : ty) : binary_candidate :=
  {| candidate_relation := value_relation [] rho U;
     candidate_values := relation_values [] rho U |}.

Lemma relation_open_inst : forall T U rho v1 v2,
  lc_ty_at 1 T -> locally_closed_ty U ->
  (value_relation [semantic_candidate rho U] rho T v1 v2 <->
   value_relation [] rho (open_ty T U) v1 v2).
Proof.
  intros T U rho v1 v2 HT HU.
  apply (relation_open_prefix T 0 [] [] rho U (semantic_candidate rho U));
    auto; intros; reflexivity.
Qed.

Lemma relation_open_fvar : forall T X rho candidate v1 v2,
  lc_ty_at 1 T -> ~ In X (ty_atoms T) ->
  (value_relation [candidate] rho T v1 v2 <->
   value_relation [] (relation_update rho X candidate)
     (open_ty T (Ty_FVar X)) v1 v2).
Proof.
  intros T X rho candidate v1 v2 HT Hfresh.
  transitivity (value_relation [candidate]
    (relation_update rho X candidate) T v1 v2).
  - symmetry; apply relation_rho_update_fresh; exact Hfresh.
  - apply (relation_open_prefix T 0 [] [] (relation_update rho X candidate)
      (Ty_FVar X) candidate); auto.
    + unfold locally_closed_ty; constructor.
    + intros left right; simpl; unfold relation_update.
      now rewrite Nat.eqb_refl.
Qed.

Lemma typing_type_closed : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_ty T.
Proof.
  induction 1; unfold locally_closed_ty in *;
    eauto using wf_ty_closed, lc_ty_at.
  - eapply wf_ty_closed; eassumption.
  - apply lc_ty_arrow; [eapply wf_ty_closed; eauto|].
    destruct (fresh_atom_exists L) as [x Hx]; eauto.
  - inversion IHhas_type1; assumption.
  - apply lc_ty_all.
    destruct (fresh_atom_exists L) as [X HX].
    apply open_ty_fvar_closes with (X := X).
    eapply H0; eauto.
  - inversion IHhas_type; subst.
    eapply open_ty_preserves; [eassumption|exact (wf_ty_closed _ _ H0)].
Qed.

Fixpoint context_ty_atoms (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (_, T) :: rest => ty_atoms T ++ context_ty_atoms rest
  end.

Lemma lookup_context_type_atoms : forall Gamma x T X,
  lookup_context x Gamma = Some T -> In X (ty_atoms T) ->
  In X (context_ty_atoms Gamma).
Proof.
  induction Gamma as [|[y A] rest IH]; intros x T X Hlookup Hin;
    simpl in *; try discriminate.
  destruct (Nat.eqb x y) eqn:E.
  - inversion Hlookup; subst; apply in_or_app; left; assumption.
  - apply in_or_app; right; eapply IH; eassumption.
Qed.

Lemma tm_atoms_instantiate_tm_ty : forall sigma t,
  tm_atoms (instantiate_tm_ty sigma t) = tm_atoms t.
Proof.
  intros sigma t; induction t; simpl; try (rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3); reflexivity.
Qed.

Definition semantic_environment (Gamma : context) (rho : binary_env)
    (sigma1 sigma2 : atom -> ty) (theta1 theta2 : atom -> tm) : Prop :=
  (forall X, locally_closed_ty (sigma1 X)) /\
  (forall X, locally_closed_ty (sigma2 X)) /\
  (forall x, locally_closed_tm (theta1 x)) /\
  (forall x, locally_closed_tm (theta2 x)) /\
  (forall x T, lookup_context x Gamma = Some T ->
     value_relation [] rho T (theta1 x) (theta2 x)).

Lemma semantic_environment_term_extend : forall Gamma rho sigma1 sigma2 theta1 theta2 x T v1 v2,
  semantic_environment Gamma rho sigma1 sigma2 theta1 theta2 ->
  value_relation [] rho T v1 v2 ->
  semantic_environment (update Gamma x T) rho sigma1 sigma2
    (atom_update theta1 x v1) (atom_update theta2 x v2).
Proof.
  intros Gamma rho sigma1 sigma2 theta1 theta2 x T v1 v2
    [Hs1 [Hs2 [Ht1 [Ht2 Henv]]]] Hr.
  destruct (relation_values _ _ _ _ _ Hr) as [Hv1 Hv2].
  repeat split; try assumption.
  - intros y; unfold atom_update; destruct (Nat.eqb x y);
      eauto using value_closed.
  - intros y; unfold atom_update; destruct (Nat.eqb x y);
      eauto using value_closed.
  - intros y A Hlookup; simpl in Hlookup.
    unfold atom_update.
    rewrite Nat.eqb_sym in Hlookup.
    destruct (Nat.eqb x y) eqn:E.
    + inversion Hlookup; subst; exact Hr.
    + eapply Henv; exact Hlookup.
Qed.

Lemma semantic_environment_type_extend : forall Gamma rho sigma1 sigma2 theta1 theta2 X U1 U2 candidate,
  ~ In X (context_ty_atoms Gamma) ->
  locally_closed_ty U1 -> locally_closed_ty U2 ->
  semantic_environment Gamma rho sigma1 sigma2 theta1 theta2 ->
  semantic_environment Gamma (relation_update rho X candidate)
    (atom_update sigma1 X U1) (atom_update sigma2 X U2) theta1 theta2.
Proof.
  intros Gamma rho sigma1 sigma2 theta1 theta2 X U1 U2 candidate
    Hfresh HU1 HU2 [Hs1 [Hs2 [Ht1 [Ht2 Henv]]]].
  repeat split; try assumption.
  - intros Y; unfold atom_update; destruct (Nat.eqb X Y); auto.
  - intros Y; unfold atom_update; destruct (Nat.eqb X Y); auto.
  - intros x T Hlookup.
    apply (relation_rho_update_fresh T X [] rho candidate).
    + intro Hin; apply Hfresh; eapply lookup_context_type_atoms; eauto.
    + eapply Henv; eauto.
Qed.

Lemma semantic_term_closed : forall t sigma theta,
  locally_closed_tm t ->
  (forall X, locally_closed_ty (sigma X)) ->
  (forall x, locally_closed_tm (theta x)) ->
  locally_closed_tm (instantiate_tm theta (instantiate_tm_ty sigma t)).
Proof.
  intros t sigma theta Ht Hsigma Htheta.
  eapply instantiate_tm_closed; [eapply instantiate_tm_ty_closed;
    [exact Ht|exact Hsigma]|exact Htheta].
Qed.

Theorem fundamental_relation : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall rho sigma1 sigma2 theta1 theta2,
    semantic_environment Gamma rho sigma1 sigma2 theta1 theta2 ->
    expression_relation [] rho T
      (instantiate_tm theta1 (instantiate_tm_ty sigma1 t))
      (instantiate_tm theta2 (instantiate_tm_ty sigma2 t)).
Proof.
  induction 1; intros rho sigma1 sigma2 theta1 theta2 Henv; simpl.
  - destruct Henv as [_ [_ [_ [_ Hrel]]]].
    apply expression_value; eapply Hrel; eauto.
  - destruct Henv as [Hs1 [Hs2 [Ht1 [Ht2 Hrel]]]].
    assert (Hwhole : semantic_environment Gamma rho sigma1 sigma2 theta1 theta2).
    { repeat split; assumption. }
    assert (Htyped : has_type Delta Gamma (tm_abs T1 t2) (Ty_Arrow T1 T2)).
    { eapply T_Abs; eauto. }
    pose proof (typing_closed _ _ _ _ Htyped) as Hclosed.
    pose proof (semantic_term_closed _ _ _ Hclosed Hs1 Ht1) as Hclosed1.
    pose proof (semantic_term_closed _ _ _ Hclosed Hs2 Ht2) as Hclosed2.
    apply expression_value; simpl.
    split; [constructor; exact Hclosed1|].
    split; [constructor; exact Hclosed2|].
    exists (instantiate_ty sigma1 T1),
      (instantiate_tm theta1 (instantiate_tm_ty sigma1 t2)),
      (instantiate_ty sigma2 T1),
      (instantiate_tm theta2 (instantiate_tm_ty sigma2 t2)).
    split; [reflexivity|]; split; [reflexivity|].
    intros arg1 arg2 Harg.
    destruct (fresh_atom_exists (L ++ tm_atoms t2)) as [x Hfresh].
    apply not_in_app in Hfresh as [HxL Hxt].
    pose proof (H1 x HxL rho sigma1 sigma2
      (atom_update theta1 x arg1) (atom_update theta2 x arg2)
      (semantic_environment_term_extend _ _ _ _ _ _ _ _ _ _
        Hwhole Harg)) as Hbody.
    unfold open_tm in Hbody.
    rewrite (instantiate_tm_ty_term_open t2 sigma1 0 x) in Hbody.
    rewrite (instantiate_tm_ty_term_open t2 sigma2 0 x) in Hbody.
    rewrite (instantiate_tm_update_open (instantiate_tm_ty sigma1 t2)
      theta1 0 x arg1) in Hbody;
      [|rewrite tm_atoms_instantiate_tm_ty; exact Hxt|exact Ht1].
    rewrite (instantiate_tm_update_open (instantiate_tm_ty sigma2 t2)
      theta2 0 x arg2) in Hbody;
      [|rewrite tm_atoms_instantiate_tm_ty; exact Hxt|exact Ht2].
    exact Hbody.
  - eapply expression_application; eauto.
  - destruct Henv as [Hs1 [Hs2 [Ht1 [Ht2 Hrel]]]].
    assert (Hwhole : semantic_environment Gamma rho sigma1 sigma2 theta1 theta2).
    { repeat split; assumption. }
    assert (Htyped : has_type Delta Gamma (tm_tabs t) (Ty_All T)).
    { eapply T_TAbs; eauto. }
    pose proof (typing_closed _ _ _ _ Htyped) as Hclosed.
    pose proof (typing_type_closed _ _ _ _ Htyped) as Hty.
    assert (Hscope : lc_ty_at 1 T) by (inversion Hty; assumption).
    pose proof (semantic_term_closed _ _ _ Hclosed Hs1 Ht1) as Hclosed1.
    pose proof (semantic_term_closed _ _ _ Hclosed Hs2 Ht2) as Hclosed2.
    apply expression_value; simpl.
    split; [constructor; exact Hclosed1|].
    split; [constructor; exact Hclosed2|].
    exists (instantiate_tm theta1 (instantiate_tm_ty sigma1 t)),
      (instantiate_tm theta2 (instantiate_tm_ty sigma2 t)).
    split; [reflexivity|]; split; [reflexivity|].
    intros U1 U2 inner_candidate HU1 HU2.
    destruct (fresh_atom_exists (L ++ tm_type_atoms t ++
      ty_atoms T ++ context_ty_atoms Gamma)) as [X Hfresh].
    repeat rewrite in_app_iff in Hfresh.
    assert (~ In X L /\ ~ In X (tm_type_atoms t) /\
      ~ In X (ty_atoms T) /\ ~ In X (context_ty_atoms Gamma))
      as [HxL [Hxt [HxT HxG]]] by tauto.
    pose proof (H0 X HxL (relation_update rho X inner_candidate)
      (atom_update sigma1 X U1) (atom_update sigma2 X U2)
      theta1 theta2
      (semantic_environment_type_extend _ _ _ _ _ _ _ _ _ _
        HxG HU1 HU2 Hwhole)) as Hbody.
    unfold open_tm_ty in Hbody.
    rewrite (instantiate_tm_ty_update_open t sigma1 0 X U1 Hxt Hs1) in Hbody.
    rewrite (instantiate_tm_ty_update_open t sigma2 0 X U2 Hxt Hs2) in Hbody.
    rewrite (instantiate_tm_type_open (instantiate_tm_ty sigma1 t)
      theta1 0 U1 Ht1) in Hbody.
    rewrite (instantiate_tm_type_open (instantiate_tm_ty sigma2 t)
      theta2 0 U2 Ht2) in Hbody.
    apply (lifting_equiv
      (value_relation [] (relation_update rho X inner_candidate)
        (open_ty T (Ty_FVar X)))
      (value_relation [inner_candidate] rho T)).
    + intros left right; symmetry; apply relation_open_fvar; assumption.
    + exact Hbody.
  - destruct Henv as [Hs1 [Hs2 [Ht1 [Ht2 Hrel]]]].
    assert (Hwhole : semantic_environment Gamma rho sigma1 sigma2 theta1 theta2).
    { repeat split; assumption. }
    assert (Hscope : lc_ty_at 1 T).
    { pose proof (typing_type_closed _ _ _ _ H) as Hty.
      inversion Hty; assumption. }
    assert (HU : locally_closed_ty U) by (eapply wf_ty_closed; eauto).
    assert (HU1 : locally_closed_ty (instantiate_ty sigma1 U)).
    { eapply instantiate_ty_closed; eauto. }
    assert (HU2 : locally_closed_ty (instantiate_ty sigma2 U)).
    { eapply instantiate_ty_closed; eauto. }
    pose proof (expression_type_application [] rho T
      (instantiate_tm theta1 (instantiate_tm_ty sigma1 t))
      (instantiate_tm theta2 (instantiate_tm_ty sigma2 t))
      (instantiate_ty sigma1 U) (instantiate_ty sigma2 U)
      (semantic_candidate rho U)
      (IHhas_type rho sigma1 sigma2 theta1 theta2 Hwhole) HU1 HU2)
      as Hbody.
    apply (lifting_equiv
      (value_relation [semantic_candidate rho U] rho T)
      (value_relation [] rho (open_ty T U))).
    + intros left right; apply relation_open_inst; assumption.
    + exact Hbody.
  - apply expression_true.
  - apply expression_false.
  - eapply expression_if; eauto.
  - apply expression_zero.
  - apply expression_succ; eauto.
  - eapply expression_rec; eauto.
  - eapply expression_choice; eauto.
Qed.

Lemma instantiate_ty_identity : forall T,
  instantiate_ty Ty_FVar T = T.
Proof.
  induction T; simpl; f_equal; auto.
Qed.

Lemma instantiate_tm_ty_identity : forall t,
  instantiate_tm_ty Ty_FVar t = t.
Proof.
  induction t; simpl;
    try (rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3,
      ?instantiate_ty_identity); reflexivity.
Qed.

Lemma instantiate_tm_identity : forall t,
  instantiate_tm tm_fvar t = t.
Proof.
  induction t; simpl;
    try (rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3); reflexivity.
Qed.

Lemma empty_semantic_environment :
  semantic_environment empty (fun _ => None) Ty_FVar Ty_FVar
    tm_fvar tm_fvar.
Proof.
  repeat split.
  - intros X; unfold locally_closed_ty; constructor.
  - intros X; unfold locally_closed_ty; constructor.
  - intros x; unfold locally_closed_tm; constructor.
  - intros x; unfold locally_closed_tm; constructor.
  - intros x T Hlookup; discriminate.
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
  intros t Htyped U v HU Hv Hvalue.
  apply parametric_identity_reduction; try assumption.
  pose proof (fundamental_relation [] empty t
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) Htyped
    (fun _ => None) Ty_FVar Ty_FVar tm_fvar tm_fvar
    empty_semantic_environment) as Hfund.
  repeat rewrite instantiate_tm_ty_identity in Hfund.
  repeat rewrite instantiate_tm_identity in Hfund.
  exact Hfund.
Qed.

End SystemFParametricityIfNondeterminismRecursionMediumTask.
