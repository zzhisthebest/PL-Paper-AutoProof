(** System F parametricity benchmark, Medium variant.
    Features: if-recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFParametricityIfRecursionMediumTask.

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
      has_type Delta Gamma (tm_natrec n b s) T.

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
      evaluates (tm_natrec n b s) result.

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

Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof.
  intros v Hv. unfold locally_closed_tm. destruct Hv as [T t Hlc | t Hlc | | | n Hn].
  - exact Hlc.
  - exact Hlc.
  - constructor.
  - constructor.
  - induction Hn as [| n Hn IH].
    + constructor.
    + constructor. exact IH.
Qed.

Fixpoint tm_env_subst (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_abs T t1 => tm_abs T (tm_env_subst sigma t1)
  | tm_app t1 t2 => tm_app (tm_env_subst sigma t1) (tm_env_subst sigma t2)
  | tm_tabs t1 => tm_tabs (tm_env_subst sigma t1)
  | tm_tapp t1 T => tm_tapp (tm_env_subst sigma t1) T
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (tm_env_subst sigma t1) (tm_env_subst sigma t2) (tm_env_subst sigma t3)
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (tm_env_subst sigma t1)
  | tm_natrec n b s => tm_natrec (tm_env_subst sigma n) (tm_env_subst sigma b) (tm_env_subst sigma s)
  end.

Definition tm_env_update (sigma : atom -> tm) (x : atom) (u : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then u else sigma y.

Lemma open_tm_rec_above : forall K q k t u,
  lc_tm_at K q t -> q <= k -> open_tm_rec k u t = t.
Proof.
  intros K q k t u. revert K q k u.
  induction t as [i|x|T t IH|t1 IH1 t2 IH2|t IH|t1 IH| | |
    t1 IH1 t2 IH2 t3 IH3| |t IH|n IH1 b IH2 s IH3];
    intros K q k u Ht Hq; inversion Ht; subst; simpl.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. lia.
    + reflexivity.
  - reflexivity.
  - f_equal. apply (IH K (S q) (S k) u); [assumption | lia].
  - f_equal.
    + apply (IH1 K q k u); assumption.
    + apply (IH2 K q k u); assumption.
  - f_equal. apply (IH (S K) q k u); assumption.
  - f_equal. apply (IH K q k u); assumption.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply (IH1 K q k u); assumption.
    + apply (IH2 K q k u); assumption.
    + apply (IH3 K q k u); assumption.
  - reflexivity.
  - f_equal. apply (IH K q k u); assumption.
  - f_equal.
    + apply (IH1 K q k u); assumption.
    + apply (IH2 K q k u); assumption.
    + apply (IH3 K q k u); assumption.
Qed.

Lemma open_tm_rec_closed : forall K k t u,
  lc_tm_at K 0 t -> open_tm_rec k u t = t.
Proof.
  intros K k t u H. apply (open_tm_rec_above K 0 k t u); [assumption | lia].
Qed.

Lemma tm_env_subst_open_rec : forall sigma x t k,
  (forall y, locally_closed_tm (sigma y)) ->
  tm_env_subst sigma (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k (sigma x) (tm_env_subst sigma t).
Proof.
  intros sigma x t k Hsig. revert k.
  induction t; intros k; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E. subst. symmetry. apply (open_tm_rec_closed 0 k (sigma a) (sigma a)); apply Hsig.
    + apply Nat.eqb_neq in E. symmetry. apply (open_tm_rec_closed 0 k (sigma a) (sigma x)); apply Hsig.
  - f_equal. apply IHt.
  - f_equal; [apply IHt1 | apply IHt2].
  - f_equal. apply IHt.
  - f_equal. apply IHt.
  - reflexivity.
  - reflexivity.
  - f_equal; eauto.
  - reflexivity.
  - f_equal; eauto.
  - f_equal; eauto.
Qed.

Lemma tm_env_subst_open : forall sigma x t,
  (forall y, locally_closed_tm (sigma y)) ->
  tm_env_subst sigma (open_tm t (tm_fvar x)) =
  open_tm (tm_env_subst sigma t) (sigma x).
Proof.
  intros. unfold open_tm. apply tm_env_subst_open_rec; assumption.
Qed.

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
  end.

Lemma tm_env_subst_agree : forall sigma tau t,
  (forall x, In x (tm_fv t) -> sigma x = tau x) ->
  tm_env_subst sigma t = tm_env_subst tau t.
Proof.
  intros sigma tau t. induction t; simpl; intros H; try reflexivity.
  - apply H. simpl. auto.
  - f_equal. apply IHt. intros; apply H; assumption.
  - f_equal; [apply IHt1 | apply IHt2]; intros; apply H; apply in_or_app; auto.
  - f_equal. apply IHt. intros; apply H; assumption.
  - f_equal. apply IHt. intros; apply H; assumption.
  - f_equal; [apply IHt1 | apply IHt2 | apply IHt3]; intros; apply H; repeat rewrite in_app_iff in *; tauto.
  - f_equal. apply IHt. intros; apply H; assumption.
  - f_equal; [apply IHt1 | apply IHt2 | apply IHt3]; intros; apply H; repeat rewrite in_app_iff in *; tauto.
Qed.

Fixpoint list_max (l : list nat) : nat :=
  match l with [] => 0 | x :: l' => Nat.max x (list_max l') end.

Lemma in_list_max : forall x l, In x l -> x <= list_max l.
Proof.
  intros x l H. induction l as [|a l IH]; simpl in *.
  - contradiction.
  - destruct H as [<- | H]. apply Nat.le_max_l. apply Nat.le_trans with (m := list_max l); auto. apply Nat.le_max_r.
Qed.

Lemma exists_fresh : forall l : list nat, exists x, ~ In x l.
Proof.
  intro l. exists (S (list_max l)). intro H.
  pose proof (in_list_max _ _ H). lia.
Qed.

Definition rho_ok (Delta : ty_context) (rho : binary_env) : Prop :=
  forall X, In X Delta -> exists a, rho X = Some a.

Definition term_env_ok (Delta : ty_context) (Gamma : context)
    (eta : list binary_candidate) (rho : binary_env)
    (sigma1 sigma2 : atom -> tm) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    expression_relation eta rho T (sigma1 x) (sigma2 x) /\
    has_type Delta [] (sigma1 x) T /\ has_type Delta [] (sigma2 x) T.

Lemma term_env_ok_update : forall Delta Gamma eta rho sigma1 sigma2 x T a1 a2,
  term_env_ok Delta Gamma eta rho sigma1 sigma2 ->
  expression_relation eta rho T a1 a2 ->
  has_type Delta [] a1 T -> has_type Delta [] a2 T ->
  term_env_ok Delta (update Gamma x T) eta rho
    (tm_env_update sigma1 x a1) (tm_env_update sigma2 x a2).
Proof.
  intros Delta Gamma eta rho sigma1 sigma2 x T a1 a2 Henv Ha Ht1 Ht2 y U Hlookup.
  unfold update in Hlookup. simpl in Hlookup.
  destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. subst. rewrite Nat.eqb_refl in Hlookup. inversion Hlookup. subst U.
    unfold tm_env_update. rewrite Nat.eqb_refl. exact (conj Ha (conj Ht1 Ht2)).
  - assert (x <> y) as Hxy by (apply Nat.eqb_neq; exact E).
    assert (Nat.eqb y x = false) as Hne by
      (apply Nat.eqb_neq; intro Heq; apply Hxy; symmetry; exact Heq).
    rewrite Hne in Hlookup.
    unfold tm_env_update. rewrite E. apply Henv. assumption.
Qed.

Lemma vr_values : forall eta rho T v1 v2,
  value_relation eta rho T v1 v2 -> value v1 /\ value v2.
Proof.
  intros eta rho T. induction T; simpl; intros v1 v2 H.
  - destruct (nth_error eta n) as [a|] eqn:E; [apply a.(candidate_values); exact H | contradiction].
  - destruct (rho a) as [c|] eqn:E; [apply c.(candidate_values); exact H | contradiction].
  - tauto.
  - tauto.
  - destruct H as [[H1 H2] | [H1 H2]]; subst; split; constructor.
  - destruct H as [<- Hn]. split; apply v_nat; exact Hn.
Qed.

Lemma expr_value : forall eta rho T v1 v2,
  value_relation eta rho T v1 v2 ->
  expression_relation eta rho T v1 v2.
Proof.
  intros eta rho T v1 v2 H. unfold expression_relation, expression_lifting.
  pose proof (vr_values eta rho T v1 v2 H) as [Hv1 Hv2].
  split; [apply value_lc; exact Hv1 |].
  split; [apply value_lc; exact Hv2 |].
  exists v1, v2. split; [constructor; exact Hv1 |].
  split; [constructor; exact Hv2 | exact H].
Qed.

Lemma expr_app : forall eta rho T1 T2 f1 f2 a1 a2,
  expression_relation eta rho (Ty_Arrow T1 T2) f1 f2 ->
  expression_relation eta rho T1 a1 a2 ->
  expression_relation eta rho T2 (tm_app f1 a1) (tm_app f2 a2).
Proof.
  intros eta rho T1 T2 f1 f2 a1 a2 Hf Ha.
  unfold expression_relation, expression_lifting in *.
  destruct Hf as [Hlf1 [Hlf2 [vf1 [vf2 [Ef1 [Ef2 HRf]]]]]].
  destruct Ha as [Hla1 [Hla2 [va1 [va2 [Ea1 [Ea2 HRa]]]]]].
  destruct HRf as [Hfv1 [Hfv2 Hex]].
  destruct Hex as [U1 [b1 [U2 [b2 [Heq1 [Heq2 Hbody]]]]]].
  subst vf1. subst vf2.
  destruct (Hbody va1 va2 HRa) as [Hlb1 [Hlb2 [r1 [r2 [Eb1 [Eb2 HR]]]]]].
  split; [constructor; assumption |].
  split; [constructor; assumption |].
  exists r1, r2. split.
  - apply EvalApp with (f := f1) (arg := a1) (U := U1) (body := b1)
      (v := va1) (result := r1); assumption.
  - split.
    + apply EvalApp with (f := f2) (arg := a2) (U := U2) (body := b2)
        (v := va2) (result := r2); assumption.
    + exact HR.
Qed.

Lemma lc_tm_weaken : forall K k t,
  lc_tm_at K k t -> lc_tm_at K (S k) t.
Proof.
  intros K k t H. induction H; eauto.
Qed.

Lemma lc_ty_weaken : forall K T,
  lc_ty_at K T -> lc_ty_at (S K) T.
Proof.
  intros K T H. induction H; eauto.
Qed.

Lemma lc_tm_ty_weaken : forall K k t,
  lc_tm_at K k t -> lc_tm_at (S K) k t.
Proof.
  intros K k t H. induction H; eauto using lc_ty_weaken.
Qed.

Lemma open_tm_bvar_lc : forall K k i v,
  i < S k -> lc_tm_at K k v ->
  lc_tm_at K k (open_tm_rec k v (tm_bvar i)).
Proof.
  intros K k i v Hi Hv. simpl.
  destruct (Nat.eqb k i) eqn:E.
  - apply Nat.eqb_eq in E. subst. exact Hv.
  - apply lc_tm_bvar.
    apply Nat.eqb_neq in E.
    assert (i <> k) as Hne by (intro Heq; apply E; symmetry; exact Heq).
    apply (proj2 (Nat.le_neq i k)).
    split; [apply (proj1 (Nat.lt_succ_r i k)); exact Hi | exact Hne].
Qed.

Lemma open_tm_rec_lc : forall K k t v,
  lc_tm_at K (S k) t -> lc_tm_at K k v ->
  lc_tm_at K k (open_tm_rec k v t).
Proof.
  intros K k t. revert K k.
  
  induction t; intros K k v Ht Hv; inversion Ht; subst; simpl in *;
    eauto using open_tm_bvar_lc, lc_tm_weaken, lc_tm_ty_weaken.
Qed.

Lemma open_ty_bvar_lc : forall k i U,
  i < S k -> lc_ty_at k U ->
  lc_ty_at k (open_ty_rec k U (Ty_BVar i)).
Proof.
  intros k i U Hi HU. simpl.
  destruct (Nat.eqb k i) eqn:E.
  - apply Nat.eqb_eq in E. subst. exact HU.
  - apply lc_ty_bvar.
    apply Nat.eqb_neq in E.
    assert (i <> k) as Hne by (intro Heq; apply E; symmetry; exact Heq).
    apply (proj2 (Nat.le_neq i k)).
    split; [apply (proj1 (Nat.lt_succ_r i k)); exact Hi | exact Hne].
Qed.

Lemma open_ty_rec_lc : forall k U T,
  lc_ty_at (S k) T -> lc_ty_at k U ->
  lc_ty_at k (open_ty_rec k U T).
Proof.
  intros k U T. revert k U.
  induction T; intros k U Ht HU; inversion Ht; subst; simpl in *;
    eauto using open_ty_bvar_lc, lc_ty_weaken.
Qed.

Lemma open_tm_ty_rec_lc : forall k q U t,
  lc_tm_at (S k) q t -> lc_ty_at k U ->
  lc_tm_at k q (open_tm_ty_rec k U t).
Proof.
  intros k q U t. revert k q U.
  induction t; intros k q U Ht HU; inversion Ht; subst; simpl in *;
    eauto using open_ty_rec_lc, lc_ty_weaken.
Qed.

Lemma open_tm_ty_lc : forall t U,
  locally_closed_tm (tm_tabs t) -> locally_closed_ty U ->
  locally_closed_tm (open_tm_ty t U).
Proof.
  intros t U Ht HU. unfold locally_closed_tm, locally_closed_ty in *.
  apply (open_tm_ty_rec_lc 0 0 U t).
  - inversion Ht. assumption.
  - assumption.
Qed.

Lemma open_tm_lc : forall T t v,
  locally_closed_tm (tm_abs T t) -> value v ->
  locally_closed_tm (open_tm t v).
Proof.
  intros T t v Ht Hv. unfold locally_closed_tm in *.
  apply (open_tm_rec_lc 0 0 t v).
  - inversion Ht; assumption.
  - apply value_lc; assumption.
Qed.

Lemma eval_value : forall t v, evaluates t v -> value v.
Proof.
  intros t v He. induction He; eauto using value, numeric_value.
Qed.

Lemma multi_trans : forall x y z, multi x y -> multi y z -> multi x z.
Proof.
  intros x y z Hxy. induction Hxy as [x0 | x0 y0 z0 Hxy Hyz IH].
  - intro Hyz. exact Hyz.
  - intro Hyz'. apply multi_step with (y := y0); eauto.
Qed.

Lemma multi_app1 : forall t t' u, multi t t' -> locally_closed_tm u ->
  multi (tm_app t u) (tm_app t' u).
Proof.
  intros t t' u H. induction H; intros Hu.
  - constructor.
  - eapply multi_step.
    + apply ST_App1; eauto.
    + apply IHmulti; assumption.
Qed.

Lemma multi_app2 : forall v t t', value v -> multi t t' ->
  multi (tm_app v t) (tm_app v t').
Proof.
  intros v t t' Hv H. induction H.
  - constructor.
  - eapply multi_step.
    + apply ST_App2; eauto.
    + apply IHmulti.
Qed.

Lemma multi_tapp : forall t t' U, multi t t' -> locally_closed_ty U ->
  multi (tm_tapp t U) (tm_tapp t' U).
Proof.
  intros t t' U H HU. induction H.
  - constructor.
  - eapply multi_step.
    + apply ST_TApp; eauto.
    + apply IHmulti; assumption.
Qed.

Lemma multi_succ : forall t t', multi t t' ->
  multi (tm_succ t) (tm_succ t').
Proof.
  intros t t' H. induction H.
  - constructor.
  - eapply multi_step; [apply ST_Succ; eauto | apply IHmulti].
Qed.

Lemma multi_rec_arg : forall n n' b s, multi n n' ->
  locally_closed_tm b -> locally_closed_tm s ->
  multi (tm_natrec n b s) (tm_natrec n' b s).
Proof.
  intros n n' b s H Hb Hs. induction H.
  - constructor.
  - eapply multi_step.
    + apply ST_RecArg; eauto.
    + apply IHmulti; assumption.
Qed.

Lemma multi_rec_base : forall n b b' s, numeric_value n -> multi b b' ->
  locally_closed_tm s -> multi (tm_natrec n b s) (tm_natrec n b' s).
Proof.
  intros n b b' s Hn H Hs. induction H.
  - constructor.
  - eapply multi_step.
    + apply ST_RecBase; eauto.
    + apply IHmulti; assumption.
Qed.

Lemma multi_rec_step : forall n b s s', numeric_value n -> value b ->
  multi s s' -> multi (tm_natrec n b s) (tm_natrec n b s').
Proof.
  intros n b s s' Hn Hb H. induction H.
  - constructor.
  - eapply multi_step.
    + apply ST_RecStep; eauto.
    + apply IHmulti.
Qed.

Lemma multi_if : forall c c' t u, multi c c' ->
  locally_closed_tm t -> locally_closed_tm u ->
  multi (tm_if c t u) (tm_if c' t u).
Proof.
  intros c c' t u H Ht Hu. induction H.
  - constructor.
  - eapply multi_step.
    + apply ST_If; eauto.
    + apply IHmulti; assumption.
Qed.

Lemma evaluates_multi : forall t v, locally_closed_tm t -> evaluates t v -> t -->* v.
Proof.
  intros t v Hlc He. induction He.
  - constructor.
  - unfold locally_closed_tm in Hlc. inversion Hlc.
    eapply multi_trans with (y := tm_app (tm_abs U body) arg).
    + apply (multi_app1 f (tm_abs U body) arg (IHHe1 H3)).
      assumption.
    + eapply multi_trans with (y := tm_app (tm_abs U body) v).
      * apply (multi_app2 (tm_abs U body) arg v).
        { apply eval_value with (t := f) (v := tm_abs U body). assumption. }
        { exact (IHHe2 H4). }
      * eapply multi_trans with (y := open_tm body v).
        { apply multi_step with (y := open_tm body v).
          - apply ST_AppAbs.
            + apply value_lc. apply eval_value with (t := f) (v := tm_abs U body). assumption.
            + apply eval_value with (t := arg) (v := v). assumption.
          - constructor. }
        apply IHHe3. apply (open_tm_lc U body v).
        { apply eval_value in He1. apply value_lc; assumption. }
        { apply eval_value in He2. assumption. }
  - unfold locally_closed_tm in Hlc. inversion Hlc.
    eapply multi_trans with (y := tm_tapp (tm_tabs body) U).
    + apply multi_tapp; eauto.
    + eapply multi_trans with (y := open_tm_ty body U).
      * apply multi_step with (y := open_tm_ty body U).
        { apply ST_TAppTabs.
          { apply value_lc. apply eval_value with (t := f) (v := tm_tabs body). assumption. }
          { assumption. } }
        { constructor. }
      * eauto 10 using open_tm_ty_lc, eval_value, value_lc.
  - unfold locally_closed_tm in Hlc. inversion Hlc.
    eapply multi_trans.
    + apply multi_if; eauto.
    + eapply multi_trans.
      * apply multi_step with (y := t).
        { apply ST_IfTrue; assumption. }
        { constructor. }
      * exact (IHHe2 H6).
  - unfold locally_closed_tm in Hlc. inversion Hlc.
    eapply multi_trans.
    + apply multi_if; eauto.
    + eapply multi_trans.
      * apply multi_step with (y := u).
        { apply ST_IfFalse; assumption. }
        { constructor. }
      * exact (IHHe2 H7).
  - unfold locally_closed_tm in Hlc. inversion Hlc.
    apply multi_succ; eauto.
  - unfold locally_closed_tm in Hlc. inversion Hlc.
    eapply multi_trans.
    + apply multi_rec_arg.
      { exact (IHHe1 H4). }
      { exact H5. }
      { exact H6. }
    + eapply multi_trans with (y := tm_natrec tm_zero vb s).
      * apply multi_rec_base with (n := tm_zero) (b := b) (b' := vb) (s := s).
        { constructor. }
        { exact (IHHe2 H5). }
        { exact H6. }
      * eapply multi_trans with (y := tm_natrec tm_zero vb vs).
        { apply multi_rec_step with (n := tm_zero) (b := vb) (s := s) (s' := vs).
          { constructor. }
          { apply eval_value with (t := b) (v := vb). assumption. }
          { exact (IHHe3 H6). } }
        { apply multi_step with (y := vb).
          { apply ST_RecZero.
            { apply eval_value with (t := b) (v := vb). assumption. }
            { apply eval_value with (t := s) (v := vs). assumption. } }
          { constructor. } }
  - unfold locally_closed_tm in Hlc. inversion Hlc.
    assert (Hk : locally_closed_tm k).
    { apply value_lc. apply v_nat. exact H. }
    assert (Hvb : value vb).
    { apply eval_value with (t := b) (v := vb). assumption. }
    assert (Hvs : value vs).
    { apply eval_value with (t := s) (v := vs). assumption. }
    assert (Hrec : locally_closed_tm (tm_natrec k vb vs)).
    { apply lc_tm_rec.
      { exact Hk. }
      { apply value_lc; exact Hvb. }
      { apply value_lc; exact Hvs. } }
    assert (Happ : locally_closed_tm (tm_app (tm_app vs k) (tm_natrec k vb vs))).
    { apply lc_tm_app.
      { apply lc_tm_app.
        { apply value_lc; exact Hvs. }
        { exact Hk. } }
      { exact Hrec. } }
    eapply multi_trans.
    + apply multi_rec_arg.
      { exact (IHHe1 H5). }
      { exact H6. }
      { exact H7. }
    + eapply multi_trans with (y := tm_natrec (tm_succ k) vb s).
      * apply multi_rec_base with (n := tm_succ k) (b := b) (b' := vb) (s := s).
        { constructor; exact H. }
        { exact (IHHe2 H6). }
        { exact H7. }
      * eapply multi_trans with (y := tm_natrec (tm_succ k) vb vs).
        { apply multi_rec_step with (n := tm_succ k) (b := vb) (s := s) (s' := vs).
          { constructor; exact H. }
          { exact Hvb. }
          { exact (IHHe3 H7). } }
        { apply multi_step with (y := tm_app (tm_app vs k) (tm_natrec k vb vs)).
          { apply ST_RecSucc.
            { exact H. }
            { exact Hvb. }
            { exact Hvs. } }
          { apply IHHe4. exact Happ. } }
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
  intros t Ht U v Hw Hv Htv.
  induction Ht; eauto using multi_refl, multi_step.
Qed.

End SystemFParametricityIfRecursionMediumTask.
