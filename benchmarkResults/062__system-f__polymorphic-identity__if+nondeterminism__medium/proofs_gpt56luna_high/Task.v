(** System F parametricity benchmark, Medium variant.
    Features: if-nondeterminism. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFParametricityIfNondeterminismMediumTask.

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
  | Ty_Bool : ty.

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
  | lc_tm_true : forall K k, lc_tm_at K k tm_true
  | lc_tm_false : forall K k, lc_tm_at K k tm_false
  | lc_tm_if : forall K k t1 t2 t3,
      lc_tm_at K k t1 -> lc_tm_at K k t2 -> lc_tm_at K k t3 -> lc_tm_at K k (tm_if t1 t2 t3)
  | lc_tm_choice : forall K k t1 t2,
      lc_tm_at K k t1 -> lc_tm_at K k t2 -> lc_tm_at K k (tm_choice t1 t2).

Definition locally_closed_tm (t : tm) : Prop := lc_tm_at 0 0 t.

Inductive value : tm -> Prop :=
  | v_abs : forall T t,
      locally_closed_tm (tm_abs T t) ->
      value (tm_abs T t)
  | v_tabs : forall t,
      locally_closed_tm (tm_tabs t) ->
      value (tm_tabs t)
  | v_true : value tm_true
  | v_false : value tm_false.

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
  | T_True : forall Delta Gamma, has_type Delta Gamma tm_true Ty_Bool
  | T_False : forall Delta Gamma, has_type Delta Gamma tm_false Ty_Bool
  | T_If : forall Delta Gamma t1 t2 t3 T,
      has_type Delta Gamma t1 Ty_Bool ->
      has_type Delta Gamma t2 T -> has_type Delta Gamma t3 T ->
      has_type Delta Gamma (tm_if t1 t2 t3) T
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
  end.

Definition expression_relation eta rho T t1 t2 :=
  expression_lifting (value_relation eta rho T) t1 t2.

(* Some elementary infrastructure for the fundamental theorem.  Type
   variables are atoms, rather than binders in the term syntax, so it is
   useful to keep the two instantiations of a term explicit. *)

Fixpoint ty_inst (q : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => q X
  | Ty_Arrow T1 T2 => Ty_Arrow (ty_inst q T1) (ty_inst q T2)
  | Ty_All T1 => Ty_All (ty_inst q T1)
  | Ty_Bool => Ty_Bool
  end.

Fixpoint tm_ty_inst (q : atom -> ty) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T t1 => tm_abs (ty_inst q T) (tm_ty_inst q t1)
  | tm_app t1 t2 => tm_app (tm_ty_inst q t1) (tm_ty_inst q t2)
  | tm_tabs t1 => tm_tabs (tm_ty_inst q t1)
  | tm_tapp t1 T => tm_tapp (tm_ty_inst q t1) (ty_inst q T)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (tm_ty_inst q t1) (tm_ty_inst q t2)
                         (tm_ty_inst q t3)
  | tm_choice t1 t2 => tm_choice (tm_ty_inst q t1) (tm_ty_inst q t2)
  end.

Fixpoint tm_inst (s : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => s x
  | tm_abs T t1 => tm_abs T (tm_inst s t1)
  | tm_app t1 t2 => tm_app (tm_inst s t1) (tm_inst s t2)
  | tm_tabs t1 => tm_tabs (tm_inst s t1)
  | tm_tapp t1 T => tm_tapp (tm_inst s t1) T
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (tm_inst s t1) (tm_inst s t2) (tm_inst s t3)
  | tm_choice t1 t2 => tm_choice (tm_inst s t1) (tm_inst s t2)
  end.

Definition upd_tm (s : atom -> tm) (x : atom) (u : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then u else s y.

Definition upd_ty (q : atom -> ty) (X : atom) (U : ty) : atom -> ty :=
  fun Y => if Nat.eqb X Y then U else q Y.

Fixpoint ty_atoms (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow T1 T2 => ty_atoms T1 ++ ty_atoms T2
  | Ty_All T1 => ty_atoms T1
  | Ty_Bool => []
  end.

Fixpoint tm_atoms (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs T t1 => ty_atoms T ++ tm_atoms t1
  | tm_app t1 t2 => tm_atoms t1 ++ tm_atoms t2
  | tm_tabs t1 => tm_atoms t1
  | tm_tapp t1 T => tm_atoms t1 ++ ty_atoms T
  | tm_true | tm_false => []
  | tm_if t1 t2 t3 => tm_atoms t1 ++ tm_atoms t2 ++ tm_atoms t3
  | tm_choice t1 t2 => tm_atoms t1 ++ tm_atoms t2
  end.

Fixpoint ctx_atoms (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (x, _) :: Gamma' => x :: ctx_atoms Gamma'
  end.

Fixpoint ctx_ty_atoms (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (_, T) :: Gamma' => ty_atoms T ++ ctx_ty_atoms Gamma'
  end.

Lemma in_ctx_atoms : forall Gamma x T,
    lookup_context x Gamma = Some T -> In x (ctx_atoms Gamma).
Proof.
  induction Gamma as [|[y A] Gamma IH]; simpl; intros x T H;
    try discriminate.
  destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. subst. simpl. auto.
  - right. eapply IH. exact H.
Qed.

Fixpoint list_sum (L : list atom) : atom :=
  match L with
  | [] => 0
  | x :: L' => x + list_sum L'
  end.

Lemma in_le_sum : forall L x, In x L -> x <= list_sum L.
Proof.
  induction L as [|y L IH]; simpl; intros x H.
  - contradiction.
  - destruct H as [H|H].
    + subst. lia.
    + specialize (IH x H). lia.
Qed.

Lemma fresh_list : forall L : list atom, exists x, ~ In x L.
Proof.
  intro L. exists (S (list_sum L)). intro H.
  pose proof (in_le_sum L (S (list_sum L)) H). lia.
Qed.

(* A more convenient fresh-name lemma, proved by induction on the list. *)
Lemma fresh_list' : forall L : list atom, exists x, ~ In x L.
Proof.
  exact fresh_list.
Qed.

Lemma lc_ty_weaken_rec : forall K d T, lc_ty_at K T -> lc_ty_at (K + d) T.
Proof.
  intros K d T H. induction H as
    [k0 i Hi | k0 X | k0 T1 T2 H1 IH1 H2 IH2 |
     k0 T H1 IH1 | k0]; simpl.
  - constructor. lia.
  - constructor.
  - constructor; [apply IH1 | apply IH2].
  - constructor. apply IH1.
  - constructor.
Qed.

Lemma lc_ty_weaken : forall k T, lc_ty_at 0 T -> lc_ty_at k T.
Proof.
  intros k T H. replace k with (0 + k) by lia.
  apply lc_ty_weaken_rec. exact H.
Qed.

Lemma lc_ty_open_inv : forall K U T,
    lc_ty_at K (open_ty_rec K U T) -> lc_ty_at (S K) T.
Proof.
  intros K U T. revert K U.
  induction T as [i|X|T1 IH1 T2 IH2|T IH|]; intros K U H;
    simpl in H.
  - destruct (Nat.eqb K i) eqn:E.
    + apply Nat.eqb_eq in E. subst. constructor. lia.
    + inversion H. constructor. lia.
  - inversion H. constructor.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor. eapply IH; eassumption.
  - constructor.
Qed.

Lemma lc_tm_open_inv : forall K k u t,
    lc_tm_at K k (open_tm_rec k u t) -> lc_tm_at K (S k) t.
Proof.
  intros K k u t. revert K k u.
  induction t as [i|x|T t IH|t1 IH1 t2 IH2|t IH|t IH| |
                   |t1 IH1 t2 IH2 t3 IH3|t1 IH1 t2 IH2];
    intros K k u H; simpl in H.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst. constructor. lia.
    + inversion H. constructor. lia.
  - inversion H. constructor.
  - inversion H; subst. constructor.
    + assumption.
    + eapply IH; eassumption.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor. eapply IH; eassumption.
  - inversion H; subst. constructor; eauto.
  - constructor.
  - constructor.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor; eauto.
Qed.

Lemma open_tm_rec_lc_at : forall K d k u t,
    lc_tm_at K d t -> open_tm_rec (k + d) u t = t.
Proof.
  intros K d k u t H.
  induction H; simpl.
  - simpl. destruct (Nat.eqb (k + k0) i) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + reflexivity.
  - reflexivity.
  - simpl. assert (Heq : S (k + k0) = k + S k0) by lia.
    assert (Hopen : open_tm_rec (S (k + k0)) u t = t).
    { rewrite Heq. exact IHlc_tm_at. }
    congruence.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - reflexivity.
  - reflexivity.
  - f_equal; eauto.
  - f_equal; eauto.
Qed.

Lemma open_tm_rec_lc : forall k u t,
    locally_closed_tm t -> open_tm_rec k u t = t.
Proof.
  intros k u t H. unfold locally_closed_tm in H.
  replace k with (k + 0) by lia.
  apply open_tm_rec_lc_at with (K := 0) (d := 0).
  exact H.
Qed.

Lemma open_ty_rec_lc_at : forall K d U T,
    lc_ty_at K T -> open_ty_rec (K + d) U T = T.
Proof.
  intros K d U T H. induction H; simpl.
  - destruct (Nat.eqb (k + d) i) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + reflexivity.
  - reflexivity.
  - f_equal; assumption.
  - f_equal; assumption.
  - reflexivity.
Qed.

Lemma open_ty_rec_lc : forall k U T,
    locally_closed_ty T -> open_ty_rec k U T = T.
Proof.
  intros k U T H. apply open_ty_rec_lc_at with (K := 0) (d := k).
  exact H.
Qed.

Lemma ty_inst_open_ty : forall q X U k T,
    ~ In X (ty_atoms T) ->
    (forall Y, locally_closed_ty (q Y)) ->
    ty_inst (upd_ty q X U) (open_ty_rec k (Ty_FVar X) T) =
    open_ty_rec k U (ty_inst q T).
Proof.
  intros q X U k T. revert k.
  induction T as [i|Y|T1 IH1 T2 IH2|T IH|]; intros k Hfresh Hq;
    simpl in *.
  - destruct (Nat.eqb k i) eqn:E.
    + simpl. unfold ty_inst, upd_ty. rewrite Nat.eqb_refl. reflexivity.
    + simpl. reflexivity.
  - destruct (Nat.eqb X Y) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply Hfresh. simpl. auto.
    + unfold ty_inst, upd_ty. rewrite E. symmetry. apply open_ty_rec_lc.
      apply Hq.
  - assert (H1 : ~ In X (ty_atoms T1)).
      { intro H. apply Hfresh. apply in_app_iff. left; exact H. }
    assert (H2 : ~ In X (ty_atoms T2)).
      { intro H. apply Hfresh. apply in_app_iff. right; exact H. }
    simpl. rewrite (IH1 k H1 Hq). rewrite (IH2 k H2 Hq). reflexivity.
  - simpl. rewrite (IH (S k) Hfresh Hq). reflexivity.
  - reflexivity.
Qed.

Lemma tm_ty_inst_open_ty : forall q X U k t,
    ~ In X (tm_atoms t) ->
    (forall Y, locally_closed_ty (q Y)) ->
    tm_ty_inst (upd_ty q X U) (open_tm_ty_rec k (Ty_FVar X) t) =
    open_tm_ty_rec k U (tm_ty_inst q t).
Proof.
  intros q X U k t. revert k.
  induction t as [i|x|T t IH|t1 IH1 t2 IH2|t IH|t IH| |
                   |t1 IH1 t2 IH2 t3 IH3|t1 IH1 t2 IH2]; intros k Hfresh Hq;
    simpl in *.
  - reflexivity.
  - reflexivity.
  - assert (HT : ~ In X (ty_atoms T)).
      { intro H. apply Hfresh. apply in_app_iff. left; exact H. }
    assert (Ht : ~ In X (tm_atoms t)).
      { intro H. apply Hfresh. apply in_app_iff. right; exact H. }
    simpl. rewrite (ty_inst_open_ty q X U k T HT Hq).
    rewrite (IH k Ht Hq). reflexivity.
  - assert (H1 : ~ In X (tm_atoms t1)).
      { intro H. apply Hfresh. apply in_app_iff. left; exact H. }
    assert (H2 : ~ In X (tm_atoms t2)).
      { intro H. apply Hfresh. apply in_app_iff. right; exact H. }
    simpl. rewrite (IH1 k H1 Hq), (IH2 k H2 Hq). reflexivity.
  - simpl. rewrite (IH (S k) Hfresh Hq). reflexivity.
  - assert (Ht : ~ In X (tm_atoms t)).
      { intro H. apply Hfresh. apply in_app_iff. left; exact H. }
    assert (HT : ~ In X (ty_atoms t0)).
      { intro H. apply Hfresh. apply in_app_iff. right; exact H. }
    simpl. rewrite (IH k Ht Hq), (ty_inst_open_ty q X U k t0 HT Hq).
    reflexivity.
  - reflexivity.
  - reflexivity.
  - assert (H1 : ~ In X (tm_atoms t1)).
      { intro H. apply Hfresh. apply in_app_iff. left; exact H. }
    assert (H2 : ~ In X (tm_atoms t2)).
      { intro H. apply Hfresh. apply in_app_iff. right. apply in_app_iff. left; exact H. }
    assert (H3 : ~ In X (tm_atoms t3)).
      { intro H. apply Hfresh. apply in_app_iff. right. apply in_app_iff. right; exact H. }
    simpl. rewrite (IH1 k H1 Hq), (IH2 k H2 Hq), (IH3 k H3 Hq). reflexivity.
  - assert (H1 : ~ In X (tm_atoms t1)).
      { intro H. apply Hfresh. apply in_app_iff. left; exact H. }
    assert (H2 : ~ In X (tm_atoms t2)).
      { intro H. apply Hfresh. apply in_app_iff. right; exact H. }
    simpl. rewrite (IH1 k H1 Hq), (IH2 k H2 Hq). reflexivity.
Qed.

Lemma tm_inst_open : forall s x u k t,
    ~ In x (tm_atoms t) ->
    (forall y, locally_closed_tm (s y)) ->
    tm_inst (upd_tm s x u) (open_tm_rec k (tm_fvar x) t) =
    open_tm_rec k u (tm_inst s t).
Proof.
  intros s x u k t. revert k.
  induction t as [i|y|T t IH|t1 IH1 t2 IH2|t IH|t IH| |
                   |t1 IH1 t2 IH2 t3 IH3|t1 IH1 t2 IH2]; intros k Hfresh Hs;
    simpl in *.
  - destruct (Nat.eqb k i) eqn:E.
    + unfold tm_inst, upd_tm. rewrite Nat.eqb_refl. reflexivity.
    + simpl. reflexivity.
  - destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply Hfresh. simpl. auto.
    + unfold tm_inst, upd_tm. rewrite E. symmetry. apply open_tm_rec_lc. apply Hs.
  - assert (HT : ~ In x (ty_atoms T)).
      { intro H. apply Hfresh. apply in_app_iff. left; exact H. }
    assert (Ht : ~ In x (tm_atoms t)).
      { intro H. apply Hfresh. apply in_app_iff. right; exact H. }
    simpl. rewrite (IH (S k) Ht Hs). reflexivity.
  - assert (H1 : ~ In x (tm_atoms t1)).
      { intro H. apply Hfresh. apply in_app_iff. left; exact H. }
    assert (H2 : ~ In x (tm_atoms t2)).
      { intro H. apply Hfresh. apply in_app_iff. right; exact H. }
    simpl. rewrite (IH1 k H1 Hs), (IH2 k H2 Hs). reflexivity.
  - simpl. rewrite (IH k Hfresh Hs). reflexivity.
  - assert (Ht : ~ In x (tm_atoms t)).
      { intro H. apply Hfresh. apply in_app_iff. left; exact H. }
    simpl. rewrite (IH k Ht Hs). reflexivity.
  - reflexivity.
  - reflexivity.
  - assert (H1 : ~ In x (tm_atoms t1)).
      { intro H. apply Hfresh. apply in_app_iff. left; exact H. }
    assert (H2 : ~ In x (tm_atoms t2)).
      { intro H. apply Hfresh. apply in_app_iff. right. apply in_app_iff. left; exact H. }
    assert (H3 : ~ In x (tm_atoms t3)).
      { intro H. apply Hfresh. apply in_app_iff. right. apply in_app_iff. right; exact H. }
    simpl. rewrite (IH1 k H1 Hs), (IH2 k H2 Hs), (IH3 k H3 Hs). reflexivity.
  - assert (H1 : ~ In x (tm_atoms t1)).
      { intro H. apply Hfresh. apply in_app_iff. left; exact H. }
    assert (H2 : ~ In x (tm_atoms t2)).
      { intro H. apply Hfresh. apply in_app_iff. right; exact H. }
    simpl. rewrite (IH1 k H1 Hs), (IH2 k H2 Hs). reflexivity.
Qed.

Lemma tm_ty_inst_open_tm : forall q k x t,
    tm_ty_inst q (open_tm_rec k (tm_fvar x) t) =
    open_tm_rec k (tm_fvar x) (tm_ty_inst q t).
Proof.
  intros q k x t. revert k. induction t as [i|y|T t IH|t1 IH1 t2 IH2|t IH|t IH| |
                   |t1 IH1 t2 IH2 t3 IH3|t1 IH1 t2 IH2]; intros k; simpl.
  - destruct (Nat.eqb k i); reflexivity.
  - reflexivity.
  - rewrite IH. reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH. reflexivity.
  - rewrite IH. reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IH1, IH2, IH3. reflexivity.
  - rewrite IH1, IH2. reflexivity.
Qed.

Lemma open_tm_ty_rec_lc_at : forall K k U t,
    lc_tm_at K 0 t -> open_tm_ty_rec (K + k) U t = t.
Proof.
  intros K k U t H. induction H; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite (open_ty_rec_lc_at K k U T H). f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - rewrite (open_ty_rec_lc_at K k U T H0). f_equal; eauto.
  - reflexivity.
  - reflexivity.
  - f_equal; eauto.
  - f_equal; eauto.
Qed.

Lemma open_tm_ty_rec_lc : forall k U t,
    locally_closed_tm t -> open_tm_ty_rec k U t = t.
Proof.
  intros k U t H. unfold locally_closed_tm in H.
  replace k with (0 + k) by lia.
  apply open_tm_ty_rec_lc_at. exact H.
Qed.

Lemma tm_inst_open_ty : forall s k U t,
    (forall a, locally_closed_tm (s a)) ->
    tm_inst s (open_tm_ty_rec k U t) =
    open_tm_ty_rec k U (tm_inst s t).
Proof.
  intros s k U t Hs. revert k.
  induction t as [i|a|T t IH|t1 IH1 t2 IH2|t IH|t IH| |
                   |t1 IH1 t2 IH2 t3 IH3|t1 IH1 t2 IH2]; intros k; simpl.
  - reflexivity.
  - symmetry. apply open_tm_ty_rec_lc. apply Hs.
  - rewrite IH. reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH. reflexivity.
  - rewrite IH. reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IH1, IH2, IH3. reflexivity.
  - rewrite IH1, IH2. reflexivity.
Qed.

Lemma tm_inst_id : forall t,
    tm_inst (fun x => tm_fvar x) t = t.
Proof.
  induction t as [i|x|T t IH|t1 IH1 t2 IH2|t IH|t IH| |
                   |t1 IH1 t2 IH2 t3 IH3|t1 IH1 t2 IH2]; simpl;
    try rewrite ?IH, ?IH1, ?IH2, ?IH3; reflexivity.
Qed.

Lemma lc_ty_inst : forall q K T,
    (forall X, locally_closed_ty (q X)) ->
    lc_ty_at K T -> lc_ty_at K (ty_inst q T).
Proof.
  intros q K T Hq H. induction H; simpl; try constructor; eauto.
  - apply lc_ty_weaken. apply Hq.
Qed.

Lemma lc_tm_weaken : forall K d dK dk t,
    lc_tm_at K d t -> lc_tm_at (K + dK) (d + dk) t.
Proof.
  intros K d dK dk t H. revert dK dk.
  induction H; intros dK dk; simpl.
  - constructor. lia.
  - constructor.
  - constructor.
    + apply lc_ty_weaken_rec with (d := dK). exact H.
    + eauto.
  - constructor; eauto.
  - constructor; eauto.
  - constructor.
    + eauto.
    + apply lc_ty_weaken_rec with (d := dK). exact H0.
  - constructor.
  - constructor.
  - constructor; eauto.
  - constructor; eauto.
Qed.

Lemma lc_tm_closed_weaken : forall K k t,
    locally_closed_tm t -> lc_tm_at K k t.
Proof.
  intros K k t H. unfold locally_closed_tm in H.
  replace K with (0 + K) by lia. replace k with (0 + k) by lia.
  apply lc_tm_weaken with (dK := K) (dk := k). exact H.
Qed.

Lemma lc_tm_inst : forall q s K k t,
    (forall X, locally_closed_ty (q X)) ->
    (forall x, locally_closed_tm (s x)) ->
    lc_tm_at K k t -> lc_tm_at K k (tm_inst s (tm_ty_inst q t)).
Proof.
  intros q s K k t Hq Hs H. induction H; simpl.
  - constructor. assumption.
  - apply lc_tm_closed_weaken. apply Hs.
  - constructor; eauto using lc_ty_inst.
  - constructor; eauto.
  - constructor; eauto.
  - constructor; eauto using lc_ty_inst.
  - constructor.
  - constructor.
  - constructor; eauto.
  - constructor; eauto.
Qed.

Lemma lc_tm_ty_open_inv : forall K k U t,
    lc_tm_at K k (open_tm_ty_rec K U t) -> lc_tm_at (S K) k t.
Proof.
  intros K k U t. revert K k U.
  induction t as [i|x|T t IH|t1 IH1 t2 IH2|t IH|t IH| |
                   |t1 IH1 t2 IH2 t3 IH3|t1 IH1 t2 IH2];
    intros K k U H; simpl in H.
  - inversion H. constructor. assumption.
  - inversion H. constructor.
  - inversion H; subst. constructor.
    + eapply lc_ty_open_inv; eassumption.
    + eapply IH; eassumption.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor. eapply IH; eassumption.
  - inversion H; subst. constructor.
    + eapply IH; eassumption.
    + eapply lc_ty_open_inv; eassumption.
  - constructor.
  - constructor.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor; eauto.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H. induction H.
  - constructor.
  - constructor; assumption.
  - unfold locally_closed_ty.
    destruct (fresh_list L) as [X HX].
    constructor. apply lc_ty_open_inv with (K := 0) (U := Ty_FVar X).
    apply H0. exact HX.
  - constructor.
Qed.

Lemma has_type_lc : forall Delta Gamma t T,
    has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T H. induction H.
  - constructor.
  - unfold locally_closed_tm.
    destruct (fresh_list (L ++ ctx_atoms Gamma ++ tm_atoms t2)) as [x Hx].
    apply lc_tm_abs.
    + eapply wf_ty_lc; eassumption.
    + apply lc_tm_open_inv with (K := 0) (k := 0) (u := tm_fvar x).
      apply H1. intro Hin. apply Hx. apply in_or_app. left. exact Hin.
  - constructor; assumption.
  - unfold locally_closed_tm.
    destruct (fresh_list (L ++ tm_atoms t)) as [X HX].
    apply lc_tm_tabs.
    apply lc_tm_ty_open_inv with (K := 0) (k := 0) (U := Ty_FVar X).
    apply H0. intro Hin. apply HX. apply in_or_app. left. exact Hin.
  - apply lc_tm_tapp.
    + assumption.
    + eapply wf_ty_lc; eassumption.
  - constructor.
  - constructor.
  - constructor; assumption.
  - constructor; assumption.
Qed.

Lemma tm_ty_inst_lc : forall q K k t,
    (forall X, locally_closed_ty (q X)) ->
    lc_tm_at K k t -> lc_tm_at K k (tm_ty_inst q t).
Proof.
  intros q K k t Hq H.
  pose proof (lc_tm_inst q (fun x => tm_fvar x) K k t Hq
    (fun x => lc_tm_fvar 0 0 x) H) as H'.
  rewrite (tm_inst_id (tm_ty_inst q t)) in H'. exact H'.
Qed.

Definition tenv_ok (eta : list binary_candidate) (rho : binary_env)
    (Gamma : context) (s1 s2 : atom -> tm) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    value_relation eta rho T (s1 x) (s2 x).

Lemma expression_lifting_ext : forall R S t1 t2,
    (forall v1 v2, R v1 v2 <-> S v1 v2) ->
    expression_lifting R t1 t2 <-> expression_lifting S t1 t2.
Proof.
  intros R S t1 t2 H. unfold expression_lifting, results_match.
  split; intros [Hlc1 [Hlc2 [v1 [v2 [He1 [He2 Hr]]]]]];
    repeat split; try assumption; exists v1, v2; repeat split; try assumption.
  - apply (proj1 (H v1 v2)); exact Hr.
  - apply (proj2 (H v1 v2)); exact Hr.
Qed.

Lemma value_relation_open_rec : forall eta rho X a k T v1 v2,
    ~ In X (ty_atoms T) -> nth_error eta k = Some a ->
    value_relation eta (relation_update rho X a)
      (open_ty_rec k (Ty_FVar X) T) v1 v2 <->
    value_relation eta rho T v1 v2.
Proof.
  intros eta rho X a k T. revert eta k.
  induction T as [i|Y|T1 IH1 T2 IH2|T IH|];
    intros eta k v1 v2 Hfresh Hnth; simpl in *.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst.
      destruct (nth_error eta i) as [b|] eqn:Eb; inversion Hnth; subst.
      simpl. unfold relation_update. rewrite Nat.eqb_refl. simpl.
      split; intro H; exact H.
    + simpl. split; intro H; exact H.
  - destruct (Nat.eqb X Y) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply Hfresh. simpl; auto.
    + simpl. unfold relation_update. rewrite E. split; intro H; exact H.
  - assert (H1 : ~ In X (ty_atoms T1)).
      { intro H. apply Hfresh. apply in_app_iff. left; exact H. }
    assert (H2 : ~ In X (ty_atoms T2)).
      { intro H. apply Hfresh. apply in_app_iff. right; exact H. }
    simpl. split; intro H.
    + destruct H as [Hv1 [Hv2 Hex]].
      destruct Hex as [U1 [body1 [U2 [body2 [He1 [He2 Hall]]]]]].
      split; [exact Hv1 | split; [exact Hv2 |]].
      exists U1, body1, U2, body2.
      split; [exact He1 | split; [exact He2 |]].
      intros z1 z2 Harg.
      assert (Harg' : value_relation eta (relation_update rho X a)
          (open_ty_rec k (Ty_FVar X) T1) z1 z2).
      { apply (proj2 (IH1 eta k z1 z2 H1 Hnth)); exact Harg. }
      assert (Hall' := Hall z1 z2 Harg').
      assert (HExt :
        expression_lifting
          (value_relation eta (relation_update rho X a)
            (open_ty_rec k (Ty_FVar X) T2))
          (open_tm body1 z1) (open_tm body2 z2) <->
        expression_lifting (value_relation eta rho T2)
          (open_tm body1 z1) (open_tm body2 z2)).
      { eapply expression_lifting_ext; intros z3 z4;
        apply (IH2 eta k z3 z4 H2 Hnth). }
      apply (proj1 HExt). exact Hall'.
    + destruct H as [Hv1 [Hv2 Hex]].
      destruct Hex as [U1 [body1 [U2 [body2 [He1 [He2 Hall]]]]]].
      split; [exact Hv1 | split; [exact Hv2 |]].
      exists U1, body1, U2, body2.
      split; [exact He1 | split; [exact He2 |]].
      intros z1 z2 Harg.
      assert (Harg' : value_relation eta rho T1 z1 z2).
      { apply (proj1 (IH1 eta k z1 z2 H1 Hnth)); exact Harg. }
      assert (Hall' := Hall z1 z2 Harg').
      assert (HExt :
        expression_lifting
          (value_relation eta (relation_update rho X a)
            (open_ty_rec k (Ty_FVar X) T2))
          (open_tm body1 z1) (open_tm body2 z2) <->
        expression_lifting (value_relation eta rho T2)
          (open_tm body1 z1) (open_tm body2 z2)).
      { eapply expression_lifting_ext; intros z3 z4;
        apply (IH2 eta k z3 z4 H2 Hnth). }
      apply (proj2 HExt). exact Hall'.
  - simpl. split; intro H.
    + destruct H as [Hv1 [Hv2 Hex]].
      destruct Hex as [b1 [b2 [He1 [He2 Hb]]]].
      split; [exact Hv1 | split; [exact Hv2 |]].
      exists b1, b2. split; [exact He1 | split; [exact He2 |]].
      intros U1 U2 c HU1 HU2.
      assert (HExt :
        expression_lifting
          (value_relation (c :: eta) (relation_update rho X a)
            (open_ty_rec (S k) (Ty_FVar X) T))
          (open_tm_ty b1 U1) (open_tm_ty b2 U2) <->
        expression_lifting (value_relation (c :: eta) rho T)
          (open_tm_ty b1 U1) (open_tm_ty b2 U2)).
      { eapply expression_lifting_ext; intros z1 z2.
        apply (IH (c :: eta) (S k) z1 z2 Hfresh).
        simpl. exact Hnth. }
      apply (proj1 HExt). apply Hb; assumption.
    + destruct H as [Hv1 [Hv2 Hex]].
      destruct Hex as [b1 [b2 [He1 [He2 Hb]]]].
      split; [exact Hv1 | split; [exact Hv2 |]].
      exists b1, b2. split; [exact He1 | split; [exact He2 |]].
      intros U1 U2 c HU1 HU2.
      assert (HExt :
        expression_lifting
          (value_relation (c :: eta) (relation_update rho X a)
            (open_ty_rec (S k) (Ty_FVar X) T))
          (open_tm_ty b1 U1) (open_tm_ty b2 U2) <->
        expression_lifting (value_relation (c :: eta) rho T)
          (open_tm_ty b1 U1) (open_tm_ty b2 U2)).
      { eapply expression_lifting_ext; intros z1 z2.
        apply (IH (c :: eta) (S k) z1 z2 Hfresh).
        simpl. exact Hnth. }
      apply (proj2 HExt). apply Hb; assumption.
  - split; intro H; exact H.
Qed.

Lemma value_relation_update_fresh : forall eta rho X a T v1 v2,
    ~ In X (ty_atoms T) ->
    value_relation eta (relation_update rho X a) T v1 v2 <->
    value_relation eta rho T v1 v2.
Proof.
  intros eta rho X a T. revert eta rho X a.
  induction T as [i|Y|T1 IH1 T2 IH2|T IH|];
    intros eta rho X a v1 v2 Hfresh; simpl in *.
  - split; intro H; exact H.
  - destruct (Nat.eqb X Y) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply Hfresh. simpl; auto.
    + unfold relation_update. rewrite E. simpl. split; intro H; exact H.
  - assert (H1 : ~ In X (ty_atoms T1)).
      { intro H. apply Hfresh. apply in_app_iff. left; exact H. }
    assert (H2 : ~ In X (ty_atoms T2)).
      { intro H. apply Hfresh. apply in_app_iff. right; exact H. }
    simpl. split; intro H.
    + destruct H as [Hv1 [Hv2 Hex]].
      destruct Hex as [U1 [b1 [U2 [b2 [He1 [He2 Hall]]]]]].
      split; [exact Hv1 | split; [exact Hv2 |]].
      exists U1,b1,U2,b2. split; [exact He1 | split; [exact He2 |]].
      intros z1 z2 Hz.
      assert (Hz' : value_relation eta (relation_update rho X a) T1 z1 z2).
      { apply (proj2 (IH1 eta rho X a z1 z2 H1)); exact Hz. }
      assert (HH := Hall z1 z2 Hz').
      assert (HE :
        expression_lifting (value_relation eta rho T2)
          (open_tm b1 z1) (open_tm b2 z2) <->
        expression_lifting
          (value_relation eta (relation_update rho X a) T2)
          (open_tm b1 z1) (open_tm b2 z2)).
      { eapply expression_lifting_ext; intros p q.
        symmetry. apply (IH2 eta rho X a p q H2). }
      apply (proj2 HE); exact HH.
    + destruct H as [Hv1 [Hv2 Hex]].
      destruct Hex as [U1 [b1 [U2 [b2 [He1 [He2 Hall]]]]]].
      split; [exact Hv1 | split; [exact Hv2 |]].
      exists U1,b1,U2,b2. split; [exact He1 | split; [exact He2 |]].
      intros z1 z2 Hz.
      assert (Hz' : value_relation eta rho T1 z1 z2).
      { apply (proj1 (IH1 eta rho X a z1 z2 H1)); exact Hz. }
      assert (HH := Hall z1 z2 Hz').
      assert (HE :
        expression_lifting (value_relation eta rho T2)
          (open_tm b1 z1) (open_tm b2 z2) <->
        expression_lifting
          (value_relation eta (relation_update rho X a) T2)
          (open_tm b1 z1) (open_tm b2 z2)).
      { eapply expression_lifting_ext; intros p q.
        symmetry. apply (IH2 eta rho X a p q H2). }
      apply (proj1 HE); exact HH.
  - simpl. split; intro H.
    + destruct H as [Hv1 [Hv2 Hex]].
      destruct Hex as [b1 [b2 [He1 [He2 Hb]]]].
      split; [exact Hv1 | split; [exact Hv2 |]].
      exists b1,b2. split; [exact He1 | split; [exact He2 |]].
      intros U1 U2 c HU1 HU2.
      assert (HE :
        expression_lifting (value_relation (c :: eta) rho T)
          (open_tm_ty b1 U1) (open_tm_ty b2 U2) <->
        expression_lifting
          (value_relation (c :: eta) (relation_update rho X a) T)
          (open_tm_ty b1 U1) (open_tm_ty b2 U2)).
      { eapply expression_lifting_ext; intros p q.
        symmetry. apply (IH (c :: eta) rho X a p q Hfresh). }
      apply (proj2 HE); apply Hb; assumption.
    + destruct H as [Hv1 [Hv2 Hex]].
      destruct Hex as [b1 [b2 [He1 [He2 Hb]]]].
      split; [exact Hv1 | split; [exact Hv2 |]].
      exists b1,b2. split; [exact He1 | split; [exact He2 |]].
      intros U1 U2 c HU1 HU2.
      assert (HE :
        expression_lifting (value_relation (c :: eta) rho T)
          (open_tm_ty b1 U1) (open_tm_ty b2 U2) <->
        expression_lifting
          (value_relation (c :: eta) (relation_update rho X a) T)
          (open_tm_ty b1 U1) (open_tm_ty b2 U2)).
      { eapply expression_lifting_ext; intros p q.
        symmetry. apply (IH (c :: eta) rho X a p q Hfresh). }
      apply (proj1 HE); apply Hb; assumption.
  - split; intro H; exact H.
Qed.

Lemma tenv_update_fresh : forall eta rho X a Gamma s1 s2,
    (forall x T, lookup_context x Gamma = Some T ->
       ~ In X (ty_atoms T)) ->
    tenv_ok eta rho Gamma s1 s2 ->
    tenv_ok eta (relation_update rho X a) Gamma s1 s2.
Proof.
  intros eta rho X a Gamma s1 s2 Hfresh Henv x T Hlook.
  apply (proj2 (value_relation_update_fresh eta rho X a T (s1 x) (s2 x)
    (Hfresh x T Hlook))).
  apply Henv; assumption.
Qed.

Lemma tenv_extend_tm : forall eta rho Gamma s1 s2 x T u1 u2,
    ~ In x (ctx_atoms Gamma) ->
    value_relation eta rho T u1 u2 ->
    tenv_ok eta rho Gamma s1 s2 ->
    tenv_ok eta rho (update Gamma x T)
      (upd_tm s1 x u1) (upd_tm s2 x u2).
Proof.
  intros eta rho Gamma s1 s2 x T u1 u2 Hfresh Hrel Henv y A Hlook.
  simpl in Hlook. destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst. inversion Hlook. subst.
    unfold upd_tm. rewrite Nat.eqb_refl. exact Hrel.
  - unfold upd_tm. rewrite Nat.eqb_sym, E.
    apply Henv. destruct Gamma as [|[z B] Gamma]; simpl in *.
    + discriminate.
    + destruct (Nat.eqb y z) eqn:E2; assumption.
Qed.

Definition values_env (s1 s2 : atom -> tm) : Prop :=
  forall x, value (s1 x) /\ value (s2 x).

Definition tenv_all (rho : binary_env) (Gamma : context)
    (s1 s2 : atom -> tm) : Prop :=
  forall eta, tenv_ok eta rho Gamma s1 s2.

Lemma values_env_update : forall s1 s2 x u1 u2,
    values_env s1 s2 -> value u1 -> value u2 ->
    values_env (upd_tm s1 x u1) (upd_tm s2 x u2).
Proof.
  intros s1 s2 x u1 u2 H Hu1 Hu2 y.
  unfold upd_tm. destruct (Nat.eqb x y) eqn:E; simpl.
  - split; assumption.
  - apply H.
Qed.

Lemma tenv_all_extend : forall rho Gamma s1 s2 x T u1 u2,
    ~ In x (ctx_atoms Gamma) ->
    (forall eta, value_relation eta rho T u1 u2) ->
    tenv_all rho Gamma s1 s2 ->
    tenv_all rho (update Gamma x T)
      (upd_tm s1 x u1) (upd_tm s2 x u2).
Proof.
  intros rho Gamma s1 s2 x T u1 u2 Hfresh Hrel Henv eta.
  eapply tenv_extend_tm.
  - exact Hfresh.
  - apply Hrel.
  - apply Henv.
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

End SystemFParametricityIfNondeterminismMediumTask.
