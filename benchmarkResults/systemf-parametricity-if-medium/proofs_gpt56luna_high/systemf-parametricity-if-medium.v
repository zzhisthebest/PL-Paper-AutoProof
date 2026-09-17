(** System F parametricity benchmark, Medium variant.
    Features: if. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFParametricityIfMediumTask.

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

Notation "'Bool'" := Ty_Bool (in custom systemf_ty at level 0) : systemf_scope.
Notation "'true'" := tm_true (in custom systemf_tm at level 0) : systemf_scope.
Notation "'false'" := tm_false (in custom systemf_tm at level 0) : systemf_scope.
Notation "'if' t1 'then' t2 'else' t3" := (tm_if t1 t2 t3)
  (in custom systemf_tm at level 200, t1 custom systemf_tm, t2 custom systemf_tm, t3 custom systemf_tm at level 200) : systemf_scope.

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
      lc_tm_at K k t1 -> lc_tm_at K k t2 -> lc_tm_at K k t3 -> lc_tm_at K k (tm_if t1 t2 t3).

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
      has_type Delta Gamma (tm_if t1 t2 t3) T.

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
      evaluates (tm_if c t u) v.

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

(* The two small substitution functions below are useful in stating the
   abstraction theorem.  In contrast to [ty_subst], they perform all the
   (free) type-variable substitutions at once. *)
Fixpoint inst_ty (theta : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => theta X
  | Ty_Arrow T1 T2 => Ty_Arrow (inst_ty theta T1) (inst_ty theta T2)
  | Ty_All T1 => Ty_All (inst_ty theta T1)
  | Ty_Bool => Ty_Bool
  end.

Fixpoint inst_tm_ty (theta : atom -> ty) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T t1 => tm_abs (inst_ty theta T) (inst_tm_ty theta t1)
  | tm_app t1 t2 => tm_app (inst_tm_ty theta t1) (inst_tm_ty theta t2)
  | tm_tabs t1 => tm_tabs (inst_tm_ty theta t1)
  | tm_tapp t1 T => tm_tapp (inst_tm_ty theta t1) (inst_ty theta T)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (inst_tm_ty theta t1) (inst_tm_ty theta t2)
                         (inst_tm_ty theta t3)
  end.

Fixpoint inst_tm (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_abs T t1 => tm_abs T (inst_tm sigma t1)
  | tm_app t1 t2 => tm_app (inst_tm sigma t1) (inst_tm sigma t2)
  | tm_tabs t1 => tm_tabs (inst_tm sigma t1)
  | tm_tapp t1 T => tm_tapp (inst_tm sigma t1) T
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (inst_tm sigma t1) (inst_tm sigma t2)
                       (inst_tm sigma t3)
  end.

Definition inst_ctx (theta : atom -> ty) (Gamma : context) : context :=
  map (fun p => (fst p, inst_ty theta (snd p))) Gamma.

Definition theta_update (theta : atom -> ty) (X : atom) (U : ty) : atom -> ty :=
  fun Y => if Nat.eqb X Y then U else theta Y.

Definition sigma_update (sigma : atom -> tm) (x : atom) (v : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then v else sigma y.

Definition rho_ok (Delta : ty_context) (theta : atom -> ty) :=
  forall X, In X Delta -> wf_ty [] (theta X).

Definition term_subst_ok (eta : list binary_candidate) (rho : binary_env)
    (Gamma : context) (theta1 theta2 : atom -> ty)
    (sigma1 sigma2 : atom -> tm) :=
  forall x T, lookup_context x Gamma = Some T ->
    value_relation eta rho T (sigma1 x) (sigma2 x) /\
    has_type [] empty (inst_tm_ty theta1 (sigma1 x)) (inst_ty theta1 T) /\
    has_type [] empty (inst_tm_ty theta2 (sigma2 x)) (inst_ty theta2 T).

Fixpoint ty_index (X : atom) (Delta : ty_context) : option nat :=
  match Delta with
  | [] => None
  | Y :: Delta' => if Nat.eqb X Y then Some 0
                  else match ty_index X Delta' with
                       | Some n => Some (S n)
                       | None => None
                       end
  end.

Fixpoint reify_ty_rec (k : nat) (Delta : ty_context) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X =>
      match ty_index X Delta with
      | Some i => Ty_BVar (k + i)
      | None => Ty_FVar X
      end
  | Ty_Arrow T1 T2 => Ty_Arrow (reify_ty_rec k Delta T1)
                               (reify_ty_rec k Delta T2)
  | Ty_All T1 => Ty_All (reify_ty_rec (S k) Delta T1)
  | Ty_Bool => Ty_Bool
  end.

Definition reify_ty (Delta : ty_context) (T : ty) : ty :=
  reify_ty_rec 0 Delta T.

Fixpoint reify_tm_rec (k : nat) (Delta : ty_context) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T t1 => tm_abs (reify_ty_rec k Delta T)
                         (reify_tm_rec k Delta t1)
  | tm_app t1 t2 => tm_app (reify_tm_rec k Delta t1)
                         (reify_tm_rec k Delta t2)
  | tm_tabs t1 => tm_tabs (reify_tm_rec (S k) Delta t1)
  | tm_tapp t1 T => tm_tapp (reify_tm_rec k Delta t1)
                          (reify_ty_rec k Delta T)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (reify_tm_rec k Delta t1)
                         (reify_tm_rec k Delta t2)
                         (reify_tm_rec k Delta t3)
  end.

Definition reify_tm (Delta : ty_context) (t : tm) : tm :=
  reify_tm_rec 0 Delta t.

Fixpoint atoms_ty (T : ty) : list atom :=
  match T with
  | Ty_BVar _ | Ty_Bool => []
  | Ty_FVar X => [X]
  | Ty_Arrow T1 T2 => atoms_ty T1 ++ atoms_ty T2
  | Ty_All T1 => atoms_ty T1
  end.

Fixpoint atoms_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_true | tm_false => []
  | tm_fvar x => [x]
  | tm_abs T t1 => atoms_ty T ++ atoms_tm t1
  | tm_app t1 t2 => atoms_tm t1 ++ atoms_tm t2
  | tm_tabs t1 => atoms_tm t1
  | tm_tapp t1 T => atoms_tm t1 ++ atoms_ty T
  | tm_if t1 t2 t3 => atoms_tm t1 ++ atoms_tm t2 ++ atoms_tm t3
  end.

Fixpoint atoms_ctx (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (x,T) :: Gamma' => x :: atoms_ty T ++ atoms_ctx Gamma'
  end.

Definition fresh_atom (xs : list atom) : atom :=
  S (fold_right Nat.max 0 xs).

Lemma in_le_fold : forall y xs, In y xs -> y <= fold_right Nat.max 0 xs.
Proof.
  intros y xs. induction xs as [|x xs IH]; simpl; intros H; [contradiction|].
  destruct H as [<-|H].
  - apply Nat.le_max_l.
  - eapply Nat.le_trans; [apply IH; exact H|apply Nat.le_max_r].
Qed.

Lemma open_ty_rec_lc : forall k U T,
    lc_ty_at k T -> open_ty_rec k U T = T.
Proof.
  intros k U T H. revert k U H. induction T; intros k U H; inversion H; simpl;
    try reflexivity.
  - destruct (Nat.eqb k n) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - f_equal; eauto.
  - f_equal; eauto.
Qed.

Lemma lc_tm_at_weaken : forall K k t,
    lc_tm_at K k t -> forall k', k <= k' -> lc_tm_at K k' t.
Proof.
  intros K k t H. induction H; intros k' Hk; simpl;
    try solve [constructor; eauto; lia].
  all: constructor; eauto; try (apply IHlc_tm_at; lia).
Qed.

Lemma lc_ty_at_weaken : forall K T,
    lc_ty_at K T -> forall K', K <= K' -> lc_ty_at K' T.
Proof.
  intros K T H. induction H; intros K' HK; try solve [constructor; eauto; lia].
  all: constructor; eauto; try (apply IHlc_ty_at; lia).
Qed.

Lemma lc_tm_at_weaken_K : forall K k t,
    lc_tm_at K k t -> forall K', K <= K' -> lc_tm_at K' k t.
Proof.
  intros K k t H. induction H; intros K' HK; simpl.
  all: try solve [constructor; eauto; lia].
  all: constructor.
  all: try eauto using lc_ty_at_weaken.
  all: try (eapply IHlc_tm_at; lia).
Qed.

Lemma open_tm_rec_lc : forall K k u t,
    lc_tm_at K k t ->
    lc_tm_at K k u -> open_tm_rec k u t = t.
Proof.
  intros K k u t. revert K k u.
  induction t as [i|x|T t IH|t1 IH1 t2 IH2|t IH|t IH T| | |t1 IH1 t2 IH2 t3 IH3];
    intros K k u Ht Hu; simpl.
  - inversion Ht. destruct (Nat.eqb k i) eqn:E;
      [apply Nat.eqb_eq in E; lia|reflexivity].
  - reflexivity.
  - inversion Ht. f_equal.
    apply IH with (K:=K) (k:=S k); [assumption|].
    eapply lc_tm_at_weaken; [exact Hu|lia].
  - inversion Ht. f_equal; [apply IH1 with (K:=K)|apply IH2 with (K:=K)]; assumption.
  - inversion Ht. f_equal.
    apply IH with (K:=S K); [assumption|].
    eapply lc_tm_at_weaken_K; [exact Hu|lia].
  - inversion Ht. f_equal. apply IH with (K:=K); assumption.
  - reflexivity.
  - reflexivity.
  - inversion Ht. f_equal; [apply IH1 with (K:=K)|apply IH2 with (K:=K)|apply IH3 with (K:=K)]; assumption.
Qed.

Lemma inst_ty_open_rec : forall theta k U T,
    (forall j X, k <= j -> lc_ty_at j (theta X)) ->
    inst_ty theta (open_ty_rec k U T) =
    open_ty_rec k (inst_ty theta U) (inst_ty theta T).
Proof.
  intros theta k U T. revert k U. induction T; intros k U H; simpl;
    try reflexivity.
  - destruct (Nat.eqb k n); reflexivity.
  - rewrite (open_ty_rec_lc k (inst_ty theta U) (theta a)).
    + reflexivity.
    + apply H; lia.
  - rewrite (IHT1 k U H), (IHT2 k U H). reflexivity.
  - f_equal. apply IHT; intros j X Hj. apply H; lia.
Qed.

Lemma inst_tm_ty_open_rec : forall theta k U t,
    (forall j X, k <= j -> lc_ty_at j (theta X)) ->
    inst_tm_ty theta (open_tm_ty_rec k U t) =
    open_tm_ty_rec k (inst_ty theta U) (inst_tm_ty theta t).
Proof.
  intros theta k U t. revert k U. induction t as
    [i|x|T t IH|t1 IH1 t2 IH2|t IH|t IH T| | |t1 IH1 t2 IH2 t3 IH3];
    intros k U H; simpl.
  - destruct (Nat.eqb k i); reflexivity.
  - reflexivity.
  - f_equal.
    + apply inst_ty_open_rec; intros; apply H; lia.
    + apply IH; exact H.
  - f_equal; [apply IH1; exact H|apply IH2; exact H].
  - f_equal. apply IH; intros; apply H; lia.
  - f_equal.
    + apply IH; exact H.
    + apply inst_ty_open_rec; intros; apply H; lia.
  - reflexivity.
  - reflexivity.
  - f_equal; [apply IH1; exact H|apply IH2; exact H|apply IH3; exact H].
Qed.

Lemma inst_tm_open_rec : forall sigma k u t,
    (forall K k', lc_tm_at K k' (inst_tm sigma u)) ->
    (forall x K k', lc_tm_at K k' (sigma x)) ->
    inst_tm sigma (open_tm_rec k u t) =
    open_tm_rec k (inst_tm sigma u) (inst_tm sigma t).
Proof.
  intros sigma k u t. revert k u. induction t as
    [i|x|T t IH|t1 IH1 t2 IH2|t IH|t IH T| | |t1 IH1 t2 IH2 t3 IH3];
    intros k u Hu Hs; simpl.
  - destruct (Nat.eqb k i); reflexivity.
  - rewrite (open_tm_rec_lc 0 k (inst_tm sigma u) (sigma x)
               (Hs x 0 k) (Hu 0 k)); reflexivity.
  - f_equal. apply IH; assumption.
  - f_equal; [apply IH1|apply IH2]; assumption.
  - f_equal. apply IH; assumption.
  - f_equal. apply IH; assumption.
  - reflexivity.
  - reflexivity.
  - f_equal; [apply IH1|apply IH2|apply IH3]; assumption.
Qed.

Lemma inst_tm_open : forall sigma t (u : tm),
    (forall K k, lc_tm_at K k (inst_tm sigma u)) ->
    (forall x K k, lc_tm_at K k (sigma x)) ->
    inst_tm sigma (open_tm t u) = open_tm (inst_tm sigma t) (inst_tm sigma u).
Proof. intros; apply inst_tm_open_rec; assumption. Qed.

Lemma inst_tm_ty_open : forall theta t U,
    (forall j X, 0 <= j -> lc_ty_at j (theta X)) ->
    inst_tm_ty theta (open_tm_ty t U) =
    open_tm_ty (inst_tm_ty theta t) (inst_ty theta U).
Proof. intros; apply inst_tm_ty_open_rec; exact H. Qed.

Lemma evaluates_value : forall t v, evaluates t v -> value v.
Proof.
  intros t v H. induction H; eauto.
Qed.

Lemma multi_trans : forall x y z, multi x y -> multi y z -> multi x z.
Proof.
  intros x y z Hxy Hyz. induction Hxy; eauto using multi.
Qed.

Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof.
  intros v H. destruct H as [T t H|t H| |].
  - exact H.
  - exact H.
  - unfold locally_closed_tm. constructor.
  - unfold locally_closed_tm. constructor.
Qed.

Lemma evaluates_lc : forall t v, evaluates t v ->
    locally_closed_tm t /\ locally_closed_tm v.
Proof.
  intros t v H. induction H as
    [v Hv|f arg U body v result Hf IHf Ha IHa Hb IHb|
     f U body result Hf IHf HU Hb IHb|
     c t u v Hc IHc Ht IHt Hu|
     c t u v Hc IHc Ht Hu IHu].
  - split; apply value_lc; assumption.
  - destruct IHf as [Hf1 Hf2], IHa as [Ha1 Ha2], IHb as [Hb1 Hb2].
    split; [constructor; assumption|assumption].
  - destruct IHf as [Hf1 Hf2], IHb as [Hb1 Hb2].
    split; [constructor; assumption|assumption].
  - destruct IHc as [Hc1 Hc2], IHt as [Ht1 Ht2].
    split; [constructor; assumption|assumption].
  - destruct IHc as [Hc1 Hc2], IHu as [Hu1 Hu2].
    split; [constructor; assumption|assumption].
Qed.

Lemma multi_app1 : forall f f' a,
    multi f f' -> locally_closed_tm a ->
    multi (tm_app f a) (tm_app f' a).
Proof.
  intros f f' a H. induction H as [x|x y z Hstep IH]; intros Ha.
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_App1; [exact Hstep|exact Ha].
    + apply IHIH; assumption.
Qed.

Lemma multi_app2 : forall v a a',
    value v -> multi a a' ->
    multi (tm_app v a) (tm_app v a').
Proof.
  intros v a a' Hv H. induction H as [x|x y z Hstep IH]; intros.
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_App2; [exact Hv|exact Hstep].
    + apply IHIH; assumption.
Qed.

Lemma multi_tapp : forall t t' U,
    multi t t' -> locally_closed_ty U ->
    multi (tm_tapp t U) (tm_tapp t' U).
Proof.
  intros t t' U H HU. induction H as [x|x y z Hstep IH].
  - apply multi_refl.
  - eapply multi_step; [apply ST_TApp; [exact Hstep|exact HU]|apply IHIH].
Qed.

Lemma multi_if1 : forall c c' t u,
    multi c c' -> locally_closed_tm t -> locally_closed_tm u ->
    multi (tm_if c t u) (tm_if c' t u).
Proof.
  intros c c' t u H. induction H as [x|x y z Hstep IH]; intros Ht Hu.
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_If; [exact Hstep|exact Ht|exact Hu].
    + apply IHIH; assumption.
Qed.

Lemma evaluates_multi : forall t v, evaluates t v -> multi t v.
Proof.
  intros t v H. induction H as
    [v Hv|f arg U body v result Hf IHf Ha IHa Hb IHb|
     f U body result Hf IHf HU Hb IHb|
     c t u v Hc IHc Ht IHt Hu|
     c t u v Hc IHc Ht Hu IHu].
  - constructor.
  - destruct (evaluates_lc _ _ Ha) as [Ha1 Ha2].
    assert (value (tm_abs U body)) as Hvabs by
      (apply evaluates_value with (t:=f); exact Hf).
    refine (multi_trans _ _ _ (multi_app1 _ _ _ IHf Ha1) _).
    refine (multi_trans _ _ _ (multi_app2 _ _ _ Hvabs IHa) _).
    assert (value v) as Hv by (apply evaluates_value with (t:=arg); exact Ha).
    refine (multi_step _ _ _ _ IHb).
    apply ST_AppAbs; [apply value_lc; exact Hvabs|exact Hv].
  - assert (value (tm_tabs body)) as Hvtab by
      (apply evaluates_value with (t:=f); exact Hf).
    refine (multi_trans _ _ _ (multi_tapp _ _ _ IHf HU) _).
    refine (multi_step _ _ _ _ IHb).
    apply ST_TAppTabs; [apply value_lc; exact Hvtab|exact HU].
  - destruct (evaluates_lc _ _ Ht) as [Ht1 Ht2].
    refine (multi_trans _ _ _ (multi_if1 _ _ _ _ IHc Ht1 Hu) _).
    refine (multi_step _ _ _ _ IHt). eapply ST_IfTrue; eauto.
  - destruct (evaluates_lc _ _ Hu) as [Hu1 Hu2].
    refine (multi_trans _ _ _ (multi_if1 _ _ _ _ IHc Ht Hu1) _).
    refine (multi_step _ _ _ _ IHu). eapply ST_IfFalse; eauto.
Qed.

Lemma expr_abs : forall eta rho T1 T2 U1 U2 b1 b2,
    locally_closed_tm (tm_abs U1 b1) -> locally_closed_tm (tm_abs U2 b2) ->
    (forall a1 a2, value_relation eta rho T1 a1 a2 ->
      expression_lifting (value_relation eta rho T2)
        (open_tm b1 a1) (open_tm b2 a2)) ->
    expression_relation eta rho (Ty_Arrow T1 T2)
      (tm_abs U1 b1) (tm_abs U2 b2).
Proof.
  intros eta rho T1 T2 U1 U2 b1 b2 Hlc1 Hlc2 H.
  assert (value (tm_abs U1 b1)) as Hv1 by (constructor; exact Hlc1).
  assert (value (tm_abs U2 b2)) as Hv2 by (constructor; exact Hlc2).
  split; [exact Hlc1|]. split; [exact Hlc2|].
  exists (tm_abs U1 b1), (tm_abs U2 b2).
  split; [constructor; exact Hv1|]. split; [constructor; exact Hv2|].
  simpl. refine (conj Hv1 (conj Hv2 _)).
  exists U1, b1, U2, b2.
  split; [reflexivity|]. split; [reflexivity|exact H].
Qed.

Lemma expr_tabs : forall eta rho T b1 b2,
    locally_closed_tm (tm_tabs b1) -> locally_closed_tm (tm_tabs b2) ->
    (forall U1 U2 a, locally_closed_ty U1 -> locally_closed_ty U2 ->
      expression_lifting (value_relation (a :: eta) rho T)
        (open_tm_ty b1 U1) (open_tm_ty b2 U2)) ->
    expression_relation eta rho (Ty_All T)
      (tm_tabs b1) (tm_tabs b2).
Proof.
  intros eta rho T b1 b2 Hlc1 Hlc2 H.
  assert (value (tm_tabs b1)) as Hv1 by (constructor; exact Hlc1).
  assert (value (tm_tabs b2)) as Hv2 by (constructor; exact Hlc2).
  split; [exact Hlc1|]. split; [exact Hlc2|].
  exists (tm_tabs b1), (tm_tabs b2).
  split; [constructor; exact Hv1|]. split; [constructor; exact Hv2|].
  simpl. refine (conj Hv1 (conj Hv2 _)).
  exists b1, b2.
  split; [reflexivity|]. split; [reflexivity|exact H].
Qed.

Lemma value_relation_values : forall eta rho T v1 v2,
    value_relation eta rho T v1 v2 -> value v1 /\ value v2.
Proof.
  intros eta rho T. induction T as [i|X|T1 IH1 T2 IH2|T IH|]; intros v1 v2 H.
  - destruct (nth_error eta i) as [a|] eqn:E in H.
    + cbn [value_relation] in H. rewrite E in H. exact (candidate_values a v1 v2 H).
    + cbn [value_relation] in H. rewrite E in H. contradiction.
  - destruct (rho X) as [a|] eqn:E in H.
    + cbn [value_relation] in H. rewrite E in H. exact (candidate_values a v1 v2 H).
    + cbn [value_relation] in H. rewrite E in H. contradiction.
  - simpl in H; intuition.
  - simpl in H; intuition.
  - simpl in H; destruct H as [[-> ->]|[-> ->]]; split; constructor.
Qed.

Lemma expr_var : forall eta rho T t1 t2,
    value_relation eta rho T t1 t2 ->
    expression_relation eta rho T t1 t2.
Proof.
  intros eta rho T t1 t2 H. destruct (value_relation_values _ _ _ _ _ H) as [H1 H2].
  split; [apply value_lc; exact H1|]. split; [apply value_lc; exact H2|].
  exists t1, t2. split; [constructor; exact H1|].
  split; [constructor; exact H2|exact H].
Qed.

Lemma expr_app : forall eta rho T1 T2 f1 f2 a1 a2,
    expression_relation eta rho (Ty_Arrow T1 T2) f1 f2 ->
    expression_relation eta rho T1 a1 a2 ->
    expression_relation eta rho T2 (tm_app f1 a1) (tm_app f2 a2).
Proof.
  intros eta rho T1 T2 f1 f2 a1 a2 Hf Ha.
  destruct Hf as [Hlf1 [Hlf2 [vf1 [vf2 [Evf1 [Evf2 Rf]]]]]].
  destruct Ha as [Hla1 [Hla2 [va1 [va2 [Eva1 [Eva2 Ra]]]]]].
  simpl in Rf. destruct Rf as [Hvf1 [Hvf2 [U1 [b1 [U2 [b2 [-> [-> Hb]]]]]]]].
  pose proof (evaluates_value _ _ Evf1) as Hv1.
  pose proof (evaluates_value _ _ Evf2) as Hv2.
  specialize (Hb va1 va2 Ra).
  destruct Hb as [Hlb1 [Hlb2 [vr1 [vr2 [Evb1 [Evb2 Rb]]]]]].
  repeat split; [constructor; assumption|constructor; assumption|].
  exists vr1, vr2. repeat split; eauto using EvalApp.
Qed.

Lemma expr_tapp : forall eta rho T f1 f2 U1 U2,
    expression_relation eta rho (Ty_All T) f1 f2 ->
    locally_closed_ty U1 -> locally_closed_ty U2 ->
    (forall x y, value_relation
       ({| candidate_relation := value_relation eta rho U1;
          candidate_values := (fun p q H => value_relation_values _ _ _ _ _ H) |} :: eta)
       rho T x y -> value_relation eta rho (open_ty T U1) x y) ->
    expression_relation eta rho (open_ty T U1)
      (tm_tapp f1 U1) (tm_tapp f2 U2).
Proof.
  intros eta rho T f1 f2 U1 U2 Hf HU1 HU2 Hconv.
  destruct Hf as [Hlf1 [Hlf2 [vf1 [vf2 [Evf1 [Evf2 Rf]]]]]].
  simpl in Rf. destruct Rf as [Hfv1 [Hfv2 [b1 [b2 [-> [-> Hb]]]]]].
  pose proof (evaluates_value _ _ Evf1) as Hv1.
  pose proof (evaluates_value _ _ Evf2) as Hv2.
  specialize (Hb U1 U2 {| candidate_relation := value_relation eta rho U1;
    candidate_values := (fun x y H => (value_relation_values _ _ _ _ _ H)) |} HU1 HU2).
  destruct Hb as [Hlb1 [Hlb2 [vr1 [vr2 [Evb1 [Evb2 Rb]]]]]].
  specialize (Hconv vr1 vr2 Rb).
  repeat split; [constructor; assumption|constructor; assumption|].
  exists vr1, vr2; repeat split; eauto using EvalTApp.
Qed.

Lemma expr_if : forall eta rho T c1 c2 t1 t2 u1 u2,
    expression_relation eta rho Ty_Bool c1 c2 ->
    expression_relation eta rho T t1 t2 ->
    expression_relation eta rho T u1 u2 ->
    expression_relation eta rho T (tm_if c1 t1 u1) (tm_if c2 t2 u2).
Proof.
  intros eta rho T c1 c2 t1 t2 u1 u2 Hc Ht Hu.
  destruct Hc as [Hlc1 [Hlc2 [vc1 [vc2 [Evc1 [Evc2 Rc]]]]]].
  destruct Ht as [Hlt1 [Hlt2 [vt1 [vt2 [Evt1 [Evt2 Rt]]]]]].
  destruct Hu as [Hlu1 [Hlu2 [vu1 [vu2 [Evu1 [Evu2 Ru]]]]]].
  destruct Rc as [[-> ->]|[-> ->]].
  - repeat split; [constructor; assumption|constructor; assumption|].
    exists vt1, vt2; repeat split; eauto using EvalIfTrue.
  - repeat split; [constructor; assumption|constructor; assumption|].
    exists vu1, vu2; repeat split; eauto using EvalIfFalse.
Qed.

Lemma fresh_atom_notin : forall xs, ~ In (fresh_atom xs) xs.
Proof.
  intros xs Hin.
  unfold fresh_atom in *.
  pose proof (in_le_fold (S (fold_right Nat.max 0 xs)) xs Hin).
  lia.
Qed.

Lemma fresh_atom_notin_app : forall xs ys,
    ~ In (fresh_atom (xs ++ ys)) xs /\
    ~ In (fresh_atom (xs ++ ys)) ys.
Proof.
  intros xs ys. split; intro H.
  - apply (fresh_atom_notin (xs ++ ys)).
    apply in_or_app. now left.
  - apply (fresh_atom_notin (xs ++ ys)).
    apply in_or_app. now right.
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
  intros t H U v HU Hv Hvty.
  inversion H.
Qed.

End SystemFParametricityIfMediumTask.
