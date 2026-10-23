(** System F parametricity benchmark, Medium variant.
    Features: recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFParametricityRecursionMediumTask.

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


Hint Constructors lc_ty_at lc_tm_at value : core.

Inductive evaluates : tm -> tm -> Prop :=
  | EvalValue : forall v, value v -> evaluates v v
  | EvalApp : forall f arg U body v result,
      evaluates f (tm_abs U body) -> evaluates arg v ->
      evaluates (open_tm body v) result -> evaluates (tm_app f arg) result
  | EvalTApp : forall f U body result,
      evaluates f (tm_tabs body) -> locally_closed_ty U ->
      evaluates (open_tm_ty body U) result -> evaluates (tm_tapp f U) result
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
  | Ty_Nat => v1 = v2 /\ numeric_value v1
  end.

Definition expression_relation eta rho T t1 t2 :=
  expression_lifting (value_relation eta rho T) t1 t2.

(* Closing substitutions.  The two type substitutions are deliberately kept
   separate: related type arguments need not be the same type. *)
Definition ty_subst_env := atom -> ty.
Definition tm_subst_env := atom -> tm.

Definition ty_env_update (theta : ty_subst_env) (X : atom) (U : ty) : ty_subst_env :=
  fun Y => if Nat.eqb X Y then U else theta Y.
Definition tm_env_update (sigma : tm_subst_env) (x : atom) (u : tm) : tm_subst_env :=
  fun y => if Nat.eqb x y then u else sigma y.

Fixpoint ty_inst (theta : ty_subst_env) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => theta X
  | Ty_Arrow T1 T2 => Ty_Arrow (ty_inst theta T1) (ty_inst theta T2)
  | Ty_All T1 => Ty_All (ty_inst theta T1)
  | Ty_Nat => Ty_Nat
  end.

Fixpoint tm_tinst (theta : ty_subst_env) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T t1 => tm_abs (ty_inst theta T) (tm_tinst theta t1)
  | tm_app t1 t2 => tm_app (tm_tinst theta t1) (tm_tinst theta t2)
  | tm_tabs t1 => tm_tabs (tm_tinst theta t1)
  | tm_tapp t1 T => tm_tapp (tm_tinst theta t1) (ty_inst theta T)
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (tm_tinst theta t1)
  | tm_natrec n b s => tm_natrec (tm_tinst theta n) (tm_tinst theta b) (tm_tinst theta s)
  end.

Fixpoint tm_inst (sigma : tm_subst_env) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_abs T t1 => tm_abs T (tm_inst sigma t1)
  | tm_app t1 t2 => tm_app (tm_inst sigma t1) (tm_inst sigma t2)
  | tm_tabs t1 => tm_tabs (tm_inst sigma t1)
  | tm_tapp t1 T => tm_tapp (tm_inst sigma t1) T
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (tm_inst sigma t1)
  | tm_natrec n b s => tm_natrec (tm_inst sigma n) (tm_inst sigma b) (tm_inst sigma s)
  end.

Definition close_tm (theta : ty_subst_env) (sigma : tm_subst_env) (t : tm) : tm :=
  tm_inst sigma (tm_tinst theta t).

Fixpoint ty_fvars (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow T1 T2 => ty_fvars T1 ++ ty_fvars T2
  | Ty_All T1 => ty_fvars T1
  | Ty_Nat => []
  end.

Fixpoint tm_fvars (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs T t1 => ty_fvars T ++ tm_fvars t1
  | tm_app t1 t2 => tm_fvars t1 ++ tm_fvars t2
  | tm_tabs t1 => tm_fvars t1
  | tm_tapp t1 T => tm_fvars t1 ++ ty_fvars T
  | tm_zero => []
  | tm_succ t1 => tm_fvars t1
  | tm_natrec n b s => tm_fvars n ++ tm_fvars b ++ tm_fvars s
  end.

Lemma fresh_not_in : forall xs : list atom, exists x, ~ In x xs.
Proof.
  assert (bound : forall xs n, In n xs -> n <= fold_right Nat.max 0 xs).
  { induction xs as [|x xs IH]; intros n H; simpl in *.
    - contradiction.
    - destruct H as [->|H].
      + apply Nat.le_max_l.
      + specialize (IH n H). lia. }
  intro xs. exists (S (fold_right Nat.max 0 xs)). intro H.
  specialize (bound xs (S (fold_right Nat.max 0 xs)) H). lia.
Qed.

Lemma value_relation_values : forall eta rho T v1 v2,
  value_relation eta rho T v1 v2 -> value v1 /\ value v2.
Proof.
  intros eta rho T v1 v2 H; induction T; simpl in H.
  - destruct (nth_error eta n) as [c|] eqn:E; [apply c.(candidate_values) in H; exact H|contradiction].
  - destruct (rho a) as [c|] eqn:E; [apply c.(candidate_values) in H; exact H|contradiction].
  - tauto.
  - tauto.
  - destruct H as [-> Hn]. split; apply v_nat; assumption.
Qed.

Lemma evaluates_value : forall t v, evaluates t v -> value v.
Proof.
  intros t v H; induction H; eauto.
  - apply v_nat. apply nv_succ. assumption.
Qed.

Lemma numeric_value_lc : forall n, numeric_value n -> locally_closed_tm n.
Proof.
  intros n H; induction H as [|n H IH].
  - apply lc_tm_zero.
  - apply lc_tm_succ. exact IH.
Qed.

Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof.
  intros v H; inversion H; eauto using numeric_value_lc.
Qed.

Lemma evaluates_lc : forall t v, evaluates t v -> locally_closed_tm t.
Proof.
  intros t v H.
  induction H as
    [v Hv
    |f arg U body v result Hf IHf Ha IHa Hb IHb
    |f U body result Hf IHf HU Hb IHb
    |t n Ht IH Hn
    |n b s vb vs Hn IHn Hb IHb Hs IHs
    |n b s k vb vs result Hn IHn Hk Hb IHb Hs IHs Happ IHapp].
  - apply value_lc; assumption.
  - apply lc_tm_app; assumption.
  - apply lc_tm_tapp; assumption.
  - apply lc_tm_succ; assumption.
  - apply lc_tm_rec; assumption.
  - apply lc_tm_rec; assumption.
Qed.

Lemma multi_trans : forall x y z, x -->* y -> y -->* z -> x -->* z.
Proof.
  intros x y z H1 H2; induction H1; eauto using multi_step.
Qed.

Lemma multi_app1 : forall t t' a, t -->* t' -> locally_closed_tm a ->
  tm_app t a -->* tm_app t' a.
Proof.
  intros t t' a H; induction H as [t|t t' t'' H IH]; intros Ha.
  - constructor.
  - eapply multi_step.
    + apply ST_App1; [exact H|exact Ha].
    + apply IHIH; exact Ha.
Qed.

Lemma multi_app2 : forall v t t', value v -> t -->* t' ->
  tm_app v t -->* tm_app v t'.
Proof.
  intros v t t' Hv H; induction H as [t|t t' t'' H IH].
  - constructor.
  - eapply multi_step.
    + apply ST_App2; [exact Hv|exact H].
    + apply IHIH.
Qed.

Lemma multi_tapp : forall t t' U, t -->* t' -> locally_closed_ty U ->
  tm_tapp t U -->* tm_tapp t' U.
Proof.
  intros t t' U H; induction H as [t|t t' t'' H IH]; intros HU.
  - constructor.
  - eapply multi_step.
    + apply ST_TApp; [exact H|exact HU].
    + apply IHIH; exact HU.
Qed.

Lemma multi_succ : forall t t', t -->* t' -> tm_succ t -->* tm_succ t'.
Proof.
  intros t t' H; induction H as [t|t t' t'' H IH].
  - constructor.
  - eapply multi_step.
    + apply ST_Succ; exact H.
    + apply IHIH.
Qed.

Lemma multi_rec_arg : forall n n' b s, n -->* n' -> locally_closed_tm b ->
  locally_closed_tm s -> tm_natrec n b s -->* tm_natrec n' b s.
Proof.
  intros n n' b s H; induction H as [n|n n' n'' H IH]; intros Hb Hs.
  - constructor.
  - eapply multi_step.
    + apply ST_RecArg; [exact H|exact Hb|exact Hs].
    + apply IHIH; assumption.
Qed.

Lemma multi_rec_base : forall n b b' s, numeric_value n -> b -->* b' ->
  locally_closed_tm s -> tm_natrec n b s -->* tm_natrec n b' s.
Proof.
  intros n b b' s Hn H; induction H as [b|b b' b'' H IH]; intros Hs.
  - constructor.
  - eapply multi_step.
    + apply ST_RecBase; [exact Hn|exact H|exact Hs].
    + apply IHIH; assumption.
Qed.

Lemma multi_rec_step : forall n b s s', numeric_value n -> value b ->
  s -->* s' -> tm_natrec n b s -->* tm_natrec n b s'.
Proof.
  intros n b s s' Hn Hb H; induction H as [s|s s' s'' H IH].
  - constructor.
  - eapply multi_step.
    + apply ST_RecStep; [exact Hn|exact Hb|exact H].
    + apply IHIH.
Qed.

Lemma evaluates_multi : forall t v, evaluates t v -> t -->* v.
Proof.
  intros t v H; induction H.
  - constructor.
  - eapply multi_trans.
    + apply multi_app1; [exact IHevaluates1|apply evaluates_lc with (t:=arg) (v:=v); exact H0].
    + eapply multi_trans.
      * apply multi_app2; [apply evaluates_value with (t:=f) (v:=tm_abs U body); exact H|exact IHevaluates2].
      * eapply multi_step.
        { apply ST_AppAbs.
          - apply value_lc. apply evaluates_value with (t:=f) (v:=tm_abs U body). exact H.
          - apply evaluates_value with (t:=arg) (v:=v). exact H0. }
        exact IHevaluates3.
  - eapply multi_trans.
    + apply multi_tapp; [exact IHevaluates1|exact H0].
    + eapply multi_step.
      { apply ST_TAppTabs.
        - apply value_lc. apply evaluates_value with (t:=f) (v:=tm_tabs body). exact H.
        - exact H0. }
      exact IHevaluates2.
  - apply multi_succ. exact IHevaluates.
  - eapply multi_trans.
    + apply multi_rec_arg; [exact IHevaluates1|apply evaluates_lc with (t:=b) (v:=vb); exact H0|apply evaluates_lc with (t:=s) (v:=vs); exact H1].
    + eapply multi_trans.
      * apply multi_rec_base; [apply nv_zero|exact IHevaluates2|apply evaluates_lc with (t:=s) (v:=vs); exact H1].
      * eapply multi_trans.
        -- apply multi_rec_step; [apply nv_zero|apply evaluates_value with (t:=b) (v:=vb); exact H0|exact IHevaluates3].
        -- eapply multi_step. apply ST_RecZero.
           ++ apply evaluates_value with (t:=b) (v:=vb); exact H0.
           ++ apply evaluates_value with (t:=s) (v:=vs); exact H1.
           ++ constructor.
  - eapply multi_trans.
    + apply multi_rec_arg; [exact IHevaluates1|apply evaluates_lc with (t:=b) (v:=vb); exact H1|apply evaluates_lc with (t:=s) (v:=vs); exact H2].
    + eapply multi_trans.
      * apply multi_rec_base; [apply nv_succ; exact H0|exact IHevaluates2|apply evaluates_lc with (t:=s) (v:=vs); exact H2].
      * eapply multi_trans.
        -- apply multi_rec_step; [apply nv_succ; exact H0|apply evaluates_value with (t:=b) (v:=vb); exact H1|exact IHevaluates3].
        -- eapply multi_step.
           ++ apply ST_RecSucc.
              ** exact H0.
              ** apply evaluates_value with (t:=b) (v:=vb); exact H1.
              ** apply evaluates_value with (t:=s) (v:=vs); exact H2.
           ++ exact IHevaluates4.
Qed.

Lemma open_ty_rec_lc : forall k U T, lc_ty_at k T ->
  open_ty_rec k U T = T.
Proof.
  intros k U T H; induction H; simpl.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + reflexivity.
  - reflexivity.
  - rewrite IHlc_ty_at1, IHlc_ty_at2; reflexivity.
  - rewrite IHlc_ty_at; reflexivity.
  - reflexivity.
Qed.

Lemma lc_ty_at_mono : forall k k' T, k <= k' ->
  lc_ty_at k T -> lc_ty_at k' T.
Proof.
  intros k k' T Hkk' H. revert k' Hkk'. induction H; intros k' Hkk'.
  - apply lc_ty_bvar. lia.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; eauto.
  - apply lc_ty_all. apply IHlc_ty_at. lia.
  - apply lc_ty_nat.
Qed.

Lemma ty_inst_open_ty_rec : forall theta X U T k,
  ~ In X (ty_fvars T) ->
  (forall Y, locally_closed_ty (theta Y)) ->
  ty_inst (ty_env_update theta X U) (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k U (ty_inst theta T).
Proof.
  intros theta X U T k. revert k.
  induction T as [i|Y|T1 IH1 T2 IH2|T IH|]; simpl; intros k H Hlc; try reflexivity.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst i. simpl. unfold ty_env_update. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - destruct (Nat.eqb_spec X Y) as [->|Hxy].
    + exact (False_rect _ (H (or_introl eq_refl))).
    + unfold ty_env_update. destruct (Nat.eqb X Y) eqn:E.
      * apply Nat.eqb_eq in E. contradiction.
      * assert (HlcY : lc_ty_at k (theta Y)).
        { unfold locally_closed_ty. apply (lc_ty_at_mono 0 k (theta Y)); [lia|apply Hlc]. }
        rewrite (open_ty_rec_lc k U (theta Y) HlcY). reflexivity.
  - rewrite (IH1 k ltac:(simpl in H; intuition) Hlc),
      (IH2 k ltac:(simpl in H; intuition) Hlc); reflexivity.
  - rewrite (IH (S k) H Hlc); reflexivity.
Qed.

Lemma ty_inst_open_ty : forall theta X U T,
  ~ In X (ty_fvars T) ->
  (forall Y, locally_closed_ty (theta Y)) ->
  ty_inst (ty_env_update theta X U) (open_ty T (Ty_FVar X)) =
  open_ty (ty_inst theta T) U.
Proof.
  intros. unfold open_ty. apply ty_inst_open_ty_rec; assumption.
Qed.

Lemma tm_tinst_open_tm_ty_rec : forall theta X U t k,
  ~ In X (tm_fvars t) ->
  (forall Y, locally_closed_ty (theta Y)) ->
  tm_tinst (ty_env_update theta X U) (open_tm_ty_rec k (Ty_FVar X) t) =
  open_tm_ty_rec k U (tm_tinst theta t).
Proof.
  intros theta X U t k. revert k.
  induction t as [i|x|T t IH|t1 IH1 t2 IH2|t IH|t IH T| |t IH|n IHn b IHb s IHs];
    simpl; intros k H Hlc; try reflexivity.
  - f_equal.
    + apply ty_inst_open_ty_rec; [simpl in H; intuition|exact Hlc].
    + apply IH; [simpl in H; intuition|exact Hlc].
  - rewrite (IH1 k ltac:(simpl in H; intuition) Hlc),
      (IH2 k ltac:(simpl in H; intuition) Hlc); reflexivity.
  - apply f_equal. apply IH; [simpl in H; intuition|exact Hlc].
  - rewrite (IH k ltac:(simpl in H; intuition) Hlc).
    f_equal. apply ty_inst_open_ty_rec; [simpl in H; intuition|exact Hlc].
  - rewrite (IH k H Hlc); reflexivity.
  - assert (Hn : ~ In X (tm_fvars n)).
    { intro Hn. apply H. apply in_or_app. left. exact Hn. }
    assert (Hb : ~ In X (tm_fvars b)).
    { intro Hb. apply H. apply in_or_app. right. apply in_or_app. left. exact Hb. }
    assert (Hs : ~ In X (tm_fvars s)).
    { intro Hs. apply H. apply in_or_app. right. apply in_or_app. right. exact Hs. }
    rewrite (IHn k Hn Hlc), (IHb k Hb Hlc), (IHs k Hs Hlc); reflexivity.
Qed.

Lemma tm_tinst_open_tm_ty : forall theta X U t,
  ~ In X (tm_fvars t) ->
  (forall Y, locally_closed_ty (theta Y)) ->
  tm_tinst (ty_env_update theta X U) (open_tm_ty t (Ty_FVar X)) =
  open_tm_ty (tm_tinst theta t) U.
Proof.
  intros. unfold open_tm_ty. apply tm_tinst_open_tm_ty_rec; assumption.
Qed.

Lemma open_tm_rec_lc : forall K k u t, lc_tm_at K k t ->
  open_tm_rec k u t = t.
Proof.
  intros K k u t H; induction H; simpl.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + reflexivity.
  - reflexivity.
  - rewrite IHlc_tm_at; reflexivity.
  - rewrite IHlc_tm_at1, IHlc_tm_at2; reflexivity.
  - rewrite IHlc_tm_at; reflexivity.
  - rewrite IHlc_tm_at; reflexivity.
  - reflexivity.
  - rewrite IHlc_tm_at; reflexivity.
  - rewrite IHlc_tm_at1, IHlc_tm_at2, IHlc_tm_at3; reflexivity.
Qed.

Lemma lc_tm_at_term_mono : forall K k k' t,
  k <= k' -> lc_tm_at K k t -> lc_tm_at K k' t.
Proof.
  intros K k k' t hk H. revert k' hk. induction H; intros k' hk.
  - apply lc_tm_bvar. lia.
  - apply lc_tm_fvar.
  - apply lc_tm_abs; [assumption|apply IHlc_tm_at; lia].
  - apply lc_tm_app; [apply IHlc_tm_at1|apply IHlc_tm_at2]; lia.
  - apply lc_tm_tabs. apply IHlc_tm_at. lia.
  - apply lc_tm_tapp; [apply IHlc_tm_at; lia|assumption].
  - apply lc_tm_zero.
  - apply lc_tm_succ. apply IHlc_tm_at. lia.
  - apply lc_tm_rec; [apply IHlc_tm_at1|apply IHlc_tm_at2|apply IHlc_tm_at3]; lia.
Qed.

Lemma lc_tm_at_type_mono : forall K K' k t,
  K <= K' -> lc_tm_at K k t -> lc_tm_at K' k t.
Proof.
  intros K K' k t HK H. revert K' HK. induction H; intros K' HK.
  - apply lc_tm_bvar; assumption.
  - apply lc_tm_fvar.
  - apply lc_tm_abs; [eapply lc_ty_at_mono; eauto|apply IHlc_tm_at; lia].
  - apply lc_tm_app; [apply IHlc_tm_at1|apply IHlc_tm_at2]; assumption.
  - apply lc_tm_tabs. apply IHlc_tm_at. lia.
  - apply lc_tm_tapp; [apply IHlc_tm_at; assumption|eapply lc_ty_at_mono; eauto].
  - apply lc_tm_zero.
  - apply lc_tm_succ. apply IHlc_tm_at. assumption.
  - apply lc_tm_rec; [apply IHlc_tm_at1|apply IHlc_tm_at2|apply IHlc_tm_at3]; assumption.
Qed.

Lemma lc_tm_at_mono : forall K K' k k' t,
  K <= K' -> k <= k' -> lc_tm_at K k t -> lc_tm_at K' k' t.
Proof.
  intros. eapply lc_tm_at_term_mono; [exact H0|].
  apply lc_tm_at_type_mono with (K := K); assumption.
Qed.

Lemma tm_inst_open_tm_rec : forall sigma x u t k,
  ~ In x (tm_fvars t) ->
  (forall y, locally_closed_tm (sigma y)) ->
  locally_closed_tm u ->
  tm_inst (tm_env_update sigma x u) (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k u (tm_inst sigma t).
Proof.
  intros sigma x u t k. revert k.
  induction t as [i|y|T t IHabs|t1 IHapp1 t2 IHapp2|tt IHtabs|tu IHtapp T| |ts IHsucc|n IHn b IHb s IHs];
    simpl; intros k H Hlc HLu.
  assert (HLu' : lc_tm_at 0 k u).
  { unfold locally_closed_tm in HLu. apply (lc_tm_at_term_mono 0 0 k u); [lia|exact HLu]. }
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst i. simpl. unfold tm_env_update. rewrite Nat.eqb_refl.
      reflexivity.
    + reflexivity.
  - destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. exact (False_rect _ (H (or_introl (eq_sym E)))).
    + apply Nat.eqb_neq in E. unfold tm_env_update. destruct (Nat.eqb x y) eqn:E'.
      * apply Nat.eqb_eq in E'. contradiction.
      * assert (Hlc' : lc_tm_at 0 k (sigma y)).
        { unfold locally_closed_tm. apply (lc_tm_at_term_mono 0 0 k (sigma y)); [lia|apply Hlc]. }
        rewrite (open_tm_rec_lc 0 k u (sigma y) Hlc'). reflexivity.
  - f_equal. apply IHabs; [simpl in H; intuition|exact Hlc|exact HLu].
  - rewrite (IHapp1 k ltac:(simpl in H; intuition) Hlc HLu),
      (IHapp2 k ltac:(simpl in H; intuition) Hlc HLu); reflexivity.
  - apply f_equal. apply IHtabs; [simpl in H; intuition|exact Hlc|exact HLu].
  - rewrite (IHtapp k ltac:(simpl in H; intuition) Hlc HLu); reflexivity.
  - reflexivity.
  - rewrite (IHsucc k ltac:(simpl in H; intuition) Hlc HLu); reflexivity.
  - assert (Hn : ~ In x (tm_fvars n)).
    { intro Hn. apply H. apply in_or_app. left. exact Hn. }
    assert (Hb : ~ In x (tm_fvars b)).
    { intro Hb. apply H. apply in_or_app. right. apply in_or_app. left. exact Hb. }
    assert (Hs : ~ In x (tm_fvars s)).
    { intro Hs. apply H. apply in_or_app. right. apply in_or_app. right. exact Hs. }
    rewrite (IHn k Hn Hlc HLu), (IHb k Hb Hlc HLu), (IHs k Hs Hlc HLu); reflexivity.
Qed.

Lemma tm_inst_open_tm : forall sigma x u t,
  ~ In x (tm_fvars t) ->
  (forall y, locally_closed_tm (sigma y)) ->
  locally_closed_tm u ->
  tm_inst (tm_env_update sigma x u) (open_tm t (tm_fvar x)) =
  open_tm (tm_inst sigma t) u.
Proof.
  intros. unfold open_tm. apply tm_inst_open_tm_rec; assumption.
Qed.

Lemma lc_tm_open_inv : forall K k t L,
  (forall x, ~ In x L ->
    lc_tm_at K k (open_tm_rec k (tm_fvar x) t)) ->
  lc_tm_at K (S k) t.
Proof.
  intros K k t L. revert K k L.
  induction t as [i|x|T t IH|t1 IH1 t2 IH2|t IH|tu IH T| |t IH|n IHn b IHb s IHs];
    intros K k L H.
  - destruct (Nat.eqb k i) eqn:E.
    + apply lc_tm_bvar. apply Nat.eqb_eq in E. lia.
    + apply lc_tm_bvar. apply Nat.eqb_neq in E.
      destruct (fresh_not_in L) as [x Hx].
      specialize (H x Hx). cbn [open_tm_rec] in H. destruct (Nat.eqb k i) eqn:E'.
      * apply Nat.eqb_eq in E'. contradiction.
      * assert (Hi : i < k).
        { simpl in H. inversion H; lia. }
        lia.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + destruct (fresh_not_in L) as [z Hz].
      pose proof (H z Hz) as Hzlc. simpl in Hzlc. inversion Hzlc; assumption.
    + apply IH with (L := L). intros x Hx. specialize (H x Hx). simpl in H. inversion H; assumption.
  - apply lc_tm_app; [apply IH1 with (L := L)|apply IH2 with (L := L)]; intros x Hx; specialize (H x Hx); simpl in H; inversion H; assumption.
  - apply lc_tm_tabs. apply IH with (L := L). intros x Hx. specialize (H x Hx). simpl in H; inversion H; assumption.
  - apply lc_tm_tapp.
    + apply IH with (L := L). intros x Hx. specialize (H x Hx). simpl in H; inversion H; assumption.
    + destruct (fresh_not_in L) as [z Hz].
      pose proof (H z Hz) as Hzlc. simpl in Hzlc. inversion Hzlc; assumption.
  - apply lc_tm_zero.
  - apply lc_tm_succ. apply IH with (L := L). intros x Hx. specialize (H x Hx). simpl in H; inversion H; assumption.
  - apply lc_tm_rec; [apply IHn with (L := L)|apply IHb with (L := L)|apply IHs with (L := L)]; intros x Hx; specialize (H x Hx); simpl in H; inversion H; assumption.
Qed.

Lemma lc_ty_open_rec_inv : forall K r T L,
  r < K ->
  (forall X, ~ In X L ->
    lc_ty_at K (open_ty_rec r (Ty_FVar X) T)) ->
  lc_ty_at K T.
Proof.
  intros K r T L. revert K r L.
  induction T as [i|Y|T1 IH1 T2 IH2|T IH|]; intros K r L Hr H.
  - destruct (Nat.eqb r i) eqn:E.
    + apply lc_ty_bvar. apply Nat.eqb_eq in E.
      destruct (fresh_not_in L) as [X HX]. specialize (H X HX).
      lia.
    + apply lc_ty_bvar. apply Nat.eqb_neq in E.
      destruct (fresh_not_in L) as [X HX]. specialize (H X HX).
      cbn [open_ty_rec] in H. destruct (Nat.eqb r i) eqn:E'.
      * apply Nat.eqb_eq in E'. contradiction.
      * simpl in H. inversion H; lia.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow.
    + apply IH1 with (r := r) (L := L); [exact Hr|]. intros X HX; specialize (H X HX); simpl in H; inversion H; assumption.
    + apply IH2 with (r := r) (L := L); [exact Hr|]. intros X HX; specialize (H X HX); simpl in H; inversion H; assumption.
  - apply lc_ty_all. apply IH with (r := S r) (L := L); [lia|].
    intros X HX. specialize (H X HX). simpl in H. inversion H; assumption.
  - apply lc_ty_nat.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T ->
  lc_ty_at (length Delta) T.
Proof.
  intros Delta T H.
  induction H as [Delta X HX|Delta T1 T2 H1 IH1 H2 IH2|L Delta T H IH|Delta].
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; assumption.
  - apply lc_ty_all. apply lc_ty_open_rec_inv with (r := 0) (L := L); [lia|].
    intros X HX. exact (IH X HX).
  - apply lc_ty_nat.
Qed.

Lemma ty_inst_lc : forall (theta : ty_subst_env) K T, lc_ty_at K T ->
  (forall X, locally_closed_ty (theta X)) ->
  lc_ty_at K (ty_inst theta T).
Proof.
  intros theta K T H. induction H as [k i Hi|k X|k T1 T2 H1 IH1 H2 IH2|k T H IH|k];
    intros Htheta; simpl.
  - apply lc_ty_bvar; assumption.
  - unfold locally_closed_ty in Htheta.
    apply (lc_ty_at_mono 0 k (theta X)); [lia|apply Htheta].
  - apply lc_ty_arrow; [apply IH1|apply IH2]; assumption.
  - apply lc_ty_all. apply IH. assumption.
  - apply lc_ty_nat.
Qed.

Lemma tm_tinst_lc : forall (theta : ty_subst_env) K k t, lc_tm_at K k t ->
  (forall X, locally_closed_ty (theta X)) ->
  lc_tm_at K k (tm_tinst theta t).
Proof.
  intros theta K k t H. induction H; intros Htheta; simpl.
  - apply lc_tm_bvar; assumption.
  - apply lc_tm_fvar.
  - apply lc_tm_abs; [apply ty_inst_lc; assumption|apply IHlc_tm_at; assumption].
  - apply lc_tm_app; [apply IHlc_tm_at1|apply IHlc_tm_at2]; assumption.
  - apply lc_tm_tabs. apply IHlc_tm_at. assumption.
  - apply lc_tm_tapp; [apply IHlc_tm_at|apply ty_inst_lc]; assumption.
  - apply lc_tm_zero.
  - apply lc_tm_succ. apply IHlc_tm_at. assumption.
  - apply lc_tm_rec; [apply IHlc_tm_at1|apply IHlc_tm_at2|apply IHlc_tm_at3]; assumption.
Qed.

Lemma tm_inst_lc : forall (sigma : tm_subst_env) K k t, lc_tm_at K k t ->
  (forall x, locally_closed_tm (sigma x)) ->
  lc_tm_at K k (tm_inst sigma t).
Proof.
  intros sigma K k t H.
  induction H as [Kb kb ib Hib|Kf kf xf|Ka ka Ta ta HTa Hta IHa|Kapp kapp t1 t2 H1 IH1 H2 IH2|
    Ktabs ktabs tt Htabs IHtabs|Ktapp ktapp tu Tu Htu IHtu HTu|Kzero kzero|Ksucc ksucc ts Hsucc IHsucc|Krec krec nn bb ss Hnn IHnn Hbb IHbb Hss IHss];
    intros Hsigma; simpl.
  - apply lc_tm_bvar; assumption.
  - unfold locally_closed_tm in Hsigma.
    apply (lc_tm_at_mono 0 Kf 0 kf (sigma xf)); [lia|lia|apply Hsigma].
  - apply lc_tm_abs; [assumption|apply IHa; assumption].
  - apply lc_tm_app; [apply IH1|apply IH2]; assumption.
  - apply lc_tm_tabs. exact (IHtabs Hsigma).
  - apply lc_tm_tapp; [exact (IHtu Hsigma)|assumption].
  - apply lc_tm_zero.
  - apply lc_tm_succ. apply IHsucc. assumption.
  - apply lc_tm_rec; [apply IHnn|apply IHbb|apply IHss]; assumption.
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

End SystemFParametricityRecursionMediumTask.
