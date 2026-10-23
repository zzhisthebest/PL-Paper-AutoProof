(** System F parametricity benchmark, Medium variant.
    Features: nondeterminism-recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFParametricityNondeterminismRecursionMediumTask.

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
  | Ty_Nat => v1 = v2 /\ numeric_value v1
  end.

Definition expression_relation eta rho T t1 t2 :=
  expression_lifting (value_relation eta rho T) t1 t2.

Lemma numeric_value_closed : forall n,
  numeric_value n -> locally_closed_tm n.
Proof.
  intros n H; induction H; constructor; auto.
Qed.

Lemma value_closed : forall v, value v -> locally_closed_tm v.
Proof.
  intros v H; inversion H; subst; auto using numeric_value_closed.
Qed.

Lemma evaluates_value : forall t v, evaluates t v -> value v.
Proof.
  intros t v H; induction H; eauto using nv_succ, v_nat.
Qed.

Lemma evaluates_closed : forall t v,
  evaluates t v -> locally_closed_tm t.
Proof.
  intros t v H; induction H;
    try solve [apply value_closed; assumption];
    unfold locally_closed_tm in *; eauto with core.
Qed.

Lemma multi_trans : forall t u v, t -->* u -> u -->* v -> t -->* v.
Proof.
  intros t u v H; induction H; eauto using multi.
Qed.

Lemma multi_app_left : forall t u arg,
  t -->* u -> locally_closed_tm arg ->
  tm_app t arg -->* tm_app u arg.
Proof.
  intros t u arg H; induction H; intros Harg; eauto using multi, ST_App1.
Qed.

Lemma multi_app_right : forall f t u,
  value f -> t -->* u -> tm_app f t -->* tm_app f u.
Proof.
  intros f t u Hf H; induction H; eauto using multi, ST_App2.
Qed.

Lemma multi_tapp : forall t u U,
  t -->* u -> locally_closed_ty U ->
  tm_tapp t U -->* tm_tapp u U.
Proof.
  intros t u U H; induction H; intros HU; eauto using multi, ST_TApp.
Qed.

Lemma multi_succ : forall t u,
  t -->* u -> tm_succ t -->* tm_succ u.
Proof.
  intros t u H; induction H; eauto using multi, ST_Succ.
Qed.

Lemma multi_rec_arg : forall n n' b s,
  n -->* n' -> locally_closed_tm b -> locally_closed_tm s ->
  tm_natrec n b s -->* tm_natrec n' b s.
Proof.
  intros n n' b s H; induction H; intros Hb Hs;
    eauto using multi, ST_RecArg.
Qed.

Lemma multi_rec_base : forall n b b' s,
  numeric_value n -> b -->* b' -> locally_closed_tm s ->
  tm_natrec n b s -->* tm_natrec n b' s.
Proof.
  intros n b b' s Hn H; induction H; intros Hs;
    eauto using multi, ST_RecBase.
Qed.

Lemma multi_rec_step : forall n b s s',
  numeric_value n -> value b -> s -->* s' ->
  tm_natrec n b s -->* tm_natrec n b s'.
Proof.
  intros n b s s' Hn Hb H; induction H;
    eauto using multi, ST_RecStep.
Qed.

Lemma evaluates_multi : forall t v, evaluates t v -> t -->* v.
Proof.
  intros t v H; induction H.
  - constructor.
  - eapply multi_trans.
    + eapply multi_app_left; eauto using evaluates_closed.
    + eapply multi_trans.
      * eapply multi_app_right; [eapply evaluates_value; eauto | exact IHevaluates2].
      * eapply multi_step.
        -- eapply ST_AppAbs.
           ++ eapply value_closed, evaluates_value; eauto.
           ++ eapply evaluates_value; eauto.
        -- exact IHevaluates3.
  - eapply multi_trans.
    + eapply multi_tapp; eauto.
    + eapply multi_step.
      * eapply ST_TAppTabs; eauto using value_closed, evaluates_value.
      * exact IHevaluates2.
  - apply multi_succ; assumption.
  - eapply multi_trans.
    + eapply multi_rec_arg; eauto using evaluates_closed.
    + eapply multi_trans.
      * eapply multi_rec_base; eauto using evaluates_closed, nv_zero.
      * eapply multi_trans.
        -- eapply multi_rec_step; eauto using evaluates_value, nv_zero.
        -- eapply multi_step.
           ++ eapply ST_RecZero; eauto using evaluates_value.
           ++ constructor.
  - eapply multi_trans.
    + eapply multi_rec_arg; eauto using evaluates_closed.
    + eapply multi_trans.
      * eapply multi_rec_base; eauto using evaluates_closed, nv_succ.
      * eapply multi_trans.
        -- eapply multi_rec_step; eauto using evaluates_value, nv_succ.
        -- eapply multi_step.
           ++ eapply ST_RecSucc; eauto using evaluates_value.
           ++ exact IHevaluates4.
  - eapply multi_step.
    + eapply ST_ChoiceLeft; eauto using evaluates_closed.
    + exact IHevaluates.
  - eapply multi_step.
    + eapply ST_ChoiceRight; eauto using evaluates_closed.
    + exact IHevaluates.
Qed.

Lemma value_relation_values : forall T eta rho v1 v2,
  value_relation eta rho T v1 v2 -> value v1 /\ value v2.
Proof.
  induction T; intros eta rho v1 v2 H; simpl in H.
  - destruct (nth_error eta n) as [a|]; [exact (candidate_values a _ _ H)| contradiction].
  - destruct (rho a) as [b|]; [exact (candidate_values b _ _ H)| contradiction].
  - tauto.
  - tauto.
  - destruct H as [-> H]; split; constructor; assumption.
Qed.

Lemma lc_ty_open_inv : forall T k X,
  lc_ty_at k (open_ty_rec k (Ty_FVar X) T) -> lc_ty_at (S k) T.
Proof.
  induction T; intros k X H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst. apply lc_ty_bvar; lia.
    + inversion H; subst. apply lc_ty_bvar; lia.
  - constructor.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - constructor.
Qed.

Lemma lc_tm_open_inv : forall t K k x,
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) ->
  lc_tm_at K (S k) t.
Proof.
  induction t; intros K k x H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst. apply lc_tm_bvar; lia.
    + inversion H; subst. apply lc_tm_bvar; lia.
  - constructor.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
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
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
Qed.

Lemma list_max_bound : forall (L : list nat) x,
  In x L -> x <= fold_right Nat.max 0 L.
Proof.
  induction L as [|a L IH]; intros x H; simpl in *.
  - contradiction.
  - destruct H as [->|H]; [lia|]. specialize (IH x H). lia.
Qed.

Lemma fresh_atom : forall L,
  ~ In (S (fold_right Nat.max 0 L)) L.
Proof.
  intros L H; pose proof (list_max_bound L _ H); lia.
Qed.

Lemma wf_ty_closed : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H; induction H; unfold locally_closed_ty in *.
  - constructor.
  - constructor; assumption.
  - constructor. eapply lc_ty_open_inv with
      (X := S (fold_right Nat.max 0 L)).
    apply H0, fresh_atom.
  - constructor.
Qed.

Lemma has_type_closed : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T H; induction H;
    unfold locally_closed_tm in *.
  - constructor.
  - constructor.
    + apply wf_ty_closed in H. exact H.
    + eapply lc_tm_open_inv with
        (x := S (fold_right Nat.max 0 L)).
      apply H1, fresh_atom.
  - constructor; assumption.
  - constructor. eapply lc_tm_ty_open_inv with
      (X := S (fold_right Nat.max 0 L)).
    apply H0, fresh_atom.
  - constructor; [assumption|]. apply wf_ty_closed in H0. exact H0.
  - constructor.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
Qed.

Fixpoint ty_atoms (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => [] | Ty_FVar X => [X]
  | Ty_Arrow A B => ty_atoms A ++ ty_atoms B
  | Ty_All A => ty_atoms A | Ty_Nat => []
  end.

Fixpoint tm_atoms (t : tm) : list atom :=
  match t with
  | tm_bvar _ => [] | tm_fvar x => [x]
  | tm_abs _ b => tm_atoms b
  | tm_app f a => tm_atoms f ++ tm_atoms a
  | tm_tabs b => tm_atoms b
  | tm_tapp f _ => tm_atoms f
  | tm_zero => [] | tm_succ n => tm_atoms n
  | tm_natrec n b s => tm_atoms n ++ tm_atoms b ++ tm_atoms s
  | tm_choice a b => tm_atoms a ++ tm_atoms b
  end.

Fixpoint tm_ty_atoms (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_fvar _ | tm_zero => []
  | tm_abs T b => ty_atoms T ++ tm_ty_atoms b
  | tm_app f a => tm_ty_atoms f ++ tm_ty_atoms a
  | tm_tabs b => tm_ty_atoms b
  | tm_tapp f T => tm_ty_atoms f ++ ty_atoms T
  | tm_succ n => tm_ty_atoms n
  | tm_natrec n b s => tm_ty_atoms n ++ tm_ty_atoms b ++ tm_ty_atoms s
  | tm_choice a b => tm_ty_atoms a ++ tm_ty_atoms b
  end.

Fixpoint instantiate_ty (sigma : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i | Ty_FVar X => sigma X
  | Ty_Arrow A B => Ty_Arrow (instantiate_ty sigma A) (instantiate_ty sigma B)
  | Ty_All A => Ty_All (instantiate_ty sigma A) | Ty_Nat => Ty_Nat
  end.

Fixpoint instantiate_tm (sigma : atom -> ty) (gamma : atom -> tm)
    (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i | tm_fvar x => gamma x
  | tm_abs T b => tm_abs (instantiate_ty sigma T) (instantiate_tm sigma gamma b)
  | tm_app f a => tm_app (instantiate_tm sigma gamma f) (instantiate_tm sigma gamma a)
  | tm_tabs b => tm_tabs (instantiate_tm sigma gamma b)
  | tm_tapp f T => tm_tapp (instantiate_tm sigma gamma f) (instantiate_ty sigma T)
  | tm_zero => tm_zero | tm_succ n => tm_succ (instantiate_tm sigma gamma n)
  | tm_natrec n b s => tm_natrec (instantiate_tm sigma gamma n)
      (instantiate_tm sigma gamma b) (instantiate_tm sigma gamma s)
  | tm_choice a b => tm_choice (instantiate_tm sigma gamma a)
      (instantiate_tm sigma gamma b)
  end.

Definition ty_update (sigma : atom -> ty) (X : atom) (U : ty) :=
  fun Y => if Nat.eqb X Y then U else sigma Y.
Definition tm_update (gamma : atom -> tm) (x : atom) (v : tm) :=
  fun y => if Nat.eqb x y then v else gamma y.

Lemma lc_ty_weaken : forall K T,
  lc_ty_at K T -> forall J, K <= J -> lc_ty_at J T.
Proof.
  intros K T H; induction H; intros J Hle.
  - apply lc_ty_bvar; lia.
  - constructor.
  - constructor; eauto.
  - constructor. apply IHlc_ty_at. lia.
  - constructor.
Qed.

Lemma lc_tm_weaken : forall K k t,
  lc_tm_at K k t -> forall J j,
    K <= J -> k <= j -> lc_tm_at J j t.
Proof.
  intros K k t H; induction H; intros J j HK Hk;
    try solve [constructor; eauto using lc_ty_weaken; lia].
  - apply lc_tm_abs.
    + eapply lc_ty_weaken; eauto.
    + apply IHlc_tm_at; lia.
  - apply lc_tm_tabs. apply IHlc_tm_at; lia.
Qed.

Lemma instantiate_ty_closed : forall K T sigma,
  lc_ty_at K T ->
  (forall X, locally_closed_ty (sigma X)) ->
  lc_ty_at K (instantiate_ty sigma T).
Proof.
  intros K T sigma H; induction H; intros Hsigma; simpl;
    eauto using lc_ty_at.
  eapply lc_ty_weaken; [apply Hsigma|lia].
Qed.

Lemma instantiate_tm_closed : forall K k t sigma gamma,
  lc_tm_at K k t ->
  (forall X, locally_closed_ty (sigma X)) ->
  (forall x, locally_closed_tm (gamma x)) ->
  lc_tm_at K k (instantiate_tm sigma gamma t).
Proof.
  intros K k t sigma gamma H; induction H; intros Hsigma Hgamma;
    simpl; eauto using lc_tm_at, instantiate_ty_closed.
  - eapply lc_tm_weaken; [apply Hgamma|lia|lia].
Qed.

Lemma lc_ty_open_id : forall K T,
  lc_ty_at K T -> forall j U, K <= j -> open_ty_rec j U T = T.
Proof.
  intros K T H; induction H; intros j U Hj; simpl.
  - destruct (Nat.eqb j i) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - reflexivity.
  - f_equal; eauto.
  - f_equal. apply IHlc_ty_at. lia.
  - reflexivity.
Qed.

Lemma lc_tm_open_id : forall K k t,
  lc_tm_at K k t -> forall j u, k <= j -> open_tm_rec j u t = t.
Proof.
  intros K k t H; induction H; intros j u Hj; simpl;
    try solve [f_equal; eauto; lia].
  - destruct (Nat.eqb j i) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - f_equal. apply IHlc_tm_at. lia.
Qed.

Lemma lc_tm_ty_open_id : forall K k t,
  lc_tm_at K k t -> forall j U, K <= j -> open_tm_ty_rec j U t = t.
Proof.
  intros K k t H; induction H; intros j U Hj; simpl;
    try solve [f_equal; eauto using lc_ty_open_id; lia].
  f_equal. apply IHlc_tm_at. lia.
Qed.

Lemma not_in_app : forall (x : atom) A B,
  ~ In x (A ++ B) -> ~ In x A /\ ~ In x B.
Proof.
  intros x A B H; split; intro Hin; apply H; apply in_or_app; auto.
Qed.

Lemma instantiate_ty_open : forall T k X sigma U,
  ~ In X (ty_atoms T) ->
  (forall Y, locally_closed_ty (sigma Y)) ->
  instantiate_ty (ty_update sigma X U)
    (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k U (instantiate_ty sigma T).
Proof.
  induction T; intros k X sigma U Hfresh Hsigma; simpl in *.
  - destruct (Nat.eqb k n); simpl; [unfold ty_update; rewrite Nat.eqb_refl|]; reflexivity.
  - assert (X <> a) by (intro E; subst; apply Hfresh; simpl; auto).
    unfold ty_update.
    assert (E : Nat.eqb X a = false) by (apply Nat.eqb_neq; congruence).
    rewrite E.
    symmetry. apply lc_ty_open_id with (K := 0).
    + apply Hsigma.
    + lia.
  - apply not_in_app in Hfresh as [HA HB].
    f_equal; eauto.
  - f_equal; eauto.
  - reflexivity.
Qed.

Lemma instantiate_tm_open : forall t k x sigma gamma v,
  ~ In x (tm_atoms t) ->
  (forall y, locally_closed_tm (gamma y)) ->
  instantiate_tm sigma (tm_update gamma x v)
    (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k v (instantiate_tm sigma gamma t).
Proof.
  induction t; intros k x sigma gamma v Hfresh Hgamma; simpl in *.
  - destruct (Nat.eqb k n); simpl; [unfold tm_update; rewrite Nat.eqb_refl|]; reflexivity.
  - assert (x <> a) by (intro E; subst; apply Hfresh; simpl; auto).
    unfold tm_update.
    assert (E : Nat.eqb x a = false) by (apply Nat.eqb_neq; congruence).
    rewrite E.
    symmetry. apply lc_tm_open_id with (k := 0) (K := 0).
    + apply Hgamma.
    + lia.
  - f_equal; eauto.
  - apply not_in_app in Hfresh as [HA HB]. f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - reflexivity.
  - f_equal; eauto.
  - apply not_in_app in Hfresh as [HA HB].
    apply not_in_app in HB as [HB0 HS].
    f_equal; eauto.
  - apply not_in_app in Hfresh as [HA HB]. f_equal; eauto.
Qed.

Lemma instantiate_tm_ty_open : forall t k X sigma gamma U,
  ~ In X (tm_ty_atoms t) ->
  (forall Y, locally_closed_ty (sigma Y)) ->
  (forall y, locally_closed_tm (gamma y)) ->
  instantiate_tm (ty_update sigma X U) gamma
    (open_tm_ty_rec k (Ty_FVar X) t) =
  open_tm_ty_rec k U (instantiate_tm sigma gamma t).
Proof.
  induction t; intros k X sigma gamma U Hfresh Hsigma Hgamma;
    simpl in *.
  - reflexivity.
  - symmetry. apply lc_tm_ty_open_id with (K := 0) (k := 0).
    + apply Hgamma.
    + lia.
  - apply not_in_app in Hfresh as [HT HB].
    f_equal; eauto using instantiate_ty_open.
  - apply not_in_app in Hfresh as [HA HB]. f_equal; eauto.
  - f_equal; eauto.
  - apply not_in_app in Hfresh as [HA HT].
    f_equal; eauto using instantiate_ty_open.
  - reflexivity.
  - f_equal; eauto.
  - apply not_in_app in Hfresh as [HA HB].
    apply not_in_app in HB as [HB0 HS].
    f_equal; eauto.
  - apply not_in_app in Hfresh as [HA HB]. f_equal; eauto.
Qed.

Lemma expression_lifting_equiv : forall R S t1 t2,
  (forall v1 v2, R v1 v2 <-> S v1 v2) ->
  expression_lifting R t1 t2 <-> expression_lifting S t1 t2.
Proof.
  intros R S t1 t2 H; unfold expression_lifting, results_match.
  split; intros (Hc1 & Hc2 & v1 & v2 & E1 & E2 & HR);
    repeat split; try assumption; exists v1, v2;
    repeat split; try assumption; apply H; assumption.
Qed.

Lemma value_relation_closed_extension : forall T eta extra rho v1 v2,
  lc_ty_at (length eta) T ->
  value_relation eta rho T v1 v2 <->
  value_relation (eta ++ extra) rho T v1 v2.
Proof.
  induction T; intros eta extra rho v1 v2 Hlc; simpl in *.
  - inversion Hlc; subst.
    rewrite nth_error_app1 by assumption. tauto.
  - tauto.
  - assert (HA : lc_ty_at (length eta) T1) by (inversion Hlc; assumption).
    assert (HB : lc_ty_at (length eta) T2) by (inversion Hlc; assumption).
    split.
    + intros (Hv1 & Hv2 & U1 & body1 & U2 & body2 & E1 & E2 & Hbody).
      split; [exact Hv1|]. split; [exact Hv2|].
      exists U1, body1, U2, body2.
      split; [exact E1|]. split; [exact E2|].
      intros a1 a2 Harg.
      apply (proj1 (expression_lifting_equiv _ _ _ _
        (fun p q => IHT2 eta extra rho p q HB))).
      apply Hbody. apply (proj2 (IHT1 eta extra rho a1 a2 HA)). exact Harg.
    + intros (Hv1 & Hv2 & U1 & body1 & U2 & body2 & E1 & E2 & Hbody).
      split; [exact Hv1|]. split; [exact Hv2|].
      exists U1, body1, U2, body2.
      split; [exact E1|]. split; [exact E2|].
      intros a1 a2 Harg.
      apply (proj2 (expression_lifting_equiv _ _ _ _
        (fun p q => IHT2 eta extra rho p q HB))).
      apply Hbody. apply (proj1 (IHT1 eta extra rho a1 a2 HA)). exact Harg.
  - assert (HA : lc_ty_at (S (length eta)) T) by (inversion Hlc; assumption).
    split.
    + intros (Hv1 & Hv2 & body1 & body2 & E1 & E2 & Hbody).
      split; [exact Hv1|]. split; [exact Hv2|].
      exists body1, body2.
      split; [exact E1|]. split; [exact E2|].
      intros U1 U2 a HU1 HU2.
      apply (proj1 (expression_lifting_equiv _ _ _ _
        (fun p q => IHT (a :: eta) extra rho p q HA))).
      apply Hbody; assumption.
    + intros (Hv1 & Hv2 & body1 & body2 & E1 & E2 & Hbody).
      split; [exact Hv1|]. split; [exact Hv2|].
      exists body1, body2.
      split; [exact E1|]. split; [exact E2|].
      intros U1 U2 a HU1 HU2.
      apply (proj2 (expression_lifting_equiv _ _ _ _
        (fun p q => IHT (a :: eta) extra rho p q HA))).
      apply Hbody; assumption.
  - tauto.
Qed.

Lemma nth_error_snoc : forall (A : Type) (eta : list A) (a : A) n,
  nth_error (eta ++ [a]) n =
    if Nat.eqb n (length eta) then Some a else nth_error eta n.
Proof.
  intros A eta; induction eta as [|b eta IH]; intros a n;
    destruct n; simpl; auto.
  destruct n; reflexivity.
Qed.

Lemma value_relation_open_fvar : forall T eta rho X a v1 v2,
  ~ In X (ty_atoms T) ->
  value_relation eta (relation_update rho X a)
    (open_ty_rec (length eta) (Ty_FVar X) T) v1 v2 <->
  value_relation (eta ++ [a]) rho T v1 v2.
Proof.
  induction T; intros eta rho X cand v1 v2 Hfresh; simpl in *.
  - rewrite nth_error_snoc.
    destruct (Nat.eqb (length eta) n) eqn:E.
    + apply Nat.eqb_eq in E; subst. rewrite Nat.eqb_refl.
      simpl. unfold relation_update. rewrite Nat.eqb_refl. tauto.
    + apply Nat.eqb_neq in E.
      assert (E' : Nat.eqb n (length eta) = false)
        by (apply Nat.eqb_neq; lia).
      rewrite E'. tauto.
  - assert (X <> a) by (intro E; subst; apply Hfresh; simpl; auto).
    unfold relation_update.
    assert (E : Nat.eqb X a = false) by (apply Nat.eqb_neq; congruence).
    rewrite E. tauto.
  - apply not_in_app in Hfresh as [HA HB].
    split.
    + intros (Hv1 & Hv2 & U1 & body1 & U2 & body2 & E1 & E2 & Hbody).
      split; [exact Hv1|]. split; [exact Hv2|].
      exists U1, body1, U2, body2.
      split; [exact E1|]. split; [exact E2|].
      intros arg1 arg2 Harg.
      apply (proj1 (expression_lifting_equiv _ _ _ _
        (fun p q => IHT2 eta rho X cand p q HB))).
      apply Hbody.
      apply (proj2 (IHT1 eta rho X cand arg1 arg2 HA)). exact Harg.
    + intros (Hv1 & Hv2 & U1 & body1 & U2 & body2 & E1 & E2 & Hbody).
      split; [exact Hv1|]. split; [exact Hv2|].
      exists U1, body1, U2, body2.
      split; [exact E1|]. split; [exact E2|].
      intros arg1 arg2 Harg.
      apply (proj2 (expression_lifting_equiv _ _ _ _
        (fun p q => IHT2 eta rho X cand p q HB))).
      apply Hbody.
      apply (proj1 (IHT1 eta rho X cand arg1 arg2 HA)). exact Harg.
  - split.
    + intros (Hv1 & Hv2 & body1 & body2 & E1 & E2 & Hbody).
      split; [exact Hv1|]. split; [exact Hv2|].
      exists body1, body2. split; [exact E1|]. split; [exact E2|].
      intros U1 U2 b HU1 HU2.
      apply (proj1 (expression_lifting_equiv _ _ _ _
        (fun p q => IHT (b :: eta) rho X cand p q Hfresh))).
      apply Hbody; assumption.
    + intros (Hv1 & Hv2 & body1 & body2 & E1 & E2 & Hbody).
      split; [exact Hv1|]. split; [exact Hv2|].
      exists body1, body2. split; [exact E1|]. split; [exact E2|].
      intros U1 U2 b HU1 HU2.
      apply (proj2 (expression_lifting_equiv _ _ _ _
        (fun p q => IHT (b :: eta) rho X cand p q Hfresh))).
      apply Hbody; assumption.
  - tauto.
Qed.

Lemma value_relation_open_ty : forall T eta rho U a v1 v2,
  locally_closed_ty U ->
  (forall p q, candidate_relation a p q <->
    value_relation [] rho U p q) ->
  value_relation eta rho (open_ty_rec (length eta) U T) v1 v2 <->
  value_relation (eta ++ [a]) rho T v1 v2.
Proof.
  induction T; intros eta rho U cand v1 v2 HU Hcand; simpl in *.
  - rewrite nth_error_snoc.
    destruct (Nat.eqb (length eta) n) eqn:E.
    + apply Nat.eqb_eq in E; subst. rewrite Nat.eqb_refl. simpl.
      rewrite Hcand.
      apply iff_sym. apply value_relation_closed_extension with
        (eta := []) (extra := eta).
      exact HU.
    + apply Nat.eqb_neq in E.
      assert (E' : Nat.eqb n (length eta) = false)
        by (apply Nat.eqb_neq; lia).
      rewrite E'. tauto.
  - tauto.
  - split.
    + intros (Hv1 & Hv2 & U1 & body1 & U2 & body2 & E1 & E2 & Hbody).
      split; [exact Hv1|]. split; [exact Hv2|].
      exists U1, body1, U2, body2.
      split; [exact E1|]. split; [exact E2|].
      intros arg1 arg2 Harg.
      apply (proj1 (expression_lifting_equiv _ _ _ _
        (fun p q => IHT2 eta rho U cand p q HU Hcand))).
      apply Hbody.
      apply (proj2 (IHT1 eta rho U cand arg1 arg2 HU Hcand)). exact Harg.
    + intros (Hv1 & Hv2 & U1 & body1 & U2 & body2 & E1 & E2 & Hbody).
      split; [exact Hv1|]. split; [exact Hv2|].
      exists U1, body1, U2, body2.
      split; [exact E1|]. split; [exact E2|].
      intros arg1 arg2 Harg.
      apply (proj2 (expression_lifting_equiv _ _ _ _
        (fun p q => IHT2 eta rho U cand p q HU Hcand))).
      apply Hbody.
      apply (proj1 (IHT1 eta rho U cand arg1 arg2 HU Hcand)). exact Harg.
  - split.
    + intros (Hv1 & Hv2 & body1 & body2 & E1 & E2 & Hbody).
      split; [exact Hv1|]. split; [exact Hv2|].
      exists body1, body2. split; [exact E1|]. split; [exact E2|].
      intros U1 U2 b HU1 HU2.
      apply (proj1 (expression_lifting_equiv _ _ _ _
        (fun p q => IHT (b :: eta) rho U cand p q HU Hcand))).
      apply Hbody; assumption.
    + intros (Hv1 & Hv2 & body1 & body2 & E1 & E2 & Hbody).
      split; [exact Hv1|]. split; [exact Hv2|].
      exists body1, body2. split; [exact E1|]. split; [exact E2|].
      intros U1 U2 b HU1 HU2.
      apply (proj2 (expression_lifting_equiv _ _ _ _
        (fun p q => IHT (b :: eta) rho U cand p q HU Hcand))).
      apply Hbody; assumption.
  - tauto.
Qed.

Definition semantic_candidate (rho : binary_env) (T : ty) : binary_candidate :=
  {| candidate_relation := value_relation [] rho T;
     candidate_values := value_relation_values T [] rho |}.

Lemma value_relation_rho_fresh : forall T rho X a v1 v2,
  locally_closed_ty T -> ~ In X (ty_atoms T) ->
  value_relation [] (relation_update rho X a) T v1 v2 <->
  value_relation [] rho T v1 v2.
Proof.
  intros T rho X a v1 v2 Hlc Hfresh.
  pose proof (value_relation_open_fvar T [] rho X a v1 v2 Hfresh) as Hopen.
  simpl in Hopen.
  rewrite (lc_ty_open_id 0 T Hlc 0 (Ty_FVar X)) in Hopen by lia.
  pose proof (value_relation_closed_extension T [] [a] rho v1 v2 Hlc) as Hext.
  simpl in Hext. tauto.
Qed.

Fixpoint context_atoms (Gamma : context) : list atom :=
  match Gamma with
  | [] => [] | (_, T) :: Gamma' => ty_atoms T ++ context_atoms Gamma'
  end.

Lemma lookup_atoms : forall Gamma x T X,
  lookup_context x Gamma = Some T ->
  In X (ty_atoms T) -> In X (context_atoms Gamma).
Proof.
  induction Gamma as [|[y U] Gamma IH]; intros x T X Hlook Hin;
    simpl in *; try discriminate.
  destruct (Nat.eqb x y) eqn:E.
  - inversion Hlook; subst. apply in_or_app. left. exact Hin.
  - apply in_or_app. right. eapply IH; eauto.
Qed.

Lemma expression_app : forall eta rho A B f1 f2 a1 a2,
  expression_relation eta rho (Ty_Arrow A B) f1 f2 ->
  expression_relation eta rho A a1 a2 ->
  expression_relation eta rho B (tm_app f1 a1) (tm_app f2 a2).
Proof.
  intros eta rho A B f1 f2 a1 a2
    [Hf1 [Hf2 [vf1 [vf2 [Ef1 [Ef2 Hfun]]]]]]
    [Ha1 [Ha2 [va1 [va2 [Ea1 [Ea2 Harg]]]]]].
  simpl in Hfun.
  destruct Hfun as [_ [_ [U1 [body1 [U2 [body2 [E1 [E2 Hbody]]]]]]]].
  subst vf1 vf2.
  specialize (Hbody va1 va2 Harg).
  destruct Hbody as [_ [_ [r1 [r2 [Er1 [Er2 Hr]]]]]].
  split; [unfold locally_closed_tm in *; constructor; assumption|].
  split; [unfold locally_closed_tm in *; constructor; assumption|].
  exists r1, r2. repeat split; try assumption.
  - eapply EvalApp; eauto.
  - eapply EvalApp; eauto.
Qed.

Lemma expression_tapp : forall rho T U U1 U2 f1 f2,
  locally_closed_ty U -> locally_closed_ty U1 -> locally_closed_ty U2 ->
  expression_relation [] rho (Ty_All T) f1 f2 ->
  expression_relation [] rho (open_ty T U)
    (tm_tapp f1 U1) (tm_tapp f2 U2).
Proof.
  intros rho T U U1 U2 f1 f2 HU HU1 HU2
    [Hf1 [Hf2 [vf1 [vf2 [Ef1 [Ef2 Hfun]]]]]].
  simpl in Hfun.
  destruct Hfun as [_ [_ [body1 [body2 [E1 [E2 Hbody]]]]]].
  subst vf1 vf2.
  specialize (Hbody U1 U2 (semantic_candidate rho U) HU1 HU2).
  apply (proj1 (expression_lifting_equiv _ _ _ _
    (fun p q => iff_sym (value_relation_open_ty T [] rho U
      (semantic_candidate rho U) p q HU (fun _ _ => iff_refl _))))) in Hbody.
  destruct Hbody as [_ [_ [r1 [r2 [Er1 [Er2 Hr]]]]]].
  split; [unfold locally_closed_tm in *; constructor; assumption|].
  split; [unfold locally_closed_tm in *; constructor; assumption|].
  exists r1, r2. repeat split; try assumption.
  - eapply EvalTApp; eauto.
  - eapply EvalTApp; eauto.
Qed.

Lemma rec_results : forall eta rho T k,
  numeric_value k ->
  forall n1 n2 b1 b2 s1 s2 vb1 vb2 vs1 vs2,
  evaluates n1 k -> evaluates n2 k ->
  evaluates b1 vb1 -> evaluates b2 vb2 ->
  evaluates s1 vs1 -> evaluates s2 vs2 ->
  value_relation eta rho T vb1 vb2 ->
  value_relation eta rho
    (Ty_Arrow Ty_Nat (Ty_Arrow T T)) vs1 vs2 ->
  exists r1 r2,
    evaluates (tm_natrec n1 b1 s1) r1 /\
    evaluates (tm_natrec n2 b2 s2) r2 /\
    value_relation eta rho T r1 r2.
Proof.
  intros eta rho T k Hnum.
  induction Hnum as [|k Hk IH];
    intros n1 n2 b1 b2 s1 s2 vb1 vb2 vs1 vs2
      En1 En2 Eb1 Eb2 Es1 Es2 Hb Hs.
  - exists vb1, vb2. split; [eapply EvalRecZero; eauto|].
    split; [eapply EvalRecZero; eauto|exact Hb].
  - destruct (value_relation_values _ _ _ _ _ Hb) as [Hvb1 Hvb2].
    destruct (value_relation_values _ _ _ _ _ Hs) as [Hvs1 Hvs2].
    assert (Hpred1 : evaluates k k) by (constructor; constructor; assumption).
    assert (Hpred2 : evaluates k k) by (constructor; constructor; assumption).
    destruct (IH k k vb1 vb2 vs1 vs2 vb1 vb2 vs1 vs2
      Hpred1 Hpred2 (EvalValue _ Hvb1) (EvalValue _ Hvb2)
      (EvalValue _ Hvs1) (EvalValue _ Hvs2) Hb Hs)
      as [rr1 [rr2 [Err1 [Err2 Hrr]]]].
    assert (Hstep : expression_relation eta rho
      (Ty_Arrow Ty_Nat (Ty_Arrow T T)) vs1 vs2).
    { split; [apply value_closed; exact Hvs1|].
      split; [apply value_closed; exact Hvs2|].
      exists vs1, vs2. split; [constructor; exact Hvs1|].
      split; [constructor; exact Hvs2|exact Hs]. }
    assert (Hpred : expression_relation eta rho Ty_Nat k k).
    { split; [apply numeric_value_closed; exact Hk|].
      split; [apply numeric_value_closed; exact Hk|].
      exists k, k. split; [constructor; constructor; exact Hk|].
      split; [constructor; constructor; exact Hk|].
      simpl. split; [reflexivity|exact Hk]. }
    assert (Hrec : expression_relation eta rho T
      (tm_natrec k vb1 vs1) (tm_natrec k vb2 vs2)).
    { split; [apply evaluates_closed in Err1; exact Err1|].
      split; [apply evaluates_closed in Err2; exact Err2|].
      exists rr1, rr2. split; [exact Err1|].
      split; [exact Err2|exact Hrr]. }
    pose proof (expression_app eta rho Ty_Nat (Ty_Arrow T T)
      vs1 vs2 k k Hstep Hpred) as Hfirst.
    pose proof (expression_app eta rho T T
      (tm_app vs1 k) (tm_app vs2 k)
      (tm_natrec k vb1 vs1) (tm_natrec k vb2 vs2)
      Hfirst Hrec) as Hsecond.
    destruct Hsecond as [_ [_ [r1 [r2 [Eapp1 [Eapp2 Hr]]]]]].
    exists r1, r2. split; [eapply EvalRecSucc; eauto|].
    split; [eapply EvalRecSucc; eauto|exact Hr].
Qed.

Lemma expression_rec : forall eta rho T n1 n2 b1 b2 s1 s2,
  expression_relation eta rho Ty_Nat n1 n2 ->
  expression_relation eta rho T b1 b2 ->
  expression_relation eta rho
    (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s1 s2 ->
  expression_relation eta rho T
    (tm_natrec n1 b1 s1) (tm_natrec n2 b2 s2).
Proof.
  intros eta rho T n1 n2 b1 b2 s1 s2
    [Hn1 [Hn2 [k1 [k2 [En1 [En2 Hk]]]]]]
    [Hb1 [Hb2 [vb1 [vb2 [Eb1 [Eb2 Hb]]]]]]
    [Hs1 [Hs2 [vs1 [vs2 [Es1 [Es2 Hs]]]]]].
  simpl in Hk. destruct Hk as [-> Hnum].
  destruct (rec_results eta rho T k2 Hnum n1 n2 b1 b2 s1 s2
    vb1 vb2 vs1 vs2 En1 En2 Eb1 Eb2 Es1 Es2 Hb Hs)
    as [r1 [r2 [Er1 [Er2 Hr]]]].
  split; [unfold locally_closed_tm in *; constructor; assumption|].
  split; [unfold locally_closed_tm in *; constructor; assumption|].
  exists r1, r2. split; [exact Er1|].
  split; [exact Er2|exact Hr].
Qed.

Definition semantic_environment (Gamma : context)
    (sigma1 sigma2 : atom -> ty) (gamma1 gamma2 : atom -> tm)
    (rho : binary_env) : Prop :=
  (forall X, locally_closed_ty (sigma1 X) /\ locally_closed_ty (sigma2 X)) /\
  (forall x, value (gamma1 x) /\ value (gamma2 x)) /\
  (forall x T, lookup_context x Gamma = Some T ->
    locally_closed_ty T /\
    value_relation [] rho T (gamma1 x) (gamma2 x)).

Lemma instantiated_typed_closed : forall Delta Gamma t T sigma gamma,
  has_type Delta Gamma t T ->
  (forall X, locally_closed_ty (sigma X)) ->
  (forall x, value (gamma x)) ->
  locally_closed_tm (instantiate_tm sigma gamma t).
Proof.
  intros Delta Gamma t T sigma gamma Hty Hsigma Hgamma.
  eapply instantiate_tm_closed.
  - apply has_type_closed with (Delta := Delta) (Gamma := Gamma) (T := T).
    exact Hty.
  - exact Hsigma.
  - intro x. apply value_closed, Hgamma.
Qed.

Lemma semantic_environment_term_update :
  forall Gamma sigma1 sigma2 gamma1 gamma2 rho x A v1 v2,
  semantic_environment Gamma sigma1 sigma2 gamma1 gamma2 rho ->
  locally_closed_ty A -> value_relation [] rho A v1 v2 ->
  semantic_environment (update Gamma x A) sigma1 sigma2
    (tm_update gamma1 x v1) (tm_update gamma2 x v2) rho.
Proof.
  intros Gamma sigma1 sigma2 gamma1 gamma2 rho x A v1 v2
    [Hsigma [Hgamma Hcontext]] HA Hvr.
  destruct (value_relation_values _ _ _ _ _ Hvr) as [Hv1 Hv2].
  split; [exact Hsigma|]. split.
  - intro y. unfold tm_update. destruct (Nat.eqb x y);
      auto using Hgamma.
  - intros y B Hlook. simpl in Hlook.
    rewrite Nat.eqb_sym in Hlook.
    unfold tm_update. destruct (Nat.eqb x y) eqn:E.
    + inversion Hlook; subst. split; [exact HA|exact Hvr].
    + apply Hcontext. exact Hlook.
Qed.

Lemma semantic_environment_type_update :
  forall Gamma sigma1 sigma2 gamma1 gamma2 rho X U1 U2 a,
  semantic_environment Gamma sigma1 sigma2 gamma1 gamma2 rho ->
  ~ In X (context_atoms Gamma) ->
  locally_closed_ty U1 -> locally_closed_ty U2 ->
  semantic_environment Gamma
    (ty_update sigma1 X U1) (ty_update sigma2 X U2)
    gamma1 gamma2 (relation_update rho X a).
Proof.
  intros Gamma sigma1 sigma2 gamma1 gamma2 rho X U1 U2 a
    [Hsigma [Hgamma Hcontext]] Hfresh HU1 HU2.
  split.
  - intro Y. unfold ty_update. destruct (Nat.eqb X Y);
      auto using Hsigma.
  - split; [exact Hgamma|].
    intros x T Hlook.
    destruct (Hcontext x T Hlook) as [HT Hvr].
    split; [exact HT|].
    assert (HTfresh : ~ In X (ty_atoms T)).
    { intro Hin. apply Hfresh. eapply lookup_atoms; eauto. }
    apply (proj2 (value_relation_rho_fresh T rho X a _ _ HT HTfresh)).
    exact Hvr.
Qed.

Lemma expression_succ : forall eta rho n1 n2,
  expression_relation eta rho Ty_Nat n1 n2 ->
  expression_relation eta rho Ty_Nat (tm_succ n1) (tm_succ n2).
Proof.
  intros eta rho n1 n2 [Hn1 [Hn2 [v1 [v2 [E1 [E2 Hr]]]]]].
  simpl in Hr. destruct Hr as [-> Hnum].
  split; [unfold locally_closed_tm in *; constructor; assumption|].
  split; [unfold locally_closed_tm in *; constructor; assumption|].
  exists (tm_succ v2), (tm_succ v2).
  split; [eapply EvalSucc; eauto|].
  split; [eapply EvalSucc; eauto|].
  simpl. split; [reflexivity|constructor; exact Hnum].
Qed.

Lemma expression_choice_left : forall eta rho T a1 a2 b1 b2,
  expression_relation eta rho T a1 a2 ->
  locally_closed_tm b1 -> locally_closed_tm b2 ->
  expression_relation eta rho T
    (tm_choice a1 b1) (tm_choice a2 b2).
Proof.
  intros eta rho T a1 a2 b1 b2
    [Ha1 [Ha2 [v1 [v2 [E1 [E2 Hr]]]]]] Hb1 Hb2.
  split; [unfold locally_closed_tm in *; constructor; assumption|].
  split; [unfold locally_closed_tm in *; constructor; assumption|].
  exists v1, v2. split; [eapply EvalChoiceLeft; eauto|].
  split; [eapply EvalChoiceLeft; eauto|exact Hr].
Qed.

Lemma value_relation_expression : forall eta rho T v1 v2,
  value_relation eta rho T v1 v2 ->
  expression_relation eta rho T v1 v2.
Proof.
  intros eta rho T v1 v2 Hvr.
  destruct (value_relation_values _ _ _ _ _ Hvr) as [Hv1 Hv2].
  split; [apply value_closed; exact Hv1|].
  split; [apply value_closed; exact Hv2|].
  exists v1, v2. split; [constructor; exact Hv1|].
  split; [constructor; exact Hv2|exact Hvr].
Qed.

Lemma ty_atoms_open_incl : forall T k X Y,
  In X (ty_atoms T) ->
  In X (ty_atoms (open_ty_rec k (Ty_FVar Y) T)).
Proof.
  induction T; intros k X Y H; simpl in *; try contradiction.
  - exact H.
  - repeat rewrite in_app_iff in *; intuition eauto.
  - eauto.
Qed.

Lemma tm_atoms_open_incl : forall t k x y,
  In x (tm_atoms t) ->
  In x (tm_atoms (open_tm_rec k (tm_fvar y) t)).
Proof.
  induction t; intros k x y H; simpl in *; try contradiction;
    try solve [exact H | eauto].
  all: repeat rewrite in_app_iff in *; intuition eauto.
Qed.

Lemma tm_atoms_open_ty_eq : forall t k U,
  tm_atoms (open_tm_ty_rec k U t) = tm_atoms t.
Proof.
  induction t; intros k U; simpl;
    repeat rewrite ?IHt1, ?IHt2, ?IHt3, ?IHt; reflexivity.
Qed.

Lemma tm_ty_atoms_open_tm_eq : forall t k x,
  tm_ty_atoms (open_tm_rec k (tm_fvar x) t) = tm_ty_atoms t.
Proof.
  induction t; intros k x; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
  - reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2, IHt3. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma tm_ty_atoms_open_ty_incl : forall t k X Y,
  In X (tm_ty_atoms t) ->
  In X (tm_ty_atoms (open_tm_ty_rec k (Ty_FVar Y) t)).
Proof.
  induction t; intros k X Y H; simpl in *; try contradiction;
    try solve [exact H | eauto].
  - repeat rewrite in_app_iff in *. destruct H as [H|H].
    + left. eapply ty_atoms_open_incl; eauto.
    + right. eapply IHt; eauto.
  - repeat rewrite in_app_iff in *; intuition eauto.
  - repeat rewrite in_app_iff in *. destruct H as [H|H].
    + left. eapply IHt; eauto.
    + right. eapply ty_atoms_open_incl; eauto.
  - repeat rewrite in_app_iff in *; intuition eauto.
  - repeat rewrite in_app_iff in *; intuition eauto.
Qed.

Lemma wf_ty_atoms_supported : forall Delta T,
  wf_ty Delta T -> forall Y, In Y (ty_atoms T) -> In Y Delta.
Proof.
  intros Delta T H; induction H; intros Y Hin; simpl in *.
  - destruct Hin as [->|[]]. exact H.
  - apply in_app_iff in Hin as [HA|HB]; eauto.
  - set (X := S (fold_right Nat.max 0 (L ++ ty_atoms T))).
    assert (HX : ~ In X (L ++ ty_atoms T))
      by (unfold X; apply fresh_atom).
    apply not_in_app in HX as [HXL HXT].
    specialize (H0 X HXL Y (ty_atoms_open_incl T 0 Y X Hin)).
    simpl in H0. destruct H0 as [E|Hdelta].
    + subst. contradiction.
    + exact Hdelta.
  - contradiction.
Qed.

Lemma has_type_term_atoms_supported : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall y, In y (tm_atoms t) ->
    exists A, lookup_context y Gamma = Some A.
Proof.
  intros Delta Gamma t T Hty; induction Hty; intros y Hin; simpl in *.
  - destruct Hin as [->|[]]. exists T. exact H.
  - set (x := S (fold_right Nat.max 0 (L ++ tm_atoms t2))).
    assert (Hx : ~ In x (L ++ tm_atoms t2))
      by (unfold x; apply fresh_atom).
    apply not_in_app in Hx as [HxL HxBody].
    specialize (H1 x HxL y (tm_atoms_open_incl t2 0 y x Hin)).
    destruct H1 as [A Hlook].
    simpl in Hlook.
    assert (E : Nat.eqb y x = false).
    { apply Nat.eqb_neq. intro Heq. subst. contradiction. }
    rewrite E in Hlook.
    exists A. exact Hlook.
  - apply in_app_iff in Hin as [HA|HB]; eauto.
  - set (X := S (fold_right Nat.max 0 L)).
    specialize (H0 X (fresh_atom L) y).
    unfold open_tm_ty in H0.
    rewrite tm_atoms_open_ty_eq in H0.
    exact (H0 Hin).
  - eauto.
  - contradiction.
  - eauto.
  - repeat rewrite in_app_iff in Hin.
    destruct Hin as [HN|[HB|HS]]; eauto.
  - apply in_app_iff in Hin as [HA|HB]; eauto.
Qed.

Lemma has_type_ty_atoms_supported : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall Y, In Y (tm_ty_atoms t) -> In Y Delta.
Proof.
  intros Delta Gamma t T Hty; induction Hty; intros Y Hin; simpl in *.
  - contradiction.
  - apply in_app_iff in Hin as [HA|HB].
    + eapply wf_ty_atoms_supported; eauto.
    + set (x := S (fold_right Nat.max 0 L)).
      specialize (H1 x (fresh_atom L) Y).
      unfold open_tm in H1.
      rewrite tm_ty_atoms_open_tm_eq in H1.
      exact (H1 HB).
  - apply in_app_iff in Hin as [HA|HB]; eauto.
  - set (X := S (fold_right Nat.max 0 (L ++ tm_ty_atoms t))).
    assert (HX : ~ In X (L ++ tm_ty_atoms t))
      by (unfold X; apply fresh_atom).
    apply not_in_app in HX as [HXL HXt].
    specialize (H0 X HXL Y (tm_ty_atoms_open_ty_incl t 0 Y X Hin)).
    simpl in H0. destruct H0 as [E|Hdelta].
    + subst. contradiction.
    + exact Hdelta.
  - apply in_app_iff in Hin as [HA|HB].
    + eauto.
    + eapply wf_ty_atoms_supported; eauto.
  - contradiction.
  - eauto.
  - repeat rewrite in_app_iff in Hin.
    destruct Hin as [HN|[HB|HS]]; eauto.
  - apply in_app_iff in Hin as [HA|HB]; eauto.
Qed.

Lemma instantiate_ty_id : forall T sigma,
  ty_atoms T = [] -> instantiate_ty sigma T = T.
Proof.
  induction T; intros sigma H; simpl in *; try reflexivity.
  - discriminate.
  - apply app_eq_nil in H as [HA HB].
    f_equal; eauto.
  - f_equal; eauto.
Qed.

Lemma instantiate_tm_id : forall t sigma gamma,
  tm_atoms t = [] -> tm_ty_atoms t = [] ->
  instantiate_tm sigma gamma t = t.
Proof.
  induction t; intros sigma gamma Hterm Htype; simpl in *;
    repeat match goal with
    | H : _ ++ _ = [] |- _ => apply app_eq_nil in H as [? ?]
    end; simpl; f_equal; eauto using instantiate_ty_id.
Qed.

Lemma closed_typed_instantiate_id : forall t T sigma gamma,
  has_type [] empty t T -> instantiate_tm sigma gamma t = t.
Proof.
  intros t T sigma gamma Hty.
  apply instantiate_tm_id.
  - destruct (tm_atoms t) as [|x xs] eqn:E; [reflexivity|].
    exfalso. destruct (has_type_term_atoms_supported [] empty t T Hty x)
      as [A HA]; [rewrite E; simpl; auto|discriminate HA].
  - destruct (tm_ty_atoms t) as [|X xs] eqn:E; [reflexivity|].
    exfalso. pose proof (has_type_ty_atoms_supported [] empty t T Hty X) as H.
    apply H. rewrite E. simpl; auto.
Qed.

Theorem fundamental_theorem : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall sigma1 sigma2 gamma1 gamma2 rho,
    semantic_environment Gamma sigma1 sigma2 gamma1 gamma2 rho ->
    expression_relation [] rho T
      (instantiate_tm sigma1 gamma1 t)
      (instantiate_tm sigma2 gamma2 t).
Proof.
  intros Delta Gamma t T Hty; induction Hty;
    intros sigma1 sigma2 gamma1 gamma2 rho Henv; simpl.
  - destruct Henv as [_ [_ Hctx]].
    destruct (Hctx x T H) as [_ Hvr].
    apply value_relation_expression. exact Hvr.
  - destruct Henv as [Hsigma [Hgamma Hctx]].
    assert (Hlc1 : locally_closed_tm
      (instantiate_tm sigma1 gamma1 (tm_abs T1 t2))).
    { eapply instantiated_typed_closed.
      - eapply T_Abs; eauto.
      - intro X. exact (proj1 (Hsigma X)).
      - intro y. exact (proj1 (Hgamma y)). }
    assert (Hlc2 : locally_closed_tm
      (instantiate_tm sigma2 gamma2 (tm_abs T1 t2))).
    { eapply instantiated_typed_closed.
      - eapply T_Abs; eauto.
      - intro X. exact (proj2 (Hsigma X)).
      - intro y. exact (proj2 (Hgamma y)). }
    apply value_relation_expression. simpl.
    split; [constructor; exact Hlc1|].
    split; [constructor; exact Hlc2|].
    exists (instantiate_ty sigma1 T1), (instantiate_tm sigma1 gamma1 t2),
      (instantiate_ty sigma2 T1), (instantiate_tm sigma2 gamma2 t2).
    split; [reflexivity|]. split; [reflexivity|].
    intros arg1 arg2 Harg.
    set (x := S (fold_right Nat.max 0 (L ++ tm_atoms t2))).
    assert (Hx : ~ In x (L ++ tm_atoms t2))
      by (unfold x; apply fresh_atom).
    apply not_in_app in Hx as [HxL HxBody].
    assert (Henv' : semantic_environment (update Gamma x T1)
      sigma1 sigma2 (tm_update gamma1 x arg1)
      (tm_update gamma2 x arg2) rho).
    { apply semantic_environment_term_update; [|apply wf_ty_closed in H; exact H|exact Harg].
      split; [exact Hsigma|]. split; assumption. }
    specialize (H1 x HxL sigma1 sigma2
      (tm_update gamma1 x arg1) (tm_update gamma2 x arg2) rho Henv').
    pose proof (instantiate_tm_open t2 0 x sigma1 gamma1 arg1 HxBody
      (fun y => value_closed _ (proj1 (Hgamma y)))) as E1.
    pose proof (instantiate_tm_open t2 0 x sigma2 gamma2 arg2 HxBody
      (fun y => value_closed _ (proj2 (Hgamma y)))) as E2.
    unfold open_tm in H1.
    rewrite E1, E2 in H1. exact H1.
  - eapply expression_app; eauto.
  - destruct Henv as [Hsigma [Hgamma Hctx]].
    assert (Hlc1 : locally_closed_tm
      (instantiate_tm sigma1 gamma1 (tm_tabs t))).
    { eapply instantiated_typed_closed.
      - eapply T_TAbs; eauto.
      - intro X. exact (proj1 (Hsigma X)).
      - intro y. exact (proj1 (Hgamma y)). }
    assert (Hlc2 : locally_closed_tm
      (instantiate_tm sigma2 gamma2 (tm_tabs t))).
    { eapply instantiated_typed_closed.
      - eapply T_TAbs; eauto.
      - intro X. exact (proj2 (Hsigma X)).
      - intro y. exact (proj2 (Hgamma y)). }
    apply value_relation_expression. simpl.
    split; [constructor; exact Hlc1|].
    split; [constructor; exact Hlc2|].
    exists (instantiate_tm sigma1 gamma1 t),
      (instantiate_tm sigma2 gamma2 t).
    split; [reflexivity|]. split; [reflexivity|].
    intros U1 U2 a HU1 HU2.
    set (X := S (fold_right Nat.max 0
      (L ++ tm_ty_atoms t ++ ty_atoms T ++ context_atoms Gamma))).
    assert (HX : ~ In X
      (L ++ tm_ty_atoms t ++ ty_atoms T ++ context_atoms Gamma))
      by (unfold X; apply fresh_atom).
    assert (HXL : ~ In X L) by (intro Hin; apply HX; repeat rewrite in_app_iff; tauto).
    assert (HXt : ~ In X (tm_ty_atoms t))
      by (intro Hin; apply HX; repeat rewrite in_app_iff; tauto).
    assert (HXT : ~ In X (ty_atoms T))
      by (intro Hin; apply HX; repeat rewrite in_app_iff; tauto).
    assert (HXctx : ~ In X (context_atoms Gamma))
      by (intro Hin; apply HX; repeat rewrite in_app_iff; tauto).
    assert (Henv' : semantic_environment Gamma
      (ty_update sigma1 X U1) (ty_update sigma2 X U2)
      gamma1 gamma2 (relation_update rho X a)).
    { apply semantic_environment_type_update; auto.
      split; [exact Hsigma|]. split; assumption. }
    specialize (H0 X HXL (ty_update sigma1 X U1)
      (ty_update sigma2 X U2) gamma1 gamma2
      (relation_update rho X a) Henv').
    pose proof (instantiate_tm_ty_open t 0 X sigma1 gamma1 U1 HXt
      (fun Y => proj1 (Hsigma Y))
      (fun y => value_closed _ (proj1 (Hgamma y)))) as E1.
    pose proof (instantiate_tm_ty_open t 0 X sigma2 gamma2 U2 HXt
      (fun Y => proj2 (Hsigma Y))
      (fun y => value_closed _ (proj2 (Hgamma y)))) as E2.
    unfold open_tm_ty in H0.
    rewrite E1, E2 in H0.
    apply (proj1 (expression_lifting_equiv _ _ _ _
      (fun p q => value_relation_open_fvar T [] rho X a p q HXT))).
    exact H0.
  - destruct Henv as [Hsigma [Hgamma Hctx]].
    eapply expression_tapp.
    + apply wf_ty_closed in H. exact H.
    + eapply instantiate_ty_closed; [apply wf_ty_closed in H; exact H|].
      intro X. exact (proj1 (Hsigma X)).
    + eapply instantiate_ty_closed; [apply wf_ty_closed in H; exact H|].
      intro X. exact (proj2 (Hsigma X)).
    + apply IHHty. split; [exact Hsigma|]. split; assumption.
  - apply value_relation_expression. simpl. split; reflexivity || constructor.
  - apply expression_succ. apply IHHty. exact Henv.
  - eapply expression_rec; eauto.
  - eapply expression_choice_left; eauto.
    + eapply instantiated_typed_closed; eauto.
      * destruct Henv as [Hsigma _]. intro X. exact (proj1 (Hsigma X)).
      * destruct Henv as [_ [Hgamma _]]. intro x. exact (proj1 (Hgamma x)).
    + eapply instantiated_typed_closed; eauto.
      * destruct Henv as [Hsigma _]. intro X. exact (proj2 (Hsigma X)).
      * destruct Henv as [_ [Hgamma _]]. intro x. exact (proj2 (Hgamma x)).
Qed.

Definition singleton_candidate (v : tm) (Hv : value v) : binary_candidate.
Proof.
  refine {| candidate_relation := fun p q => p = v /\ q = v |}.
  intros p q [-> ->]. split; exact Hv.
Defined.

Lemma expression_tapp_candidate : forall eta rho T f1 f2 U1 U2 a,
  expression_relation eta rho (Ty_All T) f1 f2 ->
  locally_closed_ty U1 -> locally_closed_ty U2 ->
  expression_relation (a :: eta) rho T
    (tm_tapp f1 U1) (tm_tapp f2 U2).
Proof.
  intros eta rho T f1 f2 U1 U2 a
    [Hf1 [Hf2 [vf1 [vf2 [Ef1 [Ef2 Hfun]]]]]] HU1 HU2.
  simpl in Hfun.
  destruct Hfun as [_ [_ [body1 [body2 [E1 [E2 Hbody]]]]]].
  subst vf1 vf2.
  specialize (Hbody U1 U2 a HU1 HU2).
  destruct Hbody as [_ [_ [r1 [r2 [Er1 [Er2 Hr]]]]]].
  split; [unfold locally_closed_tm in *; constructor; assumption|].
  split; [unfold locally_closed_tm in *; constructor; assumption|].
  exists r1, r2. split; [eapply EvalTApp; eauto|].
  split; [eapply EvalTApp; eauto|exact Hr].
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
  intros t Hty U v HU Hv _.
  set (sigma := fun _ : atom => Ty_Nat).
  set (gamma := fun _ : atom => tm_zero).
  set (rho := fun _ : atom => None : option binary_candidate).
  set (a := singleton_candidate v Hv).
  assert (Henv : semantic_environment empty sigma sigma gamma gamma rho).
  { split.
    - intro X. split; constructor.
    - split.
      + intro x. split; constructor; constructor.
      + intros x T Hlook. discriminate Hlook. }
  pose proof (fundamental_theorem [] empty t
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) Hty
    sigma sigma gamma gamma rho Henv) as Hfund.
  rewrite (closed_typed_instantiate_id t
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) sigma gamma Hty)
    in Hfund.
  pose proof (expression_tapp_candidate [] rho
    (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))
    t t U U a Hfund (wf_ty_closed [] U HU) (wf_ty_closed [] U HU))
    as Htap.
  assert (Harg : expression_relation [a] rho (Ty_BVar 0) v v).
  { apply value_relation_expression. simpl.
    unfold a, singleton_candidate. simpl. split; reflexivity. }
  pose proof (expression_app [a] rho (Ty_BVar 0) (Ty_BVar 0)
    (tm_tapp t U) (tm_tapp t U) v v Htap Harg) as Happ.
  destruct Happ as [_ [_ [r1 [r2 [Eapp [_ Hr]]]]]].
  simpl in Hr. unfold a, singleton_candidate in Hr. simpl in Hr.
  destruct Hr as [-> _].
  apply evaluates_multi. exact Eapp.
Qed.

End SystemFParametricityNondeterminismRecursionMediumTask.
