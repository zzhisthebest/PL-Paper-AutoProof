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

Lemma value_closed : forall v, value v -> locally_closed_tm v.
Proof. intros v H; inversion H; subst; unfold locally_closed_tm; eauto. Qed.

Lemma evaluates_closed : forall t v, evaluates t v -> locally_closed_tm t.
Proof.
  intros t v H; induction H; [apply value_closed; assumption|..];
    unfold locally_closed_tm in *;
    eauto using value_closed, lc_tm_app,
    lc_tm_tapp, lc_tm_if, lc_tm_choice.
Qed.

Lemma evaluates_value : forall t v, evaluates t v -> value v.
Proof. intros t v H; induction H; assumption. Qed.

Lemma multi_app_left : forall f f' arg,
  f -->* f' -> locally_closed_tm arg ->
  tm_app f arg -->* tm_app f' arg.
Proof.
  intros f f' arg H; induction H; intros Harg; eauto using multi.
  eapply multi_step; [eapply ST_App1; eauto|eauto].
Qed.

Lemma multi_app_right : forall arg arg' f,
  arg -->* arg' -> value f ->
  tm_app f arg -->* tm_app f arg'.
Proof.
  intros arg arg' f H; induction H; intros Hf; eauto using multi.
  eapply multi_step; [eapply ST_App2; eauto|eauto].
Qed.

Lemma multi_tapp : forall t t' U,
  t -->* t' -> locally_closed_ty U ->
  tm_tapp t U -->* tm_tapp t' U.
Proof.
  intros t t' U H; induction H; intros HU; eauto using multi.
  eapply multi_step; [eapply ST_TApp; eauto|eauto].
Qed.

Lemma multi_if : forall c c' t u,
  c -->* c' -> locally_closed_tm t -> locally_closed_tm u ->
  tm_if c t u -->* tm_if c' t u.
Proof.
  intros c c' t u H; induction H; intros Ht Hu; eauto using multi.
  eapply multi_step; [eapply ST_If; eauto|eauto].
Qed.

Lemma multi_trans : forall a b c, a -->* b -> b -->* c -> a -->* c.
Proof. intros a b c H; induction H; eauto using multi. Qed.

Lemma evaluates_multi : forall t v, evaluates t v -> t -->* v.
Proof.
  intros t v H; induction H.
  - constructor.
  - eapply multi_trans; [eapply multi_app_left; eauto using evaluates_closed|].
    eapply multi_trans; [eapply multi_app_right; eauto using evaluates_value|].
    eapply multi_step; [eapply ST_AppAbs; eauto using evaluates_value, value_closed|assumption].
  - eapply multi_trans; [eapply multi_tapp; eauto|].
    eapply multi_step; [eapply ST_TAppTabs; eauto using evaluates_value, value_closed|assumption].
  - eapply multi_trans; [eapply multi_if; eauto using evaluates_closed|].
    eapply multi_step; [eapply ST_IfTrue; eauto using evaluates_closed|assumption].
  - eapply multi_trans; [eapply multi_if; eauto using evaluates_closed|].
    eapply multi_step; [eapply ST_IfFalse; eauto using evaluates_closed|assumption].
  - eapply multi_step; [eapply ST_ChoiceLeft; eauto using evaluates_closed|assumption].
  - eapply multi_step; [eapply ST_ChoiceRight; eauto using evaluates_closed|assumption].
Qed.

Lemma lc_ty_open_inverse : forall T k X,
  lc_ty_at k (open_ty_rec k (Ty_FVar X) T) -> lc_ty_at (S k) T.
Proof.
  induction T; intros k X H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst; constructor; lia.
    + inversion H; subst; constructor; lia.
  - constructor.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - constructor.
Qed.

Lemma lc_tm_open_inverse : forall t K k x,
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) -> lc_tm_at K (S k) t.
Proof.
  induction t; intros K k x H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst; constructor; lia.
    + inversion H; subst; constructor; lia.
  - constructor.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - constructor.
  - constructor.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
Qed.

Lemma lc_tm_ty_open_inverse : forall t K k X,
  lc_tm_at K k (open_tm_ty_rec K (Ty_FVar X) t) -> lc_tm_at (S K) k t.
Proof.
  induction t; intros K k X H; simpl in H; inversion H; subst;
    eauto using lc_tm_at, lc_ty_open_inverse.
Qed.

Lemma fresh_exists : forall L : list atom, exists x, ~ In x L.
Proof.
  intro L; exists (S (fold_right Nat.max 0 L)).
  assert (forall y, In y L -> y <= fold_right Nat.max 0 L) as Hmax.
  { induction L as [|a L IH]; simpl; intros y Hy.
    - contradiction.
    - destruct Hy as [->|Hy]; [apply Nat.le_max_l|].
      eapply Nat.le_trans; [apply IH; exact Hy|apply Nat.le_max_r]. }
  intro Hin; specialize (Hmax _ Hin); lia.
Qed.

Lemma wf_ty_closed : forall Delta T,
  wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H; induction H; unfold locally_closed_ty in *;
    eauto using lc_ty_at.
  destruct (fresh_exists L) as [X HX].
  constructor.
  apply (lc_ty_open_inverse T 0 X); exact (H0 X HX).
Qed.

Lemma typing_closed : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T H; induction H; unfold locally_closed_tm in *;
    eauto using lc_tm_at, wf_ty_closed.
  - destruct (fresh_exists L) as [x Hx].
    apply lc_tm_abs; [eapply wf_ty_closed; eassumption|].
    apply (lc_tm_open_inverse t2 0 0 x); apply H1; assumption.
  - destruct (fresh_exists L) as [X HX].
    apply lc_tm_tabs.
    apply (lc_tm_ty_open_inverse t 0 0 X); apply H0; assumption.
  - apply lc_tm_tapp; [assumption|eapply wf_ty_closed; eassumption].
Qed.

Fixpoint interpret_ty (theta : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => theta X
  | Ty_Arrow A B => Ty_Arrow (interpret_ty theta A) (interpret_ty theta B)
  | Ty_All A => Ty_All (interpret_ty theta A)
  | Ty_Bool => Ty_Bool
  end.

Fixpoint interpret_tm (theta : atom -> ty) (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_abs T body => tm_abs (interpret_ty theta T) (interpret_tm theta sigma body)
  | tm_app f arg => tm_app (interpret_tm theta sigma f) (interpret_tm theta sigma arg)
  | tm_tabs body => tm_tabs (interpret_tm theta sigma body)
  | tm_tapp f U => tm_tapp (interpret_tm theta sigma f) (interpret_ty theta U)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if c a b => tm_if (interpret_tm theta sigma c) (interpret_tm theta sigma a) (interpret_tm theta sigma b)
  | tm_choice a b => tm_choice (interpret_tm theta sigma a) (interpret_tm theta sigma b)
  end.

Fixpoint free_ty (T : ty) : list atom :=
  match T with
  | Ty_BVar _ | Ty_Bool => []
  | Ty_FVar X => [X]
  | Ty_Arrow A B => free_ty A ++ free_ty B
  | Ty_All A => free_ty A
  end.

Fixpoint free_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_true | tm_false => []
  | tm_fvar x => [x]
  | tm_abs _ body | tm_tabs body => free_tm body
  | tm_app a b | tm_choice a b => free_tm a ++ free_tm b
  | tm_tapp a _ => free_tm a
  | tm_if c a b => free_tm c ++ free_tm a ++ free_tm b
  end.

Fixpoint free_tm_ty (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_fvar _ | tm_true | tm_false => []
  | tm_abs T body => free_ty T ++ free_tm_ty body
  | tm_tabs body => free_tm_ty body
  | tm_app a b | tm_choice a b => free_tm_ty a ++ free_tm_ty b
  | tm_tapp a U => free_tm_ty a ++ free_ty U
  | tm_if c a b => free_tm_ty c ++ free_tm_ty a ++ free_tm_ty b
  end.

Definition replace_ty (theta : atom -> ty) X U :=
  fun Y => if Nat.eqb X Y then U else theta Y.
Definition replace_tm (sigma : atom -> tm) x v :=
  fun y => if Nat.eqb x y then v else sigma y.

Lemma lc_ty_weaken : forall T k j, lc_ty_at k T -> k <= j -> lc_ty_at j T.
Proof.
  intros T k j H; revert j; induction H; intros j Hj;
    eauto using lc_ty_at with arith.
Qed.

Lemma lc_tm_weaken : forall t K k J j,
  lc_tm_at K k t -> K <= J -> k <= j -> lc_tm_at J j t.
Proof.
  intros t K k J j H; revert J j;
    induction H; intros J j HJ Hj; eauto using lc_tm_at, lc_ty_weaken with arith.
Qed.

Lemma lc_ty_open_idle : forall T k U, lc_ty_at k T -> open_ty_rec k U T = T.
Proof.
  induction T; intros k U H; simpl; inversion H; subst; f_equal; eauto.
  - destruct (Nat.eqb k n) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
Qed.

Lemma lc_tm_open_idle : forall t K k u,
  lc_tm_at K k t -> open_tm_rec k u t = t.
Proof.
  induction t; intros K k u H; simpl; inversion H; subst;
    try (f_equal; eauto); try reflexivity.
  destruct (Nat.eqb k n) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
Qed.

Lemma lc_tm_ty_open_idle : forall t K k U,
  lc_tm_at K k t -> open_tm_ty_rec K U t = t.
Proof.
  induction t; intros K k U H; simpl; inversion H; subst;
    try (f_equal; eauto using lc_ty_open_idle); try reflexivity.
Qed.

Lemma interpret_ty_closed : forall T k theta,
  lc_ty_at k T -> (forall X, locally_closed_ty (theta X)) ->
  lc_ty_at k (interpret_ty theta T).
Proof.
  intros T k theta H; revert theta; induction H; intros theta Htheta;
    simpl; eauto using lc_ty_at, lc_ty_weaken.
  eapply lc_ty_weaken; [apply Htheta|lia].
Qed.

Lemma interpret_tm_closed : forall t K k theta sigma,
  lc_tm_at K k t ->
  (forall X, locally_closed_ty (theta X)) ->
  (forall x, locally_closed_tm (sigma x)) ->
  lc_tm_at K k (interpret_tm theta sigma t).
Proof.
  intros t K k theta sigma H; revert theta sigma;
    induction H; intros theta sigma Htheta Hsigma; simpl;
    eauto using lc_tm_at, interpret_ty_closed.
  eapply lc_tm_weaken; [apply Hsigma|lia|lia].
Qed.

Lemma relation_values : forall T eta rho v1 v2,
  value_relation eta rho T v1 v2 -> value v1 /\ value v2.
Proof.
  induction T; intros eta rho v1 v2 H; simpl in H.
  - destruct (nth_error eta n) as [a|]; [exact (candidate_values a _ _ H)|contradiction].
  - destruct (rho a) as [r|]; [exact (candidate_values r _ _ H)|contradiction].
  - tauto.
  - tauto.
  - destruct H as [[-> ->]|[-> ->]]; auto using value.
Qed.

Lemma expression_value : forall R v1 v2,
  value v1 -> value v2 -> R v1 v2 -> expression_lifting R v1 v2.
Proof.
  intros R v1 v2 H1 H2 HR.
  repeat split; eauto using value_closed.
  exists v1, v2; eauto using evaluates.
Qed.

Lemma expression_app : forall rho A B f1 f2 arg1 arg2,
  expression_lifting (value_relation [] rho B) arg1 arg2 ->
  expression_lifting (value_relation [] rho (Ty_Arrow B A)) f1 f2 ->
  expression_lifting (value_relation [] rho A) (tm_app f1 arg1) (tm_app f2 arg2).
Proof.
  intros rho A B f1 f2 arg1 arg2 [Harg1 [Harg2 [v1 [v2 [He1 [He2 HRarg]]]]]]
    [Hf1 [Hf2 [g1 [g2 [HfEval1 [HfEval2 HRf]]]]]].
  simpl in HRf.
  destruct HRf as [_ [_ [U1 [body1 [U2 [body2 [-> [-> Happly]]]]]]]].
  specialize (Happly v1 v2 HRarg).
  destruct Happly as [_ [_ [w1 [w2 [Hbody1 [Hbody2 HR]]]]]].
  split; [constructor; assumption|].
  split; [constructor; assumption|].
  exists w1, w2; repeat split; try assumption.
  - eapply EvalApp; eauto.
  - eapply EvalApp; eauto.
Qed.

Lemma lifting_iff : forall R S t1 t2,
  (forall v1 v2, R v1 v2 <-> S v1 v2) ->
  expression_lifting R t1 t2 <-> expression_lifting S t1 t2.
Proof.
  intros R S t1 t2 H; unfold expression_lifting, results_match;
    split; intros [H1 [H2 [v1 [v2 [E1 [E2 HR]]]]]];
    repeat split; try assumption; exists v1, v2; repeat split;
    try assumption; apply H; assumption.
Qed.

Lemma relation_eta_agree : forall T k eta1 eta2 rho v1 v2,
  lc_ty_at k T ->
  (forall i, i < k -> nth_error eta1 i = nth_error eta2 i) ->
  (value_relation eta1 rho T v1 v2 <-> value_relation eta2 rho T v1 v2).
Proof.
  induction T; intros k eta1 eta2 rho v1 v2 Hlc Hagree;
    inversion Hlc; subst; simpl.
  - match goal with Hlt : n < k |- _ => rewrite (Hagree n Hlt) end; tauto.
  - tauto.
  - assert (Hdom : forall p q,
        value_relation eta1 rho T1 p q <-> value_relation eta2 rho T1 p q)
      by (intros; eapply IHT1; eauto).
    assert (Hran : forall p q,
        value_relation eta1 rho T2 p q <-> value_relation eta2 rho T2 p q)
      by (intros; eapply IHT2; eauto).
    split; intros [Hv1 [Hv2 [U1 [b1 [U2 [b2 [-> [-> HF]]]]]]]];
      refine (conj Hv1 (conj Hv2 _));
      exists U1, b1, U2, b2;
      refine (conj eq_refl (conj eq_refl _));
      intros p q Harg.
    + apply (proj1 (lifting_iff _ _ _ _ Hran)).
      apply HF; apply (proj2 (Hdom _ _)); assumption.
    + apply (proj2 (lifting_iff _ _ _ _ Hran)).
      apply HF; apply (proj1 (Hdom _ _)); assumption.
  - split; intros [Hv1 [Hv2 [b1 [b2 [-> [-> HF]]]]]];
      refine (conj Hv1 (conj Hv2 _));
      exists b1, b2;
      refine (conj eq_refl (conj eq_refl _));
      intros U1 U2 a Hu1 Hu2;
      assert (Hag : forall i, i < S k ->
        nth_error (a :: eta1) i = nth_error (a :: eta2) i)
        by (intros [|i] Hi; simpl; [reflexivity|apply Hagree; lia]).
    + apply (proj1 (lifting_iff _ _ _ _
          (fun p q => IHT (S k) (a :: eta1) (a :: eta2) rho p q H1 Hag))).
      apply HF; assumption.
    + apply (proj2 (lifting_iff _ _ _ _
          (fun p q => IHT (S k) (a :: eta1) (a :: eta2) rho p q H1 Hag))).
      apply HF; assumption.
  - tauto.
Qed.

Lemma relation_open : forall T prefix rho rho' U cand p q,
  (forall X, In X (free_ty T) -> rho X = rho' X) ->
  (forall eta v1 v2,
    candidate_relation cand v1 v2 <-> value_relation eta rho' U v1 v2) ->
  (value_relation (prefix ++ [cand]) rho T p q <->
    value_relation prefix rho' (open_ty_rec (length prefix) U T) p q).
Proof.
  induction T; intros prefix rho rho' U cand p q Henv Hcand; simpl.
  - destruct (n <? length prefix) eqn:Hlt.
    + apply Nat.ltb_lt in Hlt.
      assert (E : (length prefix =? n) = false) by (apply Nat.eqb_neq; lia).
      rewrite E.
      rewrite nth_error_app1 by assumption; tauto.
    + apply Nat.ltb_ge in Hlt.
      destruct (Nat.eq_dec n (length prefix)) as [Heq|Hgt].
      * subst n; rewrite Nat.eqb_refl.
        rewrite nth_error_app2 by lia.
        replace (length prefix - length prefix) with 0 by lia.
        simpl; apply Hcand.
      * assert (E : (length prefix =? n) = false) by (apply Nat.eqb_neq; lia).
        rewrite E.
        rewrite nth_error_app2 by lia.
        assert (Hnone : nth_error prefix n = None) by (apply nth_error_None; lia).
        simpl.
        rewrite Hnone.
        replace (nth_error [cand] (n - length prefix)) with
          (@None binary_candidate).
        2:{ destruct (n - length prefix) as [|[|m]] eqn:Eindex; simpl; auto; lia. }
        tauto.
  - rewrite (Henv a (or_introl eq_refl)); tauto.
  - assert (Henv1 : forall X, In X (free_ty T1) -> rho X = rho' X).
    { intros X HX; apply Henv; apply in_or_app; left; assumption. }
    assert (Henv2 : forall X, In X (free_ty T2) -> rho X = rho' X).
    { intros X HX; apply Henv; apply in_or_app; right; assumption. }
    assert (Hdom : forall v1 v2,
      value_relation (prefix ++ [cand]) rho T1 v1 v2 <->
      value_relation prefix rho' (open_ty_rec (length prefix) U T1) v1 v2)
      by (intros; apply IHT1; assumption).
    assert (Hran : forall v1 v2,
      value_relation (prefix ++ [cand]) rho T2 v1 v2 <->
      value_relation prefix rho' (open_ty_rec (length prefix) U T2) v1 v2)
      by (intros; apply IHT2; assumption).
    split; intros [Hv1 [Hv2 [U1 [b1 [U2 [b2 [-> [-> HF]]]]]]]];
      refine (conj Hv1 (conj Hv2 _)); exists U1, b1, U2, b2;
      refine (conj eq_refl (conj eq_refl _)); intros arg1 arg2 Harg.
    + apply (proj1 (lifting_iff _ _ _ _ Hran)).
      apply HF; apply (proj2 (Hdom _ _)); exact Harg.
    + apply (proj2 (lifting_iff _ _ _ _ Hran)).
      apply HF; apply (proj1 (Hdom _ _)); exact Harg.
  - split; intros [Hv1 [Hv2 [b1 [b2 [-> [-> HF]]]]]];
      refine (conj Hv1 (conj Hv2 _)); exists b1, b2;
      refine (conj eq_refl (conj eq_refl _)); intros U1 U2 candidate Hu1 Hu2;
      change (expression_lifting
        (value_relation ((candidate :: prefix) ++ [cand]) rho T) _ _)
        in HF || idtac.
    + apply (proj1 (lifting_iff _ _ _ _
        (fun v1 v2 => IHT (candidate :: prefix) rho rho' U cand v1 v2 Henv Hcand))).
      apply HF; assumption.
    + apply (proj2 (lifting_iff _ _ _ _
        (fun v1 v2 => IHT (candidate :: prefix) rho rho' U cand v1 v2 Henv Hcand))).
      apply HF; assumption.
  - tauto.
Qed.

Lemma absent_app : forall (A B : list atom) x,
  ~ In x (A ++ B) -> ~ In x A /\ ~ In x B.
Proof.
  intros A B x H; split; intro Hin; apply H; apply in_or_app;
    [left|right]; assumption.
Qed.

Lemma interpret_open_tm : forall t k theta sigma x v,
  ~ In x (free_tm t) ->
  (forall y, locally_closed_tm (sigma y)) ->
  interpret_tm theta (replace_tm sigma x v)
    (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k v (interpret_tm theta sigma t).
Proof.
  induction t; intros k theta sigma x v Hfresh Hsigma; simpl in *;
    try reflexivity.
  - destruct (Nat.eqb k n); simpl; [unfold replace_tm; rewrite Nat.eqb_refl|]; reflexivity.
  - assert (x <> a) by (intro E; subst; apply Hfresh; auto).
    unfold replace_tm.
    assert (E : (x =? a) = false) by (apply Nat.eqb_neq; assumption).
    rewrite E.
    symmetry; apply (lc_tm_open_idle (sigma a) 0 k v).
    eapply lc_tm_weaken; [apply Hsigma|lia|lia].
  - f_equal; apply IHt; assumption.
  - apply absent_app in Hfresh as [Hleft Hright].
    rewrite (IHt1 k theta sigma x v Hleft Hsigma).
    rewrite (IHt2 k theta sigma x v Hright Hsigma); reflexivity.
  - f_equal; apply IHt; assumption.
  - f_equal; apply IHt; assumption.
  - apply absent_app in Hfresh as [Hc Hrest].
    apply absent_app in Hrest as [Ha Hb].
    rewrite (IHt1 k theta sigma x v Hc Hsigma).
    rewrite (IHt2 k theta sigma x v Ha Hsigma).
    rewrite (IHt3 k theta sigma x v Hb Hsigma); reflexivity.
  - apply absent_app in Hfresh as [Ha Hb].
    rewrite (IHt1 k theta sigma x v Ha Hsigma).
    rewrite (IHt2 k theta sigma x v Hb Hsigma); reflexivity.
Qed.

Lemma interpret_open_ty : forall T k theta X U,
  ~ In X (free_ty T) ->
  (forall Y, locally_closed_ty (theta Y)) ->
  interpret_ty (replace_ty theta X U) (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k U (interpret_ty theta T).
Proof.
  induction T; intros k theta X U Hfresh Htheta; simpl in *;
    try reflexivity.
  - destruct (Nat.eqb k n) eqn:E; simpl.
    + unfold replace_ty; rewrite Nat.eqb_refl; reflexivity.
    + reflexivity.
  - assert (X <> a) by (intro E; subst; apply Hfresh; auto).
    unfold replace_ty.
    assert (E : (X =? a) = false) by (apply Nat.eqb_neq; assumption).
    rewrite E.
    symmetry; eapply lc_ty_open_idle.
    eapply lc_ty_weaken; [apply Htheta|lia].
  - apply absent_app in Hfresh as [Ha Hb].
    rewrite (IHT1 k theta X U Ha Htheta).
    rewrite (IHT2 k theta X U Hb Htheta); reflexivity.
  - f_equal; apply IHT; assumption.
Qed.

Lemma interpret_open_tm_ty : forall t k theta sigma X U,
  ~ In X (free_tm_ty t) ->
  (forall Y, locally_closed_ty (theta Y)) ->
  (forall x, locally_closed_tm (sigma x)) ->
  interpret_tm (replace_ty theta X U) sigma
    (open_tm_ty_rec k (Ty_FVar X) t) =
  open_tm_ty_rec k U (interpret_tm theta sigma t).
Proof.
  induction t; intros k theta sigma X U Hfresh Htheta Hsigma; simpl in *;
    try reflexivity.
  - symmetry; apply (lc_tm_ty_open_idle (sigma a) k 0 U).
    eapply lc_tm_weaken; [apply Hsigma|lia|lia].
  - apply absent_app in Hfresh as [HT Hbody].
    rewrite (interpret_open_ty _ _ _ _ _ HT Htheta).
    rewrite (IHt _ _ _ _ _ Hbody Htheta Hsigma); reflexivity.
  - apply absent_app in Hfresh as [Ha Hb].
    rewrite (IHt1 _ _ _ _ _ Ha Htheta Hsigma).
    rewrite (IHt2 _ _ _ _ _ Hb Htheta Hsigma); reflexivity.
  - f_equal; apply IHt; assumption.
  - apply absent_app in Hfresh as [Ha HU].
    rewrite (IHt _ _ _ _ _ Ha Htheta Hsigma).
    rewrite (interpret_open_ty _ _ _ _ _ HU Htheta); reflexivity.
  - apply absent_app in Hfresh as [Hc Hrest].
    apply absent_app in Hrest as [Ha Hb].
    rewrite (IHt1 _ _ _ _ _ Hc Htheta Hsigma).
    rewrite (IHt2 _ _ _ _ _ Ha Htheta Hsigma).
    rewrite (IHt3 _ _ _ _ _ Hb Htheta Hsigma); reflexivity.
  - apply absent_app in Hfresh as [Ha Hb].
    rewrite (IHt1 _ _ _ _ _ Ha Htheta Hsigma).
    rewrite (IHt2 _ _ _ _ _ Hb Htheta Hsigma); reflexivity.
Qed.

Lemma relation_rho_agree : forall T eta rho rho' p q,
  (forall X, In X (free_ty T) -> rho X = rho' X) ->
  (value_relation eta rho T p q <-> value_relation eta rho' T p q).
Proof.
  induction T; intros eta rho rho' p q Henv; simpl in *; try tauto.
  - rewrite (Henv a (or_introl eq_refl)); tauto.
  - assert (Henv1 : forall X, In X (free_ty T1) -> rho X = rho' X).
    { intros X HX; apply Henv; apply in_or_app; left; assumption. }
    assert (Henv2 : forall X, In X (free_ty T2) -> rho X = rho' X).
    { intros X HX; apply Henv; apply in_or_app; right; assumption. }
    assert (Hdom : forall v1 v2,
      value_relation eta rho T1 v1 v2 <-> value_relation eta rho' T1 v1 v2)
      by (intros; apply IHT1; assumption).
    assert (Hran : forall v1 v2,
      value_relation eta rho T2 v1 v2 <-> value_relation eta rho' T2 v1 v2)
      by (intros; apply IHT2; assumption).
    split; intros [Hv1 [Hv2 [U1 [b1 [U2 [b2 [-> [-> HF]]]]]]]];
      refine (conj Hv1 (conj Hv2 _)); exists U1, b1, U2, b2;
      refine (conj eq_refl (conj eq_refl _)); intros arg1 arg2 Harg.
    + apply (proj1 (lifting_iff _ _ _ _ Hran)).
      apply HF; apply (proj2 (Hdom _ _)); exact Harg.
    + apply (proj2 (lifting_iff _ _ _ _ Hran)).
      apply HF; apply (proj1 (Hdom _ _)); exact Harg.
  - split; intros [Hv1 [Hv2 [b1 [b2 [-> [-> HF]]]]]];
      refine (conj Hv1 (conj Hv2 _)); exists b1, b2;
      refine (conj eq_refl (conj eq_refl _)); intros U1 U2 a Hu1 Hu2.
    + apply (proj1 (lifting_iff _ _ _ _
        (fun v1 v2 => IHT (a :: eta) rho rho' v1 v2 Henv))).
      apply HF; assumption.
    + apply (proj2 (lifting_iff _ _ _ _
        (fun v1 v2 => IHT (a :: eta) rho rho' v1 v2 Henv))).
      apply HF; assumption.
Qed.

Definition type_candidate (rho : binary_env) (T : ty) : binary_candidate.
Proof.
  refine {| candidate_relation := value_relation [] rho T |}.
  intros v1 v2 H; eapply relation_values; exact H.
Defined.

Lemma relation_update_other : forall rho X a Y,
  X <> Y -> rho Y = relation_update rho X a Y.
Proof.
  intros rho X a Y H; unfold relation_update.
  assert (E : (X =? Y) = false) by (apply Nat.eqb_neq; assumption).
  rewrite E; reflexivity.
Qed.

Lemma interpret_identity_ty : forall T,
  interpret_ty Ty_FVar T = T.
Proof. induction T; simpl; f_equal; auto. Qed.

Lemma interpret_identity_tm : forall t,
  interpret_tm Ty_FVar tm_fvar t = t.
Proof.
  induction t; simpl; try rewrite interpret_identity_ty;
    f_equal; auto using interpret_identity_ty.
Qed.

Lemma interpreted_closed : forall Delta Gamma t T theta sigma,
  has_type Delta Gamma t T ->
  (forall X, locally_closed_ty (theta X)) ->
  (forall x, locally_closed_tm (sigma x)) ->
  locally_closed_tm (interpret_tm theta sigma t).
Proof.
  intros Delta Gamma t T theta sigma H Htheta Hsigma.
  eapply interpret_tm_closed; eauto.
  exact (typing_closed _ _ _ _ H).
Qed.

Lemma expression_if : forall rho T c1 c2 a1 a2 b1 b2,
  expression_relation [] rho Ty_Bool c1 c2 ->
  expression_relation [] rho T a1 a2 ->
  expression_relation [] rho T b1 b2 ->
  expression_relation [] rho T (tm_if c1 a1 b1) (tm_if c2 a2 b2).
Proof.
  intros rho T c1 c2 a1 a2 b1 b2
    [Hc1 [Hc2 [p [q [Ec1 [Ec2 Hbool]]]]]]
    [Ha1 [Ha2 [va [wa [Ea1 [Ea2 Hra]]]]]]
    [Hb1 [Hb2 [vb [wb [Eb1 [Eb2 Hrb]]]]]].
  unfold expression_relation, expression_lifting.
  split; [unfold locally_closed_tm in *; constructor; assumption|].
  split; [unfold locally_closed_tm in *; constructor; assumption|].
  destruct Hbool as [[-> ->]|[-> ->]].
  - exists va, wa; repeat split; try assumption;
      eauto using EvalIfTrue.
  - exists vb, wb; repeat split; try assumption;
      eauto using EvalIfFalse.
Qed.

Lemma expression_choice : forall rho T a1 a2 b1 b2,
  expression_relation [] rho T a1 a2 ->
  locally_closed_tm b1 -> locally_closed_tm b2 ->
  expression_relation [] rho T (tm_choice a1 b1) (tm_choice a2 b2).
Proof.
  intros rho T a1 a2 b1 b2
    [Ha1 [Ha2 [va [wa [Ea1 [Ea2 Hra]]]]]] Hb1 Hb2.
  unfold expression_relation, expression_lifting.
  split; [unfold locally_closed_tm in *; constructor; assumption|].
  split; [unfold locally_closed_tm in *; constructor; assumption|].
  exists va, wa; repeat split; try assumption; eauto using EvalChoiceLeft.
Qed.

Definition free_context_ty (Gamma : context) : list atom :=
  flat_map (fun binding => free_ty (snd binding)) Gamma.

Lemma lookup_free_ty : forall Gamma x A X,
  lookup_context x Gamma = Some A ->
  In X (free_ty A) -> In X (free_context_ty Gamma).
Proof.
  induction Gamma as [|[y B] Gamma IH]; intros x A X Hlookup Hin;
    simpl in *; try discriminate.
  destruct (x =? y) eqn:E.
  - inversion Hlookup; subst; apply in_or_app; left; exact Hin.
  - apply in_or_app; right; eapply IH; eassumption.
Qed.

Theorem fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall theta1 theta2 sigma1 sigma2 rho,
    (forall X, locally_closed_ty (theta1 X) /\ locally_closed_ty (theta2 X)) ->
    (forall x, locally_closed_tm (sigma1 x) /\ locally_closed_tm (sigma2 x)) ->
    (forall x A, lookup_context x Gamma = Some A ->
      value_relation [] rho A (sigma1 x) (sigma2 x)) ->
    expression_relation [] rho T
      (interpret_tm theta1 sigma1 t) (interpret_tm theta2 sigma2 t).
Proof.
  intros Delta Gamma t T Htyping; induction Htyping;
    intros theta1 theta2 sigma1 sigma2 rho Htheta Hsigma Hctx;
    unfold expression_relation in *; simpl.
  - apply expression_value.
    + apply (proj1 (relation_values _ _ _ _ _ (Hctx x T H))).
    + apply (proj2 (relation_values _ _ _ _ _ (Hctx x T H))).
    + apply Hctx; assumption.
  - assert (Htyped : has_type Delta Gamma (tm_abs T1 t2) (Ty_Arrow T1 T2)).
    { eapply T_Abs; eauto. }
    assert (Hcl1 : locally_closed_tm
      (tm_abs (interpret_ty theta1 T1) (interpret_tm theta1 sigma1 t2))).
    { change (locally_closed_tm (interpret_tm theta1 sigma1 (tm_abs T1 t2))).
      eapply interpreted_closed; [exact Htyped|intros; apply Htheta|intros; apply Hsigma]. }
    assert (Hcl2 : locally_closed_tm
      (tm_abs (interpret_ty theta2 T1) (interpret_tm theta2 sigma2 t2))).
    { change (locally_closed_tm (interpret_tm theta2 sigma2 (tm_abs T1 t2))).
      eapply interpreted_closed; [exact Htyped|intros; apply Htheta|intros; apply Hsigma]. }
    apply expression_value; [constructor; exact Hcl1|constructor; exact Hcl2|].
    simpl; repeat split; try (constructor; assumption).
    exists (interpret_ty theta1 T1), (interpret_tm theta1 sigma1 t2),
      (interpret_ty theta2 T1), (interpret_tm theta2 sigma2 t2).
    refine (conj eq_refl (conj eq_refl _)).
    intros arg1 arg2 Harg.
    destruct (fresh_exists (L ++ free_tm t2)) as [x Hfresh].
    apply absent_app in Hfresh as [Hx Hbody].
    destruct (relation_values _ _ _ _ _ Harg) as [Harg1 Harg2].
    assert (Hsig : forall y,
      locally_closed_tm (replace_tm sigma1 x arg1 y) /\
      locally_closed_tm (replace_tm sigma2 x arg2 y)).
    { intro y; unfold replace_tm; destruct (x =? y);
        auto using value_closed; apply Hsigma. }
    assert (Hctx' : forall y A,
      lookup_context y (update Gamma x T1) = Some A ->
      value_relation [] rho A (replace_tm sigma1 x arg1 y)
        (replace_tm sigma2 x arg2 y)).
    { intros y A Hy; unfold update in Hy; simpl in Hy.
      destruct (y =? x) eqn:E.
      - apply Nat.eqb_eq in E; subst y; simpl in Hy.
        inversion Hy; subst A; unfold replace_tm; rewrite Nat.eqb_refl; exact Harg.
      - unfold replace_tm; rewrite Nat.eqb_sym; rewrite E; apply Hctx; exact Hy. }
    specialize (H1 x Hx theta1 theta2
      (replace_tm sigma1 x arg1) (replace_tm sigma2 x arg2) rho
      Htheta Hsig Hctx').
    unfold open_tm in H1 |- *.
    rewrite (interpret_open_tm t2 0 theta1 sigma1 x arg1 Hbody
      (fun y => proj1 (Hsigma y))) in H1.
    rewrite (interpret_open_tm t2 0 theta2 sigma2 x arg2 Hbody
      (fun y => proj2 (Hsigma y))) in H1.
    exact H1.
  - eapply expression_app; [apply IHHtyping2|apply IHHtyping1]; assumption.
  - assert (Htyped : has_type Delta Gamma (tm_tabs t) (Ty_All T)).
    { eapply T_TAbs; eauto. }
    assert (Hcl1 : locally_closed_tm (tm_tabs (interpret_tm theta1 sigma1 t))).
    { change (locally_closed_tm (interpret_tm theta1 sigma1 (tm_tabs t))).
      eapply interpreted_closed; [exact Htyped|intros; apply Htheta|intros; apply Hsigma]. }
    assert (Hcl2 : locally_closed_tm (tm_tabs (interpret_tm theta2 sigma2 t))).
    { change (locally_closed_tm (interpret_tm theta2 sigma2 (tm_tabs t))).
      eapply interpreted_closed; [exact Htyped|intros; apply Htheta|intros; apply Hsigma]. }
    apply expression_value; [constructor; exact Hcl1|constructor; exact Hcl2|].
    simpl.
    refine (conj (v_tabs _ Hcl1) (conj (v_tabs _ Hcl2) _)).
    exists (interpret_tm theta1 sigma1 t), (interpret_tm theta2 sigma2 t).
    refine (conj eq_refl (conj eq_refl _)).
    intros U1 U2 a HU1 HU2.
    destruct (fresh_exists (L ++ free_tm_ty t ++ free_ty T ++ free_context_ty Gamma))
      as [X Hfresh].
    apply absent_app in Hfresh as [HX_L Hrest].
    apply absent_app in Hrest as [HX_t Hrest].
    apply absent_app in Hrest as [HX_T HX_gamma].
    assert (Htheta' : forall Y,
      locally_closed_ty (replace_ty theta1 X U1 Y) /\
      locally_closed_ty (replace_ty theta2 X U2 Y)).
    { intro Y; unfold replace_ty; destruct (X =? Y); auto; apply Htheta. }
    assert (Hctx' : forall x A, lookup_context x Gamma = Some A ->
      value_relation [] (relation_update rho X a) A (sigma1 x) (sigma2 x)).
    { intros x A Hlookup.
      assert (HenvA : forall Y, In Y (free_ty A) ->
        rho Y = relation_update rho X a Y).
      { intros Y HY; apply relation_update_other.
        intro E; subst Y; apply HX_gamma.
        eapply lookup_free_ty; eassumption. }
      apply (proj1 (relation_rho_agree A [] rho (relation_update rho X a)
        (sigma1 x) (sigma2 x) HenvA)).
      apply Hctx; assumption. }
    specialize (H0 X HX_L (replace_ty theta1 X U1) (replace_ty theta2 X U2)
      sigma1 sigma2 (relation_update rho X a) Htheta' Hsigma Hctx').
    unfold open_tm_ty, open_ty in H0.
    rewrite (interpret_open_tm_ty t 0 theta1 sigma1 X U1 HX_t
      (fun Y => proj1 (Htheta Y)) (fun x => proj1 (Hsigma x))) in H0.
    rewrite (interpret_open_tm_ty t 0 theta2 sigma2 X U2 HX_t
      (fun Y => proj2 (Htheta Y)) (fun x => proj2 (Hsigma x))) in H0.
    assert (HenvT : forall Y, In Y (free_ty T) ->
      rho Y = relation_update rho X a Y).
    { intros Y HY; apply relation_update_other; intro E; subst; apply HX_T; exact HY. }
    assert (Hcand : forall eta p q,
      candidate_relation a p q <->
        value_relation eta (relation_update rho X a) (Ty_FVar X) p q).
    { intros eta p q; simpl; unfold relation_update; rewrite Nat.eqb_refl; tauto. }
    apply (proj2 (lifting_iff _ _ _ _
      (fun p q => relation_open T [] rho (relation_update rho X a)
        (Ty_FVar X) a p q HenvT Hcand))).
    exact H0.
  - pose (candidate := type_candidate rho U).
    assert (Hcand : forall eta p q,
      candidate_relation candidate p q <-> value_relation eta rho U p q).
    { intros eta p q; unfold candidate, type_candidate; simpl.
      eapply relation_eta_agree; [apply (wf_ty_closed _ _ H)|].
      intros i Hi; lia. }
    assert (HUC1 : locally_closed_ty (interpret_ty theta1 U)).
    { eapply interpret_ty_closed; [apply (wf_ty_closed _ _ H)|];
        intros X; apply Htheta. }
    assert (HUC2 : locally_closed_ty (interpret_ty theta2 U)).
    { eapply interpret_ty_closed; [apply (wf_ty_closed _ _ H)|];
        intros X; apply Htheta. }
    destruct (IHHtyping theta1 theta2 sigma1 sigma2 rho Htheta Hsigma Hctx)
      as [Hf1 [Hf2 [w1 [w2 [Ef1 [Ef2 HR]]]]]].
    simpl in HR.
    destruct HR as [_ [_ [b1 [b2 [-> [-> Hall]]]]]].
    specialize (Hall (interpret_ty theta1 U) (interpret_ty theta2 U)
      candidate HUC1 HUC2).
    destruct Hall as [_ [_ [r1 [r2 [Er1 [Er2 Hr]]]]]].
    split; [unfold locally_closed_tm in *; constructor; assumption|].
    split; [unfold locally_closed_tm in *; constructor; assumption|].
    exists r1, r2; repeat split.
    + eapply EvalTApp; eauto.
    + eapply EvalTApp; eauto.
    + apply (proj1 (relation_open T [] rho rho U candidate r1 r2
        (fun X HX => eq_refl) Hcand)); exact Hr.
  - apply expression_value; auto using value.
  - apply expression_value; auto using value.
  - eapply expression_if; [apply IHHtyping1|apply IHHtyping2|apply IHHtyping3];
      assumption.
  - eapply expression_choice.
    + apply IHHtyping1; assumption.
    + eapply interpreted_closed; [exact Htyping2|intros; apply Htheta|intros; apply Hsigma].
    + eapply interpreted_closed; [exact Htyping2|intros; apply Htheta|intros; apply Hsigma].
Qed.

Definition singleton_candidate (v : tm) (Hv : value v) : binary_candidate.
Proof.
  refine {| candidate_relation := fun p q => p = v /\ q = v |}.
  intros p q [-> ->]; split; assumption.
Defined.

Theorem polymorphic_identity_theorem_for_free : forall t,
  has_type [] empty t
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) ->
  forall U v,
    wf_ty [] U ->
    value v ->
    has_type [] empty v U ->
    tm_app (tm_tapp t U) v -->* v.
Proof.
  intros t Htyped U v Hwf Hv Htyped_v.
  assert (Hrel := fundamental [] empty t
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) Htyped
    Ty_FVar Ty_FVar tm_fvar tm_fvar (fun _ => None)
    (fun X => conj (lc_ty_fvar 0 X) (lc_ty_fvar 0 X))
    (fun x => conj (lc_tm_fvar 0 0 x) (lc_tm_fvar 0 0 x))
    (fun x A H => ltac:(discriminate))).
  repeat rewrite interpret_identity_tm in Hrel.
  destruct Hrel as [_ [_ [p [q [Ep [Eq HR]]]]]].
  simpl in HR.
  destruct HR as [_ [_ [poly1 [poly2 [-> [-> Hforall]]]]]].
  assert (Hclosed : locally_closed_ty U) by (eapply wf_ty_closed; eassumption).
  pose (candidate := singleton_candidate v Hv).
  specialize (Hforall U U candidate Hclosed Hclosed).
  destruct Hforall as [_ [_ [f1 [f2 [Ef1 [Ef2 Hfun]]]]]].
  simpl in Hfun.
  destruct Hfun as [_ [_ [A1 [body1 [A2 [body2 [-> [-> Happly]]]]]]]].
  specialize (Happly v v).
  assert (Harg : value_relation [candidate] (fun _ => None) (Ty_BVar 0) v v).
  { simpl; split; reflexivity. }
  specialize (Happly Harg).
  destruct Happly as [_ [_ [result1 [result2 [Eresult1 [Eresult2 Hresult]]]]]].
  simpl in Hresult.
  destruct Hresult as [-> _].
  apply evaluates_multi.
  eapply EvalApp with (U := A1) (body := body1) (v := v).
  - eapply EvalTApp with (body := poly1); eauto.
  - constructor; assumption.
  - exact Eresult1.
Qed.

End SystemFParametricityIfNondeterminismMediumTask.
