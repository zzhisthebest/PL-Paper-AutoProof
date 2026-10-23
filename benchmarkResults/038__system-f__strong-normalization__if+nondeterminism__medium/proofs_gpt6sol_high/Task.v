(** System F CBV strong-normalization benchmark, Medium variant.
    Features: if-nondeterminism. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFNormalizationIfNondeterminismMediumTask.

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
  end.

Definition expression_relation eta rho T t :=
  expression_lifting (value_relation eta rho T) t.

Definition related_substitution (rho : relation_env) (Gamma : context)
    (gamma : term_substitution) : Prop :=
  forall x T, lookup_context x Gamma = Some T -> value_relation [] rho T (gamma x).

Lemma value_relation_value : forall eta rho T v,
  value_relation eta rho T v -> value v.
Proof.
  intros eta rho T; destruct T; simpl; intros v Hv.
  - destruct (nth_error eta n) as [a|]; [exact (candidate_values a v Hv)|contradiction].
  - destruct (rho a) as [c|]; [exact (candidate_values c v Hv)|contradiction].
  - exact (proj1 Hv).
  - exact (proj1 Hv).
  - exact (proj1 Hv).
Qed.

Lemma value_closed : forall v, value v -> locally_closed_tm v.
Proof. intros v Hv; inversion Hv; subst; auto; unfold locally_closed_tm; constructor. Qed.

Lemma value_no_step : forall v u, value v -> v --> u -> False.
Proof. intros v u Hv Hs; inversion Hv; subst; inversion Hs. Qed.

Lemma sn_reduct : forall t u,
  strongly_normalizing t -> t --> u -> strongly_normalizing u.
Proof. intros t u H Hs; inversion H; auto. Qed.

Lemma multi_trans : forall t u v, t -->* u -> u -->* v -> t -->* v.
Proof. intros t u v H; induction H; eauto using multi. Qed.

Lemma lc_ty_weaken : forall K T,
  lc_ty_at K T -> forall K', K <= K' -> lc_ty_at K' T.
Proof.
  intros K T H; induction H; intros K' Hle.
  - apply lc_ty_bvar; lia.
  - constructor.
  - constructor; eauto.
  - constructor. apply IHlc_ty_at; lia.
  - constructor.
Qed.

Lemma lc_tm_weaken : forall K k t,
  lc_tm_at K k t -> forall K' k', K <= K' -> k <= k' -> lc_tm_at K' k' t.
Proof.
  intros K k t H; induction H; intros K' k' HK Hk.
  - apply lc_tm_bvar; lia.
  - constructor.
  - apply lc_tm_abs; eauto using lc_ty_weaken; apply IHlc_tm_at; lia.
  - constructor; eauto.
  - constructor. apply IHlc_tm_at; lia.
  - constructor; eauto using lc_ty_weaken.
  - constructor.
  - constructor.
  - constructor; eauto.
  - constructor; eauto.
Qed.

Lemma lc_open_ty_rec : forall T K U,
  lc_ty_at (S K) T -> lc_ty_at K U -> lc_ty_at K (open_ty_rec K U T).
Proof.
  induction T; intros K U HT HU; inversion HT; subst; simpl;
    try (constructor; eauto using lc_ty_weaken).
  - destruct (Nat.eqb K n) eqn:Heq.
    + exact HU.
    + apply Nat.eqb_neq in Heq; constructor; lia.
Qed.

Lemma lc_open_tm_rec : forall t K k u,
  lc_tm_at K (S k) t -> lc_tm_at K k u ->
  lc_tm_at K k (open_tm_rec k u t).
Proof.
  induction t; intros K k u HT HU; inversion HT; subst; simpl;
    try (constructor; eauto).
  - destruct (Nat.eqb k n) eqn:Heq.
    + exact HU.
    + apply Nat.eqb_neq in Heq; constructor; lia.
  - apply IHt; eauto using lc_tm_weaken.
  - apply IHt; eauto using lc_tm_weaken.
Qed.

Lemma lc_open_tm_ty_rec : forall t K k U,
  lc_tm_at (S K) k t -> lc_ty_at K U ->
  lc_tm_at K k (open_tm_ty_rec K U t).
Proof.
  induction t; intros K k U HT HU; inversion HT; subst; simpl;
    try (constructor; eauto using lc_open_ty_rec).
  - apply IHt; eauto using lc_ty_weaken.
Qed.

Lemma step_closed : forall t u,
  t --> u -> locally_closed_tm t -> locally_closed_tm u.
Proof.
  intros t u H; unfold locally_closed_tm in *;
    induction H; intros Hlc; inversion Hlc; subst;
    eauto using lc_open_tm_rec, lc_open_tm_ty_rec, value_closed with core.
  - inversion H5; subst; eapply lc_open_tm_rec; eauto using value_closed.
  - match goal with
    | Htabs : lc_tm_at 0 0 (tm_tabs _) |- _ => inversion Htabs; subst
    end.
    eapply lc_open_tm_ty_rec; eauto.
Qed.

Lemma lifting_reduct : forall R t u,
  expression_lifting R t -> t --> u -> expression_lifting R u.
Proof.
  intros R t u [Hlc [Hsn Hvalues]] Hstep.
  split.
  - eauto using step_closed.
  - split; [eauto using sn_reduct|].
    intros v Hmulti Hv; apply Hvalues; [eapply multi_step; eauto | exact Hv].
Qed.

Lemma lifting_value : forall R v,
  value v -> locally_closed_tm v -> R v -> expression_lifting R v.
Proof.
  intros R v Hv Hlc HR; split; [exact Hlc|split].
  - constructor. intros u Hs; exfalso; eapply value_no_step; eauto.
  - intros u Hmulti _. inversion Hmulti; subst; auto.
    exfalso; eapply value_no_step; eauto.
Qed.

Lemma lifting_choice : forall R t1 t2,
  expression_lifting R t1 -> expression_lifting R t2 ->
  expression_lifting R (tm_choice t1 t2).
Proof.
  intros R t1 t2 [Hlc1 [Hsn1 Hval1]] [Hlc2 [Hsn2 Hval2]].
  split; [unfold locally_closed_tm in *; constructor; assumption|split].
  - constructor. intros u Hstep; inversion Hstep; subst; assumption.
  - intros v Hmulti Hv; inversion Hmulti; subst.
    + inversion Hv.
    + match goal with
      | H : tm_choice _ _ --> _ |- _ => inversion H; subst
      end; eauto.
Qed.

Lemma lifting_expand : forall R t,
  locally_closed_tm t -> (value t -> R t) ->
  (forall u, t --> u -> expression_lifting R u) ->
  expression_lifting R t.
Proof.
  intros R t Hlc Hvalue Hstep; split; [exact Hlc|split].
  - constructor; intros u Hs; exact (proj1 (proj2 (Hstep u Hs))).
  - intros v Hmulti Hv; inversion Hmulti; subst.
    + apply Hvalue; assumption.
    + destruct (Hstep y H) as [_ [_ Hvalues]].
      apply Hvalues; assumption.
Qed.

Lemma lifting_if : forall eta rho R t t1 t2,
  expression_relation eta rho Ty_Bool t ->
  expression_lifting R t1 -> expression_lifting R t2 ->
  expression_lifting R (tm_if t t1 t2).
Proof.
  intros eta rho R t t1 t2 [Hlc [Hsn Hbool]] Hthen Helse.
  destruct Hthen as [Hlc1 [Hsn1 Hrel1]].
  destruct Helse as [Hlc2 [Hsn2 Hrel2]].
  induction Hsn as [t Hred IH] in Hlc, Hbool |- *.
  apply lifting_expand.
  - unfold locally_closed_tm in *; constructor; assumption.
  - intros Hv; inversion Hv.
  - intros u Hstep; inversion Hstep; subst.
    + split; [exact Hlc1|split; assumption].
    + split; [exact Hlc2|split; assumption].
    + eapply IH.
      * eassumption.
      * eapply step_closed; eauto.
      * intros v Hmulti Hv; apply Hbool; [eapply multi_step; eauto|exact Hv].
Qed.

Lemma lifting_app_value : forall eta rho T1 T2 v t,
  value_relation eta rho (Ty_Arrow T1 T2) v ->
  expression_relation eta rho T1 t ->
  expression_relation eta rho T2 (tm_app v t).
Proof.
  intros eta rho T1 T2 v t Hfunction [Hlc [Hsn Hvalues]].
  destruct Hfunction as [Hv [U [body [Heq Hbody]]]].
  subst v.
  assert (Habs : locally_closed_tm (tm_abs U body)) by
    (eapply value_closed; eassumption).
  induction Hsn as [t Hred IH] in Hlc, Hvalues |- *.
  apply lifting_expand.
  - unfold locally_closed_tm in *; constructor; assumption.
  - intros Hvapp; inversion Hvapp.
  - intros next Hstep; inversion Hstep; subst.
    + apply Hbody. apply Hvalues; [constructor|assumption].
    + exfalso; eapply value_no_step; eauto.
    + eapply IH.
      * eassumption.
      * eapply step_closed; eauto.
      * intros result Hmulti Hresult.
        apply Hvalues; [eapply multi_step; eauto|exact Hresult].
Qed.

Lemma lifting_app : forall eta rho T1 T2 t1 t2,
  expression_relation eta rho (Ty_Arrow T1 T2) t1 ->
  expression_relation eta rho T1 t2 ->
  expression_relation eta rho T2 (tm_app t1 t2).
Proof.
  intros eta rho T1 T2 t1 t2 [Hlc [Hsn Hvalues]] Harg.
  destruct Harg as [Hlc2 [Hsn2 Hvalues2]].
  induction Hsn as [t1 Hred IH] in Hlc, Hvalues |- *.
  apply lifting_expand.
  - unfold locally_closed_tm in *; constructor; assumption.
  - intros Hvapp; inversion Hvapp.
  - intros next Hstep; inversion Hstep; subst.
    + destruct (Hvalues _ (multi_refl _) (v_abs _ _ H1))
        as [_ [U [body [Heq Hbody]]]].
      inversion Heq; subst.
      apply Hbody. apply Hvalues2; [constructor|assumption].
    + eapply IH.
      * eassumption.
      * eapply step_closed; eauto.
      * intros result Hmulti Hresult.
        apply Hvalues; [eapply multi_step; eauto|exact Hresult].
    + eapply lifting_app_value.
      * apply Hvalues; [constructor|assumption].
      * eapply lifting_reduct; [|eassumption].
        split; [exact Hlc2|split; [exact Hsn2|exact Hvalues2]].
Qed.

Lemma lifting_tapp : forall eta rho T R t U a,
  expression_relation eta rho (Ty_All T) t ->
  locally_closed_ty U ->
  (forall body,
    expression_relation (a :: eta) rho T (open_tm_ty body U) ->
    expression_lifting R (open_tm_ty body U)) ->
  expression_lifting R (tm_tapp t U).
Proof.
  intros eta rho T R t U a [Hlc [Hsn Hvalues]] HU Hresult.
  induction Hsn as [t Hred IH] in Hlc, Hvalues |- *.
  apply lifting_expand.
  - unfold locally_closed_tm in *; constructor; assumption.
  - intros Hv; inversion Hv.
  - intros next Hstep; inversion Hstep; subst.
    + destruct (Hvalues _ (multi_refl _) (v_tabs _ H1))
        as [_ [body [Heq Hbody]]].
      inversion Heq; subst.
      apply Hresult. apply Hbody; assumption.
    + eapply IH.
      * eassumption.
      * eapply step_closed; eauto.
      * intros result Hmulti HresultValue.
        apply Hvalues; [eapply multi_step; eauto|exact HresultValue].
Qed.

Lemma list_atom_bound : forall L x,
  In x L -> x <= fold_right Nat.max 0 L.
Proof.
  induction L as [|a L IH]; intros x Hin; simpl in *.
  - contradiction.
  - destruct Hin as [Heq|Hin]; [subst; lia|].
    specialize (IH _ Hin); lia.
Qed.

Lemma fresh_atom : forall L : list atom, exists x, ~ In x L.
Proof.
  intro L; exists (S (fold_right Nat.max 0 L)).
  intros Hin; pose proof (list_atom_bound _ _ Hin); lia.
Qed.

Lemma lc_open_ty_reverse : forall T K U,
  lc_ty_at K (open_ty_rec K U T) -> lc_ty_at (S K) T.
Proof.
  induction T; intros K U Hlc; simpl in Hlc.
  - destruct (Nat.eqb K n) eqn:Heq.
    + apply Nat.eqb_eq in Heq; subst; constructor; lia.
    + inversion Hlc; subst; constructor; lia.
  - constructor.
  - inversion Hlc; subst; constructor; eauto.
  - inversion Hlc; subst; constructor; eauto.
  - constructor.
Qed.

Lemma lc_open_tm_reverse : forall t K k u,
  lc_tm_at K k (open_tm_rec k u t) -> lc_tm_at K (S k) t.
Proof.
  induction t; intros K k u Hlc; simpl in Hlc.
  - destruct (Nat.eqb k n) eqn:Heq.
    + apply Nat.eqb_eq in Heq; subst; constructor; lia.
    + inversion Hlc; subst; constructor; lia.
  - constructor.
  - inversion Hlc; subst; constructor; eauto.
  - inversion Hlc; subst; constructor; eauto.
  - inversion Hlc; subst; constructor; eauto.
  - inversion Hlc; subst; constructor; eauto.
  - constructor.
  - constructor.
  - inversion Hlc; subst; constructor; eauto.
  - inversion Hlc; subst; constructor; eauto.
Qed.

Lemma lc_open_tm_ty_reverse : forall t K k U,
  lc_tm_at K k (open_tm_ty_rec K U t) -> lc_tm_at (S K) k t.
Proof.
  induction t; intros K k U Hlc; simpl in Hlc.
  - inversion Hlc; subst; constructor; assumption.
  - constructor.
  - inversion Hlc; subst; constructor;
      eauto using lc_open_ty_reverse.
  - inversion Hlc; subst; constructor; eauto.
  - inversion Hlc; subst; constructor; eauto.
  - inversion Hlc; subst; constructor;
      eauto using lc_open_ty_reverse.
  - constructor.
  - constructor.
  - inversion Hlc; subst; constructor; eauto.
  - inversion Hlc; subst; constructor; eauto.
Qed.

Lemma wf_ty_closed : forall Delta T,
  wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T Hwf; induction Hwf.
  - constructor.
  - constructor; assumption.
  - destruct (fresh_atom L) as [X HX].
    specialize (H0 X HX).
    unfold locally_closed_ty in *.
    constructor. eapply lc_open_ty_reverse; eauto.
  - constructor.
Qed.

Lemma typing_closed : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T Htype; induction Htype.
  - constructor.
  - destruct (fresh_atom L) as [x Hx].
    specialize (H1 x Hx).
    unfold locally_closed_tm in *.
    constructor; [exact (wf_ty_closed _ _ H)|].
    eapply lc_open_tm_reverse; eauto.
  - unfold locally_closed_tm in *; constructor; assumption.
  - destruct (fresh_atom L) as [X HX].
    specialize (H0 X HX).
    unfold locally_closed_tm in *.
    constructor. eapply lc_open_tm_ty_reverse; eauto.
  - unfold locally_closed_tm in *; constructor;
      [assumption|exact (wf_ty_closed _ _ H)].
  - constructor.
  - constructor.
  - unfold locally_closed_tm in *; constructor; assumption.
  - unfold locally_closed_tm in *; constructor; assumption.
Qed.

Fixpoint ty_free_atoms (T : ty) : list atom :=
  match T with
  | Ty_BVar _ | Ty_Bool => []
  | Ty_FVar X => [X]
  | Ty_Arrow T1 T2 => ty_free_atoms T1 ++ ty_free_atoms T2
  | Ty_All T1 => ty_free_atoms T1
  end.

Fixpoint tm_type_free_atoms (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_fvar _ | tm_true | tm_false => []
  | tm_abs T body => ty_free_atoms T ++ tm_type_free_atoms body
  | tm_app t1 t2 | tm_choice t1 t2 =>
      tm_type_free_atoms t1 ++ tm_type_free_atoms t2
  | tm_tabs body => tm_type_free_atoms body
  | tm_tapp body T => tm_type_free_atoms body ++ ty_free_atoms T
  | tm_if test yes no =>
      tm_type_free_atoms test ++ tm_type_free_atoms yes ++ tm_type_free_atoms no
  end.

Fixpoint tm_free_atoms (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_true | tm_false => []
  | tm_fvar x => [x]
  | tm_abs _ body | tm_tabs body => tm_free_atoms body
  | tm_app t1 t2 | tm_choice t1 t2 => tm_free_atoms t1 ++ tm_free_atoms t2
  | tm_tapp body _ => tm_free_atoms body
  | tm_if test yes no =>
      tm_free_atoms test ++ tm_free_atoms yes ++ tm_free_atoms no
  end.

Definition context_type_free_atoms (Gamma : context) : list atom :=
  flat_map (fun entry => ty_free_atoms (snd entry)) Gamma.

Lemma candidate_for_type : forall (eta : list value_candidate) (rho : relation_env) (T : ty),
  value_candidate.
Proof.
  intros eta rho T.
  exact {| candidate_relation := value_relation eta rho T;
           candidate_values := value_relation_value eta rho T |}.
Defined.

Lemma lifting_equiv : forall R S t,
  (forall v, R v <-> S v) ->
  (expression_lifting R t <-> expression_lifting S t).
Proof.
  intros R S t Hequiv; split.
  - intros [Hlc [Hsn Hvalues]].
    split; [exact Hlc|split; [exact Hsn|]].
    intros result Hmulti Hvalue.
    apply (proj1 (Hequiv result)); apply Hvalues; assumption.
  - intros [Hlc [Hsn Hvalues]].
    split; [exact Hlc|split; [exact Hsn|]].
    intros result Hmulti Hvalue.
    apply (proj2 (Hequiv result)); apply Hvalues; assumption.
Qed.

Lemma value_relation_env_fresh : forall T X (candidate : value_candidate) eta rho v,
  ~ In X (ty_free_atoms T) ->
  (value_relation eta (relation_update rho X candidate) T v <->
   value_relation eta rho T v).
Proof.
  induction T; intros X candidate eta rho v Hfresh; simpl in *.
  - tauto.
  - assert (X <> a) by (intro Heq; subst; apply Hfresh; auto).
    unfold relation_update; destruct (Nat.eqb X a) eqn:Heq; [apply Nat.eqb_eq in Heq; congruence|tauto].
  - assert (Hfresh1 : ~ In X (ty_free_atoms T1)) by
      (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (Hfresh2 : ~ In X (ty_free_atoms T2)) by
      (intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
    split.
    + intros [Hv [U [body [Heq Hbody]]]].
      split; [exact Hv|]. exists U, body; split; [exact Heq|].
      intros arg Harg; apply lifting_equiv with
        (R := value_relation eta (relation_update rho X candidate) T2).
      * intros result; apply IHT2; exact Hfresh2.
      * apply Hbody. apply (proj2 (IHT1 X candidate eta rho arg Hfresh1)); exact Harg.
    + intros [Hv [U [body [Heq Hbody]]]].
      split; [exact Hv|]. exists U, body; split; [exact Heq|].
      intros arg Harg; apply lifting_equiv with
        (R := value_relation eta rho T2).
      * intros result; symmetry; apply IHT2; exact Hfresh2.
      * apply Hbody. apply (proj1 (IHT1 X candidate eta rho arg Hfresh1)); exact Harg.
  - split.
    + intros [Hv [body [Heq Hbody]]].
      split; [exact Hv|]. exists body; split; [exact Heq|].
      intros U quantified HU; apply lifting_equiv with
        (R := value_relation (quantified :: eta) (relation_update rho X candidate) T).
      * intros result; apply IHT; exact Hfresh.
      * apply Hbody; assumption.
    + intros [Hv [body [Heq Hbody]]].
      split; [exact Hv|]. exists body; split; [exact Heq|].
      intros U quantified HU; apply lifting_equiv with
        (R := value_relation (quantified :: eta) rho T).
      * intros result; symmetry; apply IHT; exact Hfresh.
      * apply Hbody; assumption.
  - tauto.
Qed.

Lemma value_relation_eta_ext : forall T K eta1 eta2 rho v,
  lc_ty_at K T ->
  (forall i, i < K -> nth_error eta1 i = nth_error eta2 i) ->
  (value_relation eta1 rho T v <-> value_relation eta2 rho T v).
Proof.
  induction T; intros K eta1 eta2 rho v Hlc Heta; inversion Hlc; subst; simpl.
  - rewrite Heta by assumption; tauto.
  - tauto.
  - split.
    + intros [Hv [U [body [Heq Hbody]]]].
      split; [exact Hv|]. exists U, body; split; [exact Heq|].
      intros arg Harg.
      apply lifting_equiv with (R := value_relation eta1 rho T2).
      * intro result; apply (IHT2 K eta1 eta2 rho result); assumption.
      * apply Hbody. apply (proj2 (IHT1 K eta1 eta2 rho arg H2 Heta)); exact Harg.
    + intros [Hv [U [body [Heq Hbody]]]].
      split; [exact Hv|]. exists U, body; split; [exact Heq|].
      intros arg Harg.
      apply lifting_equiv with (R := value_relation eta2 rho T2).
      * intro result; symmetry; apply (IHT2 K eta1 eta2 rho result); assumption.
      * apply Hbody. apply (proj1 (IHT1 K eta1 eta2 rho arg H2 Heta)); exact Harg.
  - split.
    + intros [Hv [body [Heq Hbody]]].
      split; [exact Hv|]. exists body; split; [exact Heq|].
      intros U candidate HU.
      apply lifting_equiv with (R := value_relation (candidate :: eta1) rho T).
      * intro result; apply IHT with (K := S K).
        -- assumption.
        -- intros [|i] Hi; [reflexivity|simpl; apply Heta; lia].
      * apply Hbody; assumption.
    + intros [Hv [body [Heq Hbody]]].
      split; [exact Hv|]. exists body; split; [exact Heq|].
      intros U candidate HU.
      apply lifting_equiv with (R := value_relation (candidate :: eta2) rho T).
      * intro result; symmetry; apply IHT with (K := S K).
        -- assumption.
        -- intros [|i] Hi; [reflexivity|simpl; apply Heta; lia].
      * apply Hbody; assumption.
  - tauto.
Qed.

Lemma value_relation_closed_eta : forall T eta rho v,
  locally_closed_ty T ->
  (value_relation eta rho T v <-> value_relation [] rho T v).
Proof.
  intros T eta rho v Hlc; apply value_relation_eta_ext with (K := 0);
    [exact Hlc|intros i Hi; lia].
Qed.

Lemma value_relation_open : forall T K eta replacement a rho1 rho2 v,
  lc_ty_at (S K) T -> length eta = K ->
  (forall other v,
    value_relation other rho1 replacement v <-> candidate_relation a v) ->
  (forall Y v, In Y (ty_free_atoms T) ->
    value_relation [] rho1 (Ty_FVar Y) v <->
    value_relation [] rho2 (Ty_FVar Y) v) ->
  (value_relation eta rho1 (open_ty_rec K replacement T) v <->
   value_relation (eta ++ [a]) rho2 T v).
Proof.
  induction T; intros K eta replacement candidate rho1 rho2 v Hlc Hlength Hreplacement Hfree;
    revert Hlength; inversion Hlc; subst; intros Hlength; simpl.
  - destruct (Nat.eqb K n) eqn:Heq.
    + apply Nat.eqb_eq in Heq; subst n.
      rewrite nth_error_app2 by lia.
      replace (K - length eta) with 0 by lia.
      simpl; apply Hreplacement.
    + apply Nat.eqb_neq in Heq.
      assert (n < K) by lia.
      rewrite nth_error_app1 by lia; tauto.
  - apply Hfree; simpl; auto.
  - assert (Hfree1 : forall Y result, In Y (ty_free_atoms T1) ->
        value_relation [] rho1 (Ty_FVar Y) result <->
        value_relation [] rho2 (Ty_FVar Y) result) by
      (intros Y result HY; apply Hfree; apply in_or_app; left; exact HY).
    assert (Hfree2 : forall Y result, In Y (ty_free_atoms T2) ->
        value_relation [] rho1 (Ty_FVar Y) result <->
        value_relation [] rho2 (Ty_FVar Y) result) by
      (intros Y result HY; apply Hfree; apply in_or_app; right; exact HY).
    split.
    + intros [Hv [U [body [Heq Hbody]]]].
      split; [exact Hv|]. exists U, body; split; [exact Heq|].
      intros arg Harg.
      apply lifting_equiv with
        (R := value_relation eta rho1 (open_ty_rec K replacement T2)).
      * intro result; apply IHT2; assumption.
      * apply Hbody.
        apply (proj2 (IHT1 K eta replacement candidate rho1 rho2 arg
          H2 Hlength Hreplacement Hfree1)); exact Harg.
    + intros [Hv [U [body [Heq Hbody]]]].
      split; [exact Hv|]. exists U, body; split; [exact Heq|].
      intros arg Harg.
      apply lifting_equiv with
        (R := value_relation (eta ++ [candidate]) rho2 T2).
      * intro result; symmetry; apply IHT2; assumption.
      * apply Hbody.
        apply (proj1 (IHT1 K eta replacement candidate rho1 rho2 arg
          H2 Hlength Hreplacement Hfree1)); exact Harg.
  - split.
    + intros [Hv [body [Heq Hbody]]].
      split; [exact Hv|]. exists body; split; [exact Heq|].
      intros U quantified HU.
      apply lifting_equiv with
        (R := value_relation (quantified :: eta) rho1
          (open_ty_rec (S K) replacement T)).
      * intro result.
        change (value_relation (quantified :: eta) rho1
          (open_ty_rec (S K) replacement T) result <->
          value_relation ((quantified :: eta) ++ [candidate]) rho2 T result).
        apply IHT; simpl; eauto.
      * apply Hbody; assumption.
    + intros [Hv [body [Heq Hbody]]].
      split; [exact Hv|]. exists body; split; [exact Heq|].
      intros U quantified HU.
      apply lifting_equiv with
        (R := value_relation ((quantified :: eta) ++ [candidate]) rho2 T).
      * intro result.
        change (value_relation ((quantified :: eta) ++ [candidate]) rho2 T result <->
          value_relation (quantified :: eta) rho1
            (open_ty_rec (S K) replacement T) result).
        symmetry; apply IHT; simpl; eauto.
      * apply Hbody; assumption.
  - tauto.
Qed.

Lemma value_relation_open_closed : forall T U rho v,
  lc_ty_at 1 T -> locally_closed_ty U ->
  (value_relation [] rho (open_ty T U) v <->
   value_relation [candidate_for_type [] rho U] rho T v).
Proof.
  intros T U rho v HT HU.
  apply (value_relation_open T 0 [] U
    (candidate_for_type [] rho U) rho rho v); auto.
  - intros other result; simpl.
    exact (value_relation_closed_eta U other rho result HU).
  - intros Y result _; tauto.
Qed.

Lemma value_relation_open_fvar : forall T X candidate rho v,
  lc_ty_at 1 T -> ~ In X (ty_free_atoms T) ->
  (value_relation [] (relation_update rho X candidate)
    (open_ty T (Ty_FVar X)) v <->
   value_relation [candidate] rho T v).
Proof.
  intros T X candidate rho v HT Hfresh.
  apply (value_relation_open T 0 [] (Ty_FVar X) candidate
    (relation_update rho X candidate) rho v); auto.
  - intros other result; simpl; unfold relation_update.
    rewrite Nat.eqb_refl; tauto.
  - intros Y result HY; simpl; unfold relation_update.
    destruct (Nat.eqb X Y) eqn:Heq; [apply Nat.eqb_eq in Heq; subst; contradiction|tauto].
Qed.

Definition type_substitution_update (theta : type_substitution) X U : type_substitution :=
  fun Y => if Nat.eqb X Y then U else theta Y.

Definition term_substitution_update (gamma : term_substitution) x v : term_substitution :=
  fun y => if Nat.eqb x y then v else gamma y.

Lemma closed_ty_open_identity : forall T K k U,
  lc_ty_at K T -> K <= k -> open_ty_rec k U T = T.
Proof.
  induction T; intros K k U Hlc Hle; inversion Hlc; subst; simpl; auto.
  - destruct (Nat.eqb k n) eqn:Heq; [apply Nat.eqb_eq in Heq; lia|reflexivity].
  - rewrite (IHT1 K k U H2 Hle), (IHT2 K k U H3 Hle); reflexivity.
  - rewrite (IHT (S K) (S k) U H1) by lia; reflexivity.
Qed.

Lemma closed_tm_open_identity : forall t K d k u,
  lc_tm_at K d t -> d <= k -> open_tm_rec k u t = t.
Proof.
  induction t; intros K d k u Hlc Hle; inversion Hlc; subst; simpl; auto.
  - destruct (Nat.eqb k n) eqn:Heq; [apply Nat.eqb_eq in Heq; lia|reflexivity].
  - f_equal; eapply IHt; eauto; lia.
  - f_equal; [eapply IHt1|eapply IHt2]; eauto; lia.
  - f_equal; eapply IHt; eauto; lia.
  - f_equal; eapply IHt; eauto; lia.
  - f_equal; [eapply IHt1|eapply IHt2|eapply IHt3]; eauto; lia.
  - f_equal; [eapply IHt1|eapply IHt2]; eauto; lia.
Qed.

Lemma closed_tm_ty_open_identity : forall t K d k U,
  lc_tm_at K d t -> K <= k -> open_tm_ty_rec k U t = t.
Proof.
  induction t; intros K d k U Hlc Hle; inversion Hlc; subst; simpl; auto.
  - f_equal; [eapply closed_ty_open_identity|eapply IHt]; eauto; lia.
  - f_equal; [eapply IHt1|eapply IHt2]; eauto; lia.
  - f_equal; eapply IHt; eauto; lia.
  - f_equal; [eapply IHt|eapply closed_ty_open_identity]; eauto; lia.
  - f_equal; [eapply IHt1|eapply IHt2|eapply IHt3]; eauto; lia.
  - f_equal; [eapply IHt1|eapply IHt2]; eauto; lia.
Qed.

Lemma instantiate_ty_update_fresh : forall T X theta U,
  ~ In X (ty_free_atoms T) ->
  instantiate_ty (type_substitution_update theta X U) T = instantiate_ty theta T.
Proof.
  induction T; intros X theta U Hfresh; simpl in *; auto.
  - unfold type_substitution_update.
    destruct (Nat.eqb X a) eqn:Heq;
      [apply Nat.eqb_eq in Heq; subst; exfalso; apply Hfresh; simpl; auto|reflexivity].
  - f_equal; apply IHT1 + apply IHT2;
      intro Hin; apply Hfresh; apply in_or_app; auto.
  - f_equal; apply IHT; exact Hfresh.
Qed.

Lemma instantiate_ty_open_fvar : forall T k X theta U,
  ~ In X (ty_free_atoms T) -> type_substitution_closed theta ->
  instantiate_ty (type_substitution_update theta X U)
    (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k U (instantiate_ty theta T).
Proof.
  induction T; intros k X theta U Hfresh Htheta; simpl in *.
  - destruct (Nat.eqb k n) eqn:Heq; simpl;
      [unfold type_substitution_update; rewrite Nat.eqb_refl|]; reflexivity.
  - unfold type_substitution_update.
    destruct (Nat.eqb X a) eqn:Heq.
    + apply Nat.eqb_eq in Heq; subst; exfalso; apply Hfresh; simpl; auto.
    + symmetry; apply (closed_ty_open_identity (theta a) 0 k U);
        [apply Htheta|lia].
  - assert (Hfresh1 : ~ In X (ty_free_atoms T1)) by
      (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (Hfresh2 : ~ In X (ty_free_atoms T2)) by
      (intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
    rewrite (IHT1 k X theta U Hfresh1 Htheta),
      (IHT2 k X theta U Hfresh2 Htheta); reflexivity.
  - rewrite (IHT (S k) X theta U Hfresh Htheta); reflexivity.
  - reflexivity.
Qed.

Lemma instantiate_tm_open_fvar : forall t k x theta gamma v,
  ~ In x (tm_free_atoms t) -> term_substitution_closed gamma ->
  instantiate theta (term_substitution_update gamma x v)
    (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k v (instantiate theta gamma t).
Proof.
  induction t; intros k x theta gamma v Hfresh Hgamma; simpl in *; auto.
  - destruct (Nat.eqb k n); simpl;
      [unfold term_substitution_update; rewrite Nat.eqb_refl|]; reflexivity.
  - unfold term_substitution_update.
    destruct (Nat.eqb x a) eqn:Heq.
    + apply Nat.eqb_eq in Heq; subst; exfalso; apply Hfresh; simpl; auto.
    + symmetry; apply (closed_tm_open_identity (gamma a) 0 0 k v);
        [apply Hgamma|lia].
  - rewrite (IHt (S k) x theta gamma v Hfresh Hgamma); reflexivity.
  - assert (Hfresh1 : ~ In x (tm_free_atoms t1)) by
      (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (Hfresh2 : ~ In x (tm_free_atoms t2)) by
      (intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
    rewrite (IHt1 k x theta gamma v Hfresh1 Hgamma),
      (IHt2 k x theta gamma v Hfresh2 Hgamma); reflexivity.
  - rewrite (IHt k x theta gamma v Hfresh Hgamma); reflexivity.
  - rewrite (IHt k x theta gamma v Hfresh Hgamma); reflexivity.
  - assert (Hfresh1 : ~ In x (tm_free_atoms t1)) by
      (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (Hfresh2 : ~ In x (tm_free_atoms t2)) by
      (intro Hin; apply Hfresh; apply in_or_app; right; apply in_or_app; left; exact Hin).
    assert (Hfresh3 : ~ In x (tm_free_atoms t3)) by
      (intro Hin; apply Hfresh; apply in_or_app; right; apply in_or_app; right; exact Hin).
    rewrite (IHt1 k x theta gamma v Hfresh1 Hgamma),
      (IHt2 k x theta gamma v Hfresh2 Hgamma),
      (IHt3 k x theta gamma v Hfresh3 Hgamma); reflexivity.
  - assert (Hfresh1 : ~ In x (tm_free_atoms t1)) by
      (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (Hfresh2 : ~ In x (tm_free_atoms t2)) by
      (intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
    rewrite (IHt1 k x theta gamma v Hfresh1 Hgamma),
      (IHt2 k x theta gamma v Hfresh2 Hgamma); reflexivity.
Qed.

Lemma instantiate_tm_ty_open_fvar : forall t k X theta gamma U,
  ~ In X (tm_type_free_atoms t) ->
  type_substitution_closed theta -> term_substitution_closed gamma ->
  instantiate (type_substitution_update theta X U) gamma
    (open_tm_ty_rec k (Ty_FVar X) t) =
  open_tm_ty_rec k U (instantiate theta gamma t).
Proof.
  induction t; intros k X theta gamma U Hfresh Htheta Hgamma;
    simpl in *; auto.
  - symmetry; apply (closed_tm_ty_open_identity (gamma a) 0 0 k U);
      [apply Hgamma|lia].
  - assert (Hfresh1 : ~ In X (ty_free_atoms t)) by
      (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (Hfresh2 : ~ In X (tm_type_free_atoms t0)) by
      (intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
    rewrite (instantiate_ty_open_fvar t k X theta U Hfresh1 Htheta),
      (IHt (k) X theta gamma U Hfresh2 Htheta Hgamma); reflexivity.
  - assert (Hfresh1 : ~ In X (tm_type_free_atoms t1)) by
      (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (Hfresh2 : ~ In X (tm_type_free_atoms t2)) by
      (intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
    rewrite (IHt1 k X theta gamma U Hfresh1 Htheta Hgamma),
      (IHt2 k X theta gamma U Hfresh2 Htheta Hgamma); reflexivity.
  - rewrite (IHt (S k) X theta gamma U Hfresh Htheta Hgamma); reflexivity.
  - assert (Hfresh1 : ~ In X (tm_type_free_atoms t)) by
      (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (Hfresh2 : ~ In X (ty_free_atoms t0)) by
      (intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
    rewrite (IHt k X theta gamma U Hfresh1 Htheta Hgamma),
      (instantiate_ty_open_fvar t0 k X theta U Hfresh2 Htheta); reflexivity.
  - assert (Hfresh1 : ~ In X (tm_type_free_atoms t1)) by
      (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (Hfresh2 : ~ In X (tm_type_free_atoms t2)) by
      (intro Hin; apply Hfresh; apply in_or_app; right; apply in_or_app; left; exact Hin).
    assert (Hfresh3 : ~ In X (tm_type_free_atoms t3)) by
      (intro Hin; apply Hfresh; apply in_or_app; right; apply in_or_app; right; exact Hin).
    rewrite (IHt1 k X theta gamma U Hfresh1 Htheta Hgamma),
      (IHt2 k X theta gamma U Hfresh2 Htheta Hgamma),
      (IHt3 k X theta gamma U Hfresh3 Htheta Hgamma); reflexivity.
  - assert (Hfresh1 : ~ In X (tm_type_free_atoms t1)) by
      (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (Hfresh2 : ~ In X (tm_type_free_atoms t2)) by
      (intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
    rewrite (IHt1 k X theta gamma U Hfresh1 Htheta Hgamma),
      (IHt2 k X theta gamma U Hfresh2 Htheta Hgamma); reflexivity.
Qed.

Lemma type_update_closed : forall theta X U,
  type_substitution_closed theta -> locally_closed_ty U ->
  type_substitution_closed (type_substitution_update theta X U).
Proof.
  intros theta X U Htheta HU Y; unfold type_substitution_update.
  destruct (Nat.eqb X Y); auto.
Qed.

Lemma term_update_closed : forall gamma x v,
  term_substitution_closed gamma -> locally_closed_tm v ->
  term_substitution_closed (term_substitution_update gamma x v).
Proof.
  intros gamma x v Hgamma Hv y; unfold term_substitution_update.
  destruct (Nat.eqb x y); auto.
Qed.

Lemma instantiate_ty_lc : forall T K theta,
  lc_ty_at K T -> type_substitution_closed theta ->
  lc_ty_at K (instantiate_ty theta T).
Proof.
  intros T K theta Hlc; induction Hlc; intros Htheta; simpl.
  - constructor; assumption.
  - eapply lc_ty_weaken; [apply Htheta|lia].
  - constructor; auto.
  - constructor; auto.
  - constructor.
Qed.

Lemma instantiate_tm_lc : forall t K k theta gamma,
  lc_tm_at K k t -> type_substitution_closed theta ->
  term_substitution_closed gamma ->
  lc_tm_at K k (instantiate theta gamma t).
Proof.
  intros t K k theta gamma Hlc; induction Hlc; intros Htheta Hgamma;
    simpl; try (constructor; eauto using instantiate_ty_lc).
  - eapply lc_tm_weaken; [apply Hgamma|lia|lia].
Qed.

Lemma instantiate_closed : forall t theta gamma,
  locally_closed_tm t -> type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm (instantiate theta gamma t).
Proof. intros; eapply instantiate_tm_lc; eauto. Qed.

Lemma typing_result_closed : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_ty T.
Proof.
  intros Delta Gamma t T Htype; induction Htype.
  - eapply wf_ty_closed; eassumption.
  - unfold locally_closed_ty in *; constructor;
      [eapply wf_ty_closed; eassumption|].
    destruct (fresh_atom L) as [x Hx]; exact (H1 x Hx).
  - inversion IHHtype1; assumption.
  - unfold locally_closed_ty in *; constructor.
    destruct (fresh_atom L) as [X HX].
    eapply lc_open_ty_reverse; apply H0; exact HX.
  - unfold locally_closed_ty in *.
    inversion IHHtype; subst.
    eapply lc_open_ty_rec; [eassumption|eapply wf_ty_closed; eassumption].
  - constructor.
  - constructor.
  - assumption.
  - assumption.
Qed.

Lemma related_term_update : forall rho Gamma gamma x T v,
  related_substitution rho Gamma gamma -> value_relation [] rho T v ->
  related_substitution rho (update Gamma x T)
    (term_substitution_update gamma x v).
Proof.
  intros rho Gamma gamma x T v Hrelated Hvalue y S Hlookup.
  simpl in Hlookup; unfold term_substitution_update.
  destruct (Nat.eqb y x) eqn:Heq.
  - apply Nat.eqb_eq in Heq; subst y.
    inversion Hlookup; subst.
    rewrite Nat.eqb_refl; exact Hvalue.
  - rewrite Nat.eqb_sym, Heq.
    apply Hrelated; exact Hlookup.
Qed.

Lemma lookup_context_fresh : forall Gamma x T X,
  lookup_context x Gamma = Some T ->
  ~ In X (context_type_free_atoms Gamma) ->
  ~ In X (ty_free_atoms T).
Proof.
  induction Gamma as [|[y S] Gamma IH]; intros x T X Hlookup Hfresh;
    simpl in *; [discriminate|].
  destruct (Nat.eqb x y) eqn:Heq.
  - inversion Hlookup; subst T; intro Hin.
    apply Hfresh; apply in_or_app; left; exact Hin.
  - eapply IH; [exact Hlookup|].
    intro Hin; apply Hfresh; apply in_or_app; right; exact Hin.
Qed.

Lemma related_type_update : forall rho Gamma gamma X a,
  related_substitution rho Gamma gamma ->
  ~ In X (context_type_free_atoms Gamma) ->
  related_substitution (relation_update rho X a) Gamma gamma.
Proof.
  intros rho Gamma gamma X candidate Hrelated Hfresh x T Hlookup.
  apply (proj2 (value_relation_env_fresh T X candidate [] rho (gamma x)
    (lookup_context_fresh Gamma x T X Hlookup Hfresh))).
  apply Hrelated; exact Hlookup.
Qed.

Theorem fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall theta gamma rho,
    type_substitution_closed theta -> term_substitution_closed gamma ->
    related_substitution rho Gamma gamma ->
    expression_relation [] rho T (instantiate theta gamma t).
Proof.
  intros Delta Gamma t T Htype.
  induction Htype; intros theta gamma rho Htheta Hgamma Hrelated; simpl.
  - assert (Hvalue : value_relation [] rho T (gamma x)) by
      (apply Hrelated; assumption).
    apply lifting_value; [eapply value_relation_value; eassumption|
      eapply value_closed, value_relation_value; eassumption|exact Hvalue].
  - assert (Habs : locally_closed_tm
        (tm_abs (instantiate_ty theta T1) (instantiate theta gamma t2))) by
      (change (locally_closed_tm (instantiate theta gamma (tm_abs T1 t2)));
        eapply instantiate_closed;
        [eapply typing_closed; eauto using T_Abs|exact Htheta|exact Hgamma]).
    apply lifting_value; [constructor; exact Habs|exact Habs|].
    simpl. split; [constructor; exact Habs|].
    exists (instantiate_ty theta T1), (instantiate theta gamma t2).
    split; [reflexivity|].
    intros arg Harg.
    destruct (fresh_atom (L ++ tm_free_atoms t2)) as [x Hfresh].
    assert (Hx : ~ In x L) by
      (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (HfreshTerm : ~ In x (tm_free_atoms t2)) by
      (intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
    assert (HargValue : value arg) by
      (eapply value_relation_value; exact Harg).
    specialize (H1 x Hx theta (term_substitution_update gamma x arg) rho
      Htheta (term_update_closed gamma x arg Hgamma (value_closed _ HargValue))
      (related_term_update rho Gamma gamma x T1 arg Hrelated Harg)).
    unfold open_tm in *.
    rewrite <- (instantiate_tm_open_fvar t2 0 x theta gamma arg
      HfreshTerm Hgamma).
    exact H1.
  - eapply lifting_app; eauto.
  - assert (Htabs : locally_closed_tm (tm_tabs (instantiate theta gamma t))) by
      (change (locally_closed_tm (instantiate theta gamma (tm_tabs t)));
        eapply instantiate_closed;
        [eapply typing_closed; eauto using T_TAbs|exact Htheta|exact Hgamma]).
    apply lifting_value; [constructor; exact Htabs|exact Htabs|].
    simpl. split; [constructor; exact Htabs|].
    exists (instantiate theta gamma t); split; [reflexivity|].
    intros U candidate HU.
    destruct (fresh_atom
      (L ++ context_type_free_atoms Gamma ++ ty_free_atoms T ++
        tm_type_free_atoms t)) as [X Hfresh].
    assert (HX : ~ In X L) by
      (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (HfreshGamma : ~ In X (context_type_free_atoms Gamma)) by
      (intro Hin; apply Hfresh; apply in_or_app; right;
        apply in_or_app; left; exact Hin).
    assert (HfreshType : ~ In X (ty_free_atoms T)) by
      (intro Hin; apply Hfresh; apply in_or_app; right;
        apply in_or_app; right; apply in_or_app; left; exact Hin).
    assert (HfreshTerm : ~ In X (tm_type_free_atoms t)) by
      (intro Hin; apply Hfresh; apply in_or_app; right;
        apply in_or_app; right; apply in_or_app; right; exact Hin).
    assert (HT : lc_ty_at 1 T) by
      (pose proof (typing_result_closed _ _ _ _
        (T_TAbs L Delta Gamma t T H)) as HAll; inversion HAll;
        assumption).
    specialize (H0 X HX (type_substitution_update theta X U) gamma
      (relation_update rho X candidate)
      (type_update_closed theta X U Htheta HU) Hgamma
      (related_type_update rho Gamma gamma X candidate Hrelated HfreshGamma)).
    unfold open_tm_ty in *.
    rewrite <- (instantiate_tm_ty_open_fvar t 0 X theta gamma U
      HfreshTerm Htheta Hgamma).
    apply (proj1 (lifting_equiv
      (value_relation [] (relation_update rho X candidate)
        (open_ty T (Ty_FVar X)))
      (value_relation [candidate] rho T)
      (instantiate (type_substitution_update theta X U) gamma
        (open_tm_ty t (Ty_FVar X)))
      (fun result => value_relation_open_fvar T X candidate rho result
        HT HfreshType))) in H0.
    exact H0.
  - assert (HT : lc_ty_at 1 T) by
      (pose proof (typing_result_closed _ _ _ _ Htype) as HAll;
        inversion HAll; assumption).
    assert (HU : locally_closed_ty U) by (eapply wf_ty_closed; eassumption).
    eapply (lifting_tapp [] rho T (value_relation [] rho (open_ty T U))
      (instantiate theta gamma t) (instantiate_ty theta U)
      (candidate_for_type [] rho U)).
    + apply IHHtype; assumption.
    + eapply instantiate_ty_lc; [exact HU|exact Htheta].
    + intros body Hbody.
      apply (proj2 (lifting_equiv
        (value_relation [] rho (open_ty T U))
        (value_relation [candidate_for_type [] rho U] rho T)
        (open_tm_ty body (instantiate_ty theta U))
        (fun result => value_relation_open_closed T U rho result HT HU))).
      exact Hbody.
  - apply lifting_value; [constructor|constructor|].
    simpl; split; [constructor|left; reflexivity].
  - apply lifting_value; [constructor|constructor|].
    simpl; split; [constructor|right; reflexivity].
  - eapply (lifting_if [] rho (value_relation [] rho T)).
    + apply IHHtype1; assumption.
    + apply IHHtype2; assumption.
    + apply IHHtype3; assumption.
  - eapply (lifting_choice (value_relation [] rho T)).
    + apply IHHtype1; assumption.
    + apply IHHtype2; assumption.
Qed.

Lemma instantiate_ty_identity : forall T,
  instantiate_ty (fun X => Ty_FVar X) T = T.
Proof.
  induction T; simpl; try rewrite IHT1; try rewrite IHT2;
    try rewrite IHT; reflexivity.
Qed.

Lemma instantiate_identity : forall t,
  instantiate (fun X => Ty_FVar X) (fun x => tm_fvar x) t = t.
Proof.
  induction t; simpl; try rewrite IHt1; try rewrite IHt2; try rewrite IHt3;
    try rewrite IHt; try rewrite instantiate_ty_identity; reflexivity.
Qed.

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  intros t T Htype.
  pose proof (fundamental [] empty t T Htype
    (fun X => Ty_FVar X) (fun x => tm_fvar x)
    (fun _ => None)) as Hfund.
  assert (Htheta : type_substitution_closed (fun X => Ty_FVar X)) by
    (intros X; constructor).
  assert (Hgamma : term_substitution_closed (fun x => tm_fvar x)) by
    (intros x; constructor).
  assert (Hrelated : related_substitution (fun _ => None) empty
    (fun x => tm_fvar x)) by
    (intros x S Hlookup; discriminate Hlookup).
  specialize (Hfund Htheta Hgamma Hrelated).
  rewrite instantiate_identity in Hfund.
  exact (proj1 (proj2 Hfund)).
Qed.

End SystemFNormalizationIfNondeterminismMediumTask.
