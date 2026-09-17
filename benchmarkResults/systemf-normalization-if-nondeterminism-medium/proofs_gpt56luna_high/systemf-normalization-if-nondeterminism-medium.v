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

(* Some elementary facts about the operational semantics. *)

Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof.
  intros v Hv. inversion Hv; subst; unfold locally_closed_tm; eauto.
Qed.

Lemma value_no_step : forall v u, value v -> ~ v --> u.
Proof.
  intros v u Hv Hs. destruct Hv; inversion Hs.
Qed.

Lemma value_sn : forall v, value v -> strongly_normalizing v.
Proof.
  intros v Hv. constructor. intros u Hu. exfalso.
  eapply value_no_step; eauto.
Qed.

Lemma lc_ty_weaken : forall k T, lc_ty_at k T -> lc_ty_at (S k) T.
Proof.
  intros k T H. induction H; eauto; constructor; lia.
Qed.

Lemma lc_tm_weaken : forall K k t, lc_tm_at K k t -> lc_tm_at K (S k) t.
Proof.
  intros K k t H. induction H; eauto; constructor; lia.
Qed.

Lemma lc_ty_weaken_ty : forall K T, lc_ty_at K T -> lc_ty_at (S K) T.
Proof.
  intros K T H. induction H; eauto; constructor; lia.
Qed.

Lemma lc_tm_weaken_ty : forall K k t, lc_tm_at K k t -> lc_tm_at (S K) k t.
Proof.
  intros K k t H. induction H; eauto using lc_ty_weaken_ty.
Qed.

Lemma lc_ty_open_rec : forall k U T,
    lc_ty_at (S k) T -> lc_ty_at k U ->
    lc_ty_at k (open_ty_rec k U T).
Proof.
  intros k U T. revert k U.
  induction T as [i|X|T1 IH1 T2 IH2|T IH|];
    intros k U Ht Hu; simpl; inversion Ht; subst; eauto.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst. exact Hu.
    + apply lc_ty_bvar. apply Nat.eqb_neq in E. lia.
  - apply lc_ty_all. apply IH; eauto using lc_ty_weaken.
Qed.

Lemma lc_tm_open_rec : forall K k u t,
    lc_tm_at K (S k) t -> lc_tm_at K k u ->
    lc_tm_at K k (open_tm_rec k u t).
Proof.
  intros K k u t. revert K k u.
  induction t as [i|x|T t IH|t1 IH1 t2 IH2|t IH|t IH| | |
                   t1 IH1 t2 IH2 t3 IH3|t1 IH1 t2 IH2];
    intros K k u Ht Hu; simpl; inversion Ht; subst; eauto.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst. exact Hu.
    + apply lc_tm_bvar. apply Nat.eqb_neq in E. lia.
  - apply lc_tm_abs; eauto. apply IH; eauto using lc_tm_weaken.
  - apply lc_tm_tabs. apply IH; eauto using lc_tm_weaken, lc_tm_weaken_ty.
Qed.

Lemma lc_tm_ty_open_rec : forall K k U t,
    lc_tm_at (S K) k t -> lc_ty_at K U ->
    lc_tm_at K k (open_tm_ty_rec K U t).
Proof.
  intros K k U t. revert K k U.
  induction t as [i|x|T t IH|t1 IH1 t2 IH2|t IH|t IH| | |
                   t1 IH1 t2 IH2 t3 IH3|t1 IH1 t2 IH2];
    intros K k U Ht Hu; simpl; inversion Ht; subst; eauto.
  - apply lc_tm_abs.
    + eapply lc_ty_open_rec; eauto.
    + apply IH; eauto.
  - apply lc_tm_tabs. apply IH; eauto using lc_ty_weaken.
  - apply lc_tm_tapp.
    + apply IH; eauto.
    + eapply lc_ty_open_rec; eauto.
Qed.

Lemma lc_open_tm : forall t u,
    lc_tm_at 0 1 t -> locally_closed_tm u ->
    locally_closed_tm (open_tm t u).
Proof.
  intros. unfold locally_closed_tm, open_tm. eapply lc_tm_open_rec; eauto.
Qed.

Lemma lc_open_tm_ty : forall t U,
    lc_tm_at 1 0 t -> locally_closed_ty U ->
    locally_closed_tm (open_tm_ty t U).
Proof.
  intros. unfold locally_closed_tm, open_tm_ty. eapply lc_tm_ty_open_rec; eauto.
Qed.

Lemma lc_abs_body : forall T t,
    locally_closed_tm (tm_abs T t) -> lc_tm_at 0 1 t.
Proof. intros; inversion H; assumption. Qed.

Lemma lc_tabs_body : forall t,
    locally_closed_tm (tm_tabs t) -> lc_tm_at 1 0 t.
Proof. intros; inversion H; assumption. Qed.

Lemma lc_app_abs_body : forall T t v,
    locally_closed_tm (tm_app (tm_abs T t) v) -> lc_tm_at 0 1 t.
Proof. intros T t v H; inversion H; subst; eapply lc_abs_body; eauto. Qed.

Lemma lc_tapp_tabs_body : forall t T,
    locally_closed_tm (tm_tapp (tm_tabs t) T) -> lc_tm_at 1 0 t.
Proof. intros t T H; inversion H; subst; eapply lc_tabs_body; eauto. Qed.

Lemma lc_step : forall t u, locally_closed_tm t -> t --> u -> locally_closed_tm u.
Proof.
  intros t u Hlc Hs. revert Hlc.
  induction Hs; intros Hlc; unfold locally_closed_tm in *.
  - apply lc_open_tm.
    + inversion Hlc; subst; eauto using lc_abs_body.
    + eapply value_lc; eauto.
  - apply lc_tm_app.
    + eapply IHHs. inversion Hlc; assumption.
    + inversion Hlc; assumption.
  - apply lc_tm_app.
    + inversion Hlc; assumption.
    + eapply IHHs; inversion Hlc; assumption.
  - apply lc_open_tm_ty.
    + inversion Hlc; subst; eauto using lc_tabs_body.
    + assumption.
  - apply lc_tm_tapp.
    + eapply IHHs; inversion Hlc; assumption.
    + inversion Hlc; assumption.
  - inversion Hlc; assumption.
  - inversion Hlc; assumption.
  - apply lc_tm_if.
    + eapply IHHs; inversion Hlc; assumption.
    + inversion Hlc; assumption.
    + inversion Hlc; assumption.
  - inversion Hlc; assumption.
  - inversion Hlc; assumption.
Qed.

Lemma multi_step_l : forall t u v, t --> u -> u -->* v -> t -->* v.
Proof.
  intros. econstructor; eauto.
Qed.

Lemma multi_trans : forall t u v, t -->* u -> u -->* v -> t -->* v.
Proof.
  intros t u v H. induction H; eauto using multi_step_l.
Qed.

Lemma expression_lifting_step : forall R t u,
    expression_lifting R t -> t --> u -> expression_lifting R u.
Proof.
  intros R t u [Hlc [Hsn Hterm]] Hstep.
  repeat split.
  - eapply lc_step; eauto.
  - constructor. intros v Hv. eapply Hsn; eauto.
  - intros v Huv Hv. eapply Hterm; eauto using multi_step_l.
Qed.

Lemma expression_lifting_multi : forall R t u,
    expression_lifting R t -> t -->* u -> expression_lifting R u.
Proof.
  intros R t u H Hm. induction Hm; eauto using expression_lifting_step.
Qed.

Lemma value_relation_value : forall eta rho T v,
    value_relation eta rho T v -> value v.
Proof.
  induction T as [i|X|T1 IH1 T2 IH2|T IH|]; simpl; intros v H;
    try (destruct (nth_error eta i) as [a|] eqn:E; simpl in H;
         [eapply a.(candidate_values); eauto | contradiction]);
    try (destruct (rho X) as [a|] eqn:E; simpl in H;
         [eapply a.(candidate_values); eauto | contradiction]);
    try tauto.
Qed.

Lemma value_relation_lc : forall eta rho T v,
    value_relation eta rho T v -> locally_closed_tm v.
Proof.
  intros. eapply value_lc. eapply value_relation_value; eauto.
Qed.

Lemma value_relation_sn : forall eta rho T v,
    value_relation eta rho T v -> strongly_normalizing v.
Proof.
  intros. eapply value_sn. eapply value_relation_value; eauto.
Qed.

Fixpoint tm_atoms (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs _ t1 => tm_atoms t1
  | tm_app t1 t2 => tm_atoms t1 ++ tm_atoms t2
  | tm_tabs t1 => tm_atoms t1
  | tm_tapp t1 _ => tm_atoms t1
  | tm_true | tm_false => []
  | tm_if t1 t2 t3 => tm_atoms t1 ++ tm_atoms t2 ++ tm_atoms t3
  | tm_choice t1 t2 => tm_atoms t1 ++ tm_atoms t2
  end.

Fixpoint ty_atoms (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow T1 T2 => ty_atoms T1 ++ ty_atoms T2
  | Ty_All T1 => ty_atoms T1
  | Ty_Bool => []
  end.

Fixpoint term_inst (gamma : term_substitution) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => gamma x
  | tm_abs T t1 => tm_abs T (term_inst gamma t1)
  | tm_app t1 t2 => tm_app (term_inst gamma t1) (term_inst gamma t2)
  | tm_tabs t1 => tm_tabs (term_inst gamma t1)
  | tm_tapp t1 T => tm_tapp (term_inst gamma t1) T
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (term_inst gamma t1) (term_inst gamma t2) (term_inst gamma t3)
  | tm_choice t1 t2 => tm_choice (term_inst gamma t1) (term_inst gamma t2)
  end.

Lemma term_inst_open_rec : forall k gamma x s t,
    ~ In x (tm_atoms t) ->
    term_inst (update gamma x s) (open_tm_rec k (tm_fvar x) t) =
    open_tm_rec k s (term_inst gamma t).
Proof.
  intros k gamma x s t. revert k.
  induction t as [i|y|T t IH|t1 IH1 t2 IH2|t IH|t IH| | |
                   t1 IH1 t2 IH2 t3 IH3|t1 IH1 t2 IH2];
    intros k Hfresh; simpl in *; try reflexivity.
  - destruct (Nat.eqb k i) eqn:E; simpl.
    + reflexivity.
    + reflexivity.
  - destruct (Nat.eqb x y) eqn:E; simpl in *.
    + exfalso. apply Hfresh. simpl. apply Nat.eqb_eq in E. subst. auto.
    + reflexivity.
  - f_equal. apply IH. assumption.
  - f_equal; [apply IH1 | apply IH2]; simpl in *; intuition.
  - f_equal. apply IH. assumption.
  - f_equal. apply IH. assumption.
  - f_equal; [apply IH1 | apply IH2 | apply IH3]; simpl in *; intuition.
  - f_equal; [apply IH1 | apply IH2]; simpl in *; intuition.
Qed.

Lemma term_inst_open : forall gamma x s t,
    ~ In x (tm_atoms t) ->
    term_inst (update gamma x s) (open_tm t (tm_fvar x)) =
    open_tm (term_inst gamma t) s.
Proof. intros; unfold open_tm; apply term_inst_open_rec; assumption. Qed.

Lemma term_inst_open_tm_ty_rec : forall k gamma U t,
    term_inst gamma (open_tm_ty_rec k U t) =
    open_tm_ty_rec k U (term_inst gamma t).
Proof.
  intros k gamma U t. revert k U.
  induction t as [i|x|T t IH|t1 IH1 t2 IH2|t IH|t IH| | |
                   t1 IH1 t2 IH2 t3 IH3|t1 IH1 t2 IH2];
    intros k U; simpl; try reflexivity.
  - f_equal. apply IH.
  - f_equal; [apply IH1 | apply IH2].
  - f_equal. apply IH.
  - f_equal. apply IH.
  - f_equal; [apply IH1 | apply IH2 | apply IH3].
  - f_equal; [apply IH1 | apply IH2].
Qed.

Lemma term_inst_open_tm_ty : forall gamma U t,
    term_inst gamma (open_tm_ty t U) =
    open_tm_ty (term_inst gamma t) U.
Proof. intros; unfold open_tm_ty; apply term_inst_open_tm_ty_rec. Qed.

Lemma not_in_exists : forall (xs : list atom), exists x, ~ In x xs.
Proof.
  induction xs as [|x xs IH].
  - exists 0; simpl; tauto.
  - destruct IH as [y Hy]. exists (S (x + y)).
    intro H. simpl in H. destruct H as [<-|H]. lia. apply Hy.
    lia.
Qed.

Definition ty_atoms_ctx (Delta : ty_context) : list atom := Delta.
Definition tm_atoms_ctx (Gamma : context) : list atom :=
  map fst Gamma.

Fixpoint candidate_insert (k : nat) (a : value_candidate)
    (eta : list value_candidate) : list value_candidate :=
  match k, eta with
  | 0, [] => [a]
  | 0, _ => a :: eta
  | S k', [] => []
  | S k', b :: eta' => b :: candidate_insert k' a eta'
  end.

Lemma nth_error_candidate_insert : forall k eta a,
    k <= length eta -> forall i, i <= k ->
    nth_error (candidate_insert k a eta) i =
      if Nat.eqb k i then Some a else nth_error eta i.
Proof.
  induction k as [|k IH]; intros eta a Hlen i.
  - intros Hi. destruct i; simpl; reflexivity. lia.
  - intros Hi. destruct eta as [|b eta]; simpl in Hlen; try lia.
    destruct i as [|i]; simpl.
    + reflexivity.
    + rewrite IH by lia. destruct (Nat.eqb k i); reflexivity.
Qed.

Lemma expression_lifting_ext : forall R S t,
    (forall v, R v <-> S v) ->
    expression_lifting R t <-> expression_lifting S t.
Proof.
  intros R S t He. unfold expression_lifting. tauto.
Qed.

Definition eta_agree (k : nat) (eta eta' : list value_candidate) : Prop :=
  forall i, i < k -> nth_error eta i = nth_error eta' i.

Lemma eta_agree_cons : forall k eta eta' a,
    eta_agree k eta eta' -> eta_agree (S k) (a :: eta) (a :: eta').
Proof.
  intros k eta eta' a H i Hi. destruct i; simpl; auto. apply H; lia.
Qed.

Lemma value_relation_eta_agree : forall k eta eta' rho T v,
    lc_ty_at k T -> eta_agree k eta eta' ->
    value_relation eta rho T v <-> value_relation eta' rho T v.
Proof.
  intros k eta eta' rho T v Hlc Hag. revert k eta eta' rho v Hag.
  induction T as [i|X|T1 IH1 T2 IH2|T IH|];
    intros k eta eta' rho v Hag; simpl in *.
  - inversion Hlc. subst. specialize (Hag i ltac:(lia)).
    rewrite Hag. tauto.
  - tauto.
  - inversion Hlc; subst. split; intros H.
    + destruct H as [Hv [U [body [Heq H]]]]. split; [assumption|].
      exists U, body. split; [assumption|].
      intros arg Ha. eapply (expression_lifting_ext
        (value_relation eta rho T2) (value_relation eta' rho T2)
        (open_tm body arg)).2.
      * intro z. eapply IH2; eauto.
      * apply H. eapply (IH1 k eta eta' rho arg); eauto.
    + destruct H as [Hv [U [body [Heq H]]]]. split; [assumption|].
      exists U, body. split; [assumption|].
      intros arg Ha. eapply (expression_lifting_ext
        (value_relation eta rho T2) (value_relation eta' rho T2)
        (open_tm body arg)).1.
      * intro z. eapply IH2; eauto.
      * apply H. eapply (IH1 k eta eta' rho arg); eauto.
  - inversion Hlc; subst. split; intros H.
    + destruct H as [Hv [body [Heq H]]]. split; [assumption|].
      exists body. split; [assumption|]. intros U a HU Ha.
      eapply (expression_lifting_ext
        (value_relation (a :: eta) rho T)
        (value_relation (a :: eta') rho T)
        (open_tm_ty body U)).2.
      * intro z. eapply IH; eauto using eta_agree_cons.
      * apply H; assumption.
    + destruct H as [Hv [body [Heq H]]]. split; [assumption|].
      exists body. split; [assumption|]. intros U a HU Ha.
      eapply (expression_lifting_ext
        (value_relation (a :: eta) rho T)
        (value_relation (a :: eta') rho T)
        (open_tm_ty body U)).1.
      * intro z. eapply IH; eauto using eta_agree_cons.
      * apply H; assumption.
  - tauto.
Qed.

Lemma value_relation_open_rec : forall k eta rho X a T v,
    lc_ty_at (S k) T -> ~ In X (ty_atoms T) -> k <= length eta ->
    value_relation eta (relation_update rho X a)
      (open_ty_rec k (Ty_FVar X) T) v <-
    value_relation (candidate_insert k a eta) rho T v.
Proof.
  intros k eta rho X a T v Hlc Hfresh Hlen. revert k eta rho X a v Hlen.
  induction T as [i|Y|T1 IH1 T2 IH2|T IH|];
    intros k eta rho X a v Hlen; simpl in *.
  - inversion Hlc. subst.
    destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst.
      rewrite nth_error_candidate_insert by assumption; [|lia].
      simpl. destruct (rho X); simpl; tauto.
    + rewrite nth_error_candidate_insert by assumption; [|lia].
      apply Nat.eqb_neq in E. rewrite Nat.eqb_sym, E. simpl. tauto.
  - destruct (Nat.eqb X Y) eqn:E.
    + exfalso. apply Hfresh. simpl. apply Nat.eqb_eq in E. subst. auto.
    + apply Nat.eqb_neq in E. simpl. rewrite E. reflexivity.
  - inversion Hlc; subst. simpl in Hfresh.
    unfold value_relation in *; simpl.
    repeat rewrite IH1 by (intuition; lia).
    repeat rewrite IH2 by (intuition; lia).
    tauto.
  - inversion Hlc; subst. simpl in Hfresh.
    unfold value_relation in *; simpl.
    split; intros H.
    + destruct H as [Hv [body [Heq Hall]]]. subst v.
      split; [assumption|]. exists body. split; [reflexivity|].
      intros U b HbU Hb.
      eapply (expression_lifting_ext
        (value_relation (b :: eta) (relation_update rho X a)
          (open_ty_rec (S k) (Ty_FVar X) T))
        (value_relation (b :: candidate_insert k a eta) rho T)
        (open_tm_ty body U)).2.
      * intro z. eapply IH; eauto. simpl in *. lia.
      * apply Hall; assumption.
    + destruct H as [Hv [body [Heq Hall]]]. subst v.
      split; [assumption|]. exists body. split; [reflexivity|].
      intros U b HbU Hb.
      eapply (expression_lifting_ext
        (value_relation (b :: eta) (relation_update rho X a)
          (open_ty_rec (S k) (Ty_FVar X) T))
        (value_relation (b :: candidate_insert k a eta) rho T)
        (open_tm_ty body U)).1.
      * intro z. eapply IH; eauto. simpl in *. lia.
      * apply Hall; assumption.
  - tauto.
Qed.

Lemma value_relation_open : forall eta rho X a T v,
    lc_ty_at 1 T -> ~ In X (ty_atoms T) ->
    value_relation eta (relation_update rho X a)
      (open_ty T (Ty_FVar X)) v <-
    value_relation (candidate_insert 0 a eta) rho T v.
Proof. intros; unfold open_ty; eapply value_relation_open_rec; eauto. Qed.

Lemma value_relation_open_candidate : forall k eta rho U a T v,
    lc_ty_at (S k) T ->
    (forall eta' z, value_relation eta' rho U z <-> a.(candidate_relation) z) ->
    value_relation eta rho (open_ty_rec k U T) v <-
    value_relation (candidate_insert k a eta) rho T v.
Proof.
  intros k eta rho U a T v Hlc Hrel. revert k eta rho U a v Hrel.
  induction T as [i|X|T1 IH1 T2 IH2|T IH|];
    intros k eta rho U a v Hrel; simpl in *.
  - inversion Hlc. subst. destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst.
      rewrite nth_error_candidate_insert by assumption; [|lia]. simpl. apply Hrel.
    + rewrite nth_error_candidate_insert by assumption; [|lia].
      apply Nat.eqb_neq in E. rewrite Nat.eqb_sym, E. tauto.
  - tauto.
  - inversion Hlc; subst. simpl. split; intros H.
    + destruct H as [Hv [V [body [Heq H]]]]. split; [assumption|].
      exists V, body. split; [assumption|]. intros arg Ha.
      eapply (expression_lifting_ext
        (value_relation eta rho T2)
        (value_relation (candidate_insert k a eta) rho T2)
        (open_tm body arg)).2.
      * intro z. eapply IH2; eauto.
      * apply H. eapply IH1; eauto.
    + destruct H as [Hv [V [body [Heq H]]]]. split; [assumption|].
      exists V, body. split; [assumption|]. intros arg Ha.
      eapply (expression_lifting_ext
        (value_relation eta rho T2)
        (value_relation (candidate_insert k a eta) rho T2)
        (open_tm body arg)).1.
      * intro z. eapply IH2; eauto.
      * apply H. eapply IH1; eauto.
  - inversion Hlc; subst. simpl. split; intros H.
    + destruct H as [Hv [body [Heq H]]]. split; [assumption|]. exists body.
      split; [assumption|]. intros V b HV Hb.
      eapply (expression_lifting_ext
        (value_relation (b :: eta) rho T)
        (value_relation (b :: candidate_insert k a eta) rho T)
        (open_tm_ty body V)).2.
      * intro z. eapply IH; eauto.
      * apply H; assumption.
    + destruct H as [Hv [body [Heq H]]]. split; [assumption|]. exists body.
      split; [assumption|]. intros V b HV Hb.
      eapply (expression_lifting_ext
        (value_relation (b :: eta) rho T)
        (value_relation (b :: candidate_insert k a eta) rho T)
        (open_tm_ty body V)).1.
      * intro z. eapply IH; eauto.
      * apply H; assumption.
  - tauto.
Qed.

Lemma value_relation_lc_eta_irrel : forall eta eta' rho T v,
    locally_closed_ty T ->
    value_relation eta rho T v <-> value_relation eta' rho T v.
Proof.
  intros. eapply value_relation_eta_agree with (k := 0); eauto.
  intros i Hi. lia.
Qed.

Definition semantic_candidate (eta : list value_candidate)
    (rho : relation_env) (U : ty) : value_candidate :=
  {| candidate_relation := value_relation eta rho U;
     candidate_values := fun v H => value_relation_value eta rho U v H |}.

Lemma semantic_candidate_relation : forall eta eta' rho U v,
    locally_closed_ty U ->
    value_relation eta' rho U v <->
      (semantic_candidate eta rho U).(candidate_relation) v.
Proof.
  intros. unfold semantic_candidate. simpl.
  eapply value_relation_lc_eta_irrel; eauto.
Qed.

Lemma expression_tapp_semantic : forall eta rho T U t,
    expression_relation eta rho (Ty_All T) t ->
    locally_closed_ty U ->
    expression_relation eta rho (open_ty T U) (tm_tapp t U).
Proof.
  intros eta rho T U t Ht HU. unfold expression_relation in *.
  destruct Ht as [L N F]. repeat split.
  - constructor; assumption.
  - apply sn_tapp; assumption.
    intros v Hv Hvval. destruct (F v Hv Hvval) as [body [Heq Hall]].
    subst v. destruct Hall with (U := U) (a := semantic_candidate eta rho U) HU.
    eapply (proj2 (value_relation_open_candidate 0 eta rho U
      (semantic_candidate eta rho U) T z)); eauto.
  - eapply terminal_tapp; eauto.
    intros v Hv. destruct (F v (multi_refl _) (value_relation_value _ _ _ v Hv))
      as [body [Heq Hall]]. subst v. exists body. split; [reflexivity|].
    eapply (expression_lifting_ext
      (value_relation eta rho (open_ty T U))
      (value_relation (semantic_candidate eta rho U :: eta) rho T)
      (open_tm_ty body U)).2.
    + intro z. eapply value_relation_open_candidate; eauto.
    + eapply Hall; assumption.
Qed.

Definition theta_update (theta : type_substitution) (X : atom) (U : ty) :
    type_substitution :=
  fun Y => if Nat.eqb X Y then U else theta Y.

Definition theta_closed (theta : type_substitution) : Prop :=
  forall X, locally_closed_ty (theta X).

Definition semantic_realization (Delta : ty_context)
    (theta : type_substitution) (rho : relation_env) : Prop :=
  forall X, In X Delta -> exists a,
    rho X = Some a /\
    forall eta v, value_relation eta rho (instantiate_ty theta (Ty_FVar X)) v <-
      a.(candidate_relation) v.

Definition related_substitution_theta (theta : type_substitution)
    (rho : relation_env) (Gamma : context) (gamma : term_substitution) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    value_relation [] rho (instantiate_ty theta T) (gamma x).

Fixpoint tm_ty_atoms (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_fvar _ | tm_true | tm_false => []
  | tm_abs T t1 => ty_atoms T ++ tm_ty_atoms t1
  | tm_app t1 t2 => tm_ty_atoms t1 ++ tm_ty_atoms t2
  | tm_tabs t1 => tm_ty_atoms t1
  | tm_tapp t1 T => tm_ty_atoms t1 ++ ty_atoms T
  | tm_if t1 t2 t3 => tm_ty_atoms t1 ++ tm_ty_atoms t2 ++ tm_ty_atoms t3
  | tm_choice t1 t2 => tm_ty_atoms t1 ++ tm_ty_atoms t2
  end.

Lemma theta_update_eq : forall theta X U,
    theta_update theta X U X = U.
Proof. intros; unfold theta_update; rewrite Nat.eqb_refl; reflexivity. Qed.

Lemma theta_update_neq : forall theta X U Y, X <> Y ->
    theta_update theta X U Y = theta Y.
Proof. intros; unfold theta_update; rewrite Nat.eqb_neq; assumption. Qed.

Lemma semantic_realization_update : forall Delta theta rho X U a,
    semantic_realization Delta theta rho ->
    ~ In X Delta ->
    (forall eta v, value_relation eta rho (instantiate_ty theta U) v <-
      a.(candidate_relation) v) ->
    semantic_realization (X :: Delta) (theta_update theta X U)
      (relation_update rho X a).
Proof.
  intros Delta theta rho X U a Hreal Hfresh HX Y HY.
  simpl in HY. destruct HY as [<-|HY].
  - exists a. split; [unfold relation_update; rewrite Nat.eqb_refl; reflexivity|].
    intros eta v. rewrite theta_update_eq. simpl. apply HX.
  - destruct (Hreal Y HY) as [b [Hb Hrel]]. exists b. split.
    + unfold relation_update. destruct (Nat.eqb X Y) eqn:E; auto.
      apply Nat.eqb_neq in E. rewrite E. exact Hb.
    + intros eta v. rewrite theta_update_neq by (intro; subst; apply Hfresh; assumption).
      destruct (Nat.eqb X Y) eqn:E; [exfalso; apply Hfresh; subst; assumption|].
      apply Hrel.
Qed.

Lemma open_ty_lc : forall T U,
    locally_closed_ty T -> open_ty T U = T.
Proof.
  intros T U H. unfold locally_closed_ty, open_ty in *. revert H.
  induction T as [i|X|T1 IH1 T2 IH2|T IH|]; intros H; simpl in *; inversion H; subst; eauto.
  - destruct (Nat.eqb 0 i) eqn:E; [lia|]. f_equal. apply IH; eauto.
Qed.

Lemma instantiate_ty_open : forall theta X U T,
    theta_closed theta -> ~ In X (ty_atoms T) ->
    instantiate_ty (theta_update theta X U) (open_ty T (Ty_FVar X)) =
    open_ty (instantiate_ty theta T) (instantiate_ty theta U).
Proof.
  intros theta X U T Hclosed Hfresh. unfold open_ty. revert X U theta Hclosed Hfresh.
  induction T as [i|Y|T1 IH1 T2 IH2|T IH|];
    intros X U theta Hclosed Hfresh; simpl in *.
  - destruct (Nat.eqb 0 i) eqn:E; simpl.
    + reflexivity.
    + reflexivity.
  - destruct (Nat.eqb X Y) eqn:E.
    + exfalso. apply Hfresh. simpl. apply Nat.eqb_eq in E. subst; auto.
    + simpl. rewrite E. symmetry. apply open_ty_lc; eauto.
  - simpl in *. f_equal; [apply IH1 | apply IH2]; simpl in *; intuition.
  - simpl in *. f_equal. apply IH; simpl in *; intuition.
  - reflexivity.
Qed.

Lemma instantiate_open_tm_ty : forall theta gamma X U t,
    theta_closed theta ->
    ~ In X (tm_ty_atoms t) ->
    instantiate (theta_update theta X U) gamma
      (open_tm_ty t (Ty_FVar X)) =
    open_tm_ty (instantiate theta gamma t) (instantiate_ty theta U).
Proof.
  intros theta gamma X U t Hclosed Hfresh. unfold open_tm_ty. revert X U theta gamma Hclosed Hfresh.
  induction t as [i|x|T t IH|t1 IH1 t2 IH2|t IH|t IH| | |
                   t1 IH1 t2 IH2 t3 IH3|t1 IH1 t2 IH2];
    intros X U theta gamma Hclosed Hfresh; simpl in *; try reflexivity.
  - f_equal.
    + eapply instantiate_ty_open; eauto.
    + apply IH; eauto.
  - f_equal; [apply IH1 | apply IH2]; simpl in *; intuition.
  - f_equal. apply IH; eauto.
  - f_equal. apply IH; eauto.
  - f_equal; [apply IH1 | apply IH2 | apply IH3]; simpl in *; intuition.
  - f_equal; [apply IH1 | apply IH2]; simpl in *; intuition.
Qed.

Lemma lc_ty_instantiate : forall theta k T,
    theta_closed theta -> lc_ty_at k T ->
    lc_ty_at k (instantiate_ty theta T).
Proof.
  intros theta k T Hclosed Hlc. induction Hlc; simpl; eauto.
  apply Hclosed.
Qed.

Lemma value_relation_env_no_effect : forall eta rho X a T v,
    ~ In X (ty_atoms T) ->
    value_relation eta (relation_update rho X a) T v <-
    value_relation eta rho T v.
Proof.
  intros eta rho X a T v Hfresh. revert eta rho X a v Hfresh.
  induction T as [i|Y|T1 IH1 T2 IH2|T IH|];
    intros eta rho X a v Hfresh; simpl in *.
  - tauto.
  - destruct (Nat.eqb X Y) eqn:E.
    + exfalso. apply Hfresh. simpl. apply Nat.eqb_eq in E; subst; auto.
    + apply Nat.eqb_neq in E. simpl. rewrite E. reflexivity.
  - inversion Hfresh; subst. simpl. split; intros H.
    + destruct H as [Hv [U [body [Heq H]]]]. split; [assumption|].
      exists U, body. split; [assumption|]. intros arg Ha.
      eapply (expression_lifting_ext (value_relation eta rho T2)
        (value_relation eta (relation_update rho X a) T2) (open_tm body arg)).1.
      * intro z. eapply IH2; eauto.
      * apply H. eapply IH1; eauto.
    + destruct H as [Hv [U [body [Heq H]]]]. split; [assumption|].
      exists U, body. split; [assumption|]. intros arg Ha.
      eapply (expression_lifting_ext (value_relation eta rho T2)
        (value_relation eta (relation_update rho X a) T2) (open_tm body arg)).2.
      * intro z. eapply IH2; eauto.
      * apply H. eapply IH1; eauto.
  - inversion Hfresh; subst. simpl. split; intros H.
    + destruct H as [Hv [body [Heq H]]]. split; [assumption|]. exists body.
      split; [assumption|]. intros U b HU Hb.
      eapply (expression_lifting_ext (value_relation (b :: eta) rho T)
        (value_relation (b :: eta) (relation_update rho X a) T)
        (open_tm_ty body U)).1.
      * intro z. eapply IH; eauto.
      * apply H; assumption.
    + destruct H as [Hv [body [Heq H]]]. split; [assumption|]. exists body.
      split; [assumption|]. intros U b HU Hb.
      eapply (expression_lifting_ext (value_relation (b :: eta) rho T)
        (value_relation (b :: eta) (relation_update rho X a) T)
        (open_tm_ty body U)).2.
      * intro z. eapply IH; eauto.
      * apply H; assumption.
  - tauto.
Qed.

Lemma value_relation_inst_open : forall theta eta rho X U a T v,
    theta_closed theta -> lc_ty_at 1 T -> locally_closed_ty U ->
    ~ In X (ty_atoms T) -> ~ In X (ty_atoms U) ->
    ~ In X (ty_atoms (instantiate_ty theta T)) ->
    (forall eta' z, value_relation eta' rho (instantiate_ty theta U) z <-
      a.(candidate_relation) z) ->
    value_relation eta (relation_update rho X a)
      (instantiate_ty (theta_update theta X U)
        (open_ty T (Ty_FVar X))) v <-
    value_relation (a :: eta) rho (instantiate_ty theta T) v.
Proof.
  intros theta eta rho X U a T v Hth Hlc HU HxT HxU HxI Ha.
  rewrite instantiate_ty_open by assumption.
  rewrite value_relation_env_no_effect by assumption.
  eapply (value_relation_open_candidate 0 eta rho
    (instantiate_ty theta U) a (instantiate_ty theta T) v).
  - eapply lc_ty_instantiate; eauto.
  - intros eta' z. apply Ha.
Qed.

Lemma term_inst_lc : forall K k gamma t,
    lc_tm_at K k t -> (forall x, locally_closed_tm (gamma x)) ->
    lc_tm_at K k (term_inst gamma t).
Proof.
  intros K k gamma t H. induction H; simpl; eauto using lc_ty_weaken_ty, lc_tm_weaken,
    lc_tm_weaken_ty.
Qed.

Lemma instantiate_open_tm : forall theta gamma x s t,
    ~ In x (tm_atoms t) ->
    instantiate theta (update gamma x s) (open_tm t (tm_fvar x)) =
    open_tm (instantiate theta gamma t) s.
Proof.
  intros theta gamma x s t Hfresh. unfold open_tm. revert theta gamma x s Hfresh.
  induction t as [i|y|T t IH|t1 IH1 t2 IH2|t IH|t IH| | |
                   t1 IH1 t2 IH2 t3 IH3|t1 IH1 t2 IH2];
    intros theta gamma x s Hfresh; simpl in *; try reflexivity.
  - destruct (Nat.eqb 0 i); reflexivity.
  - destruct (Nat.eqb x y) eqn:E; simpl in *.
    + exfalso. apply Hfresh. simpl. apply Nat.eqb_eq in E; subst; auto.
    + reflexivity.
  - f_equal; [reflexivity|]. apply IH; assumption.
  - f_equal; [apply IH1 | apply IH2]; simpl in *; intuition.
  - f_equal. apply IH; assumption.
  - f_equal. apply IH; assumption.
  - f_equal; [apply IH1 | apply IH2 | apply IH3]; simpl in *; intuition.
  - f_equal; [apply IH1 | apply IH2]; simpl in *; intuition.
Qed.

Lemma theta_closed_update : forall theta X U,
    theta_closed theta -> locally_closed_ty U ->
    theta_closed (theta_update theta X U).
Proof.
  intros theta X U Hth HU Y. unfold theta_update.
  destruct (Nat.eqb X Y); auto.
Qed.

Lemma multi_value_same : forall t v,
    value t -> t -->* v -> value v -> t = v.
Proof.
  intros t v Ht Hm. induction Hm; auto.
  exfalso. eapply value_no_step; eauto.
Qed.

Lemma expression_value : forall eta rho T v,
    value_relation eta rho T v ->
    expression_relation eta rho T v.
Proof.
  intros eta rho T v H. unfold expression_relation, expression_lifting.
  repeat split; try (eapply value_relation_lc; eauto); try (eapply value_relation_sn; eauto).
  intros w Hm Hw. rewrite (multi_value_same v w (value_relation_value _ _ _ _ H) Hm Hw).
  assumption.
Qed.

Lemma fundamental : forall Delta Gamma t T,
    has_type Delta Gamma t T ->
    forall theta eta rho gamma,
      theta_closed theta -> env_wf Delta rho ->
      related_substitution rho Gamma gamma ->
      (forall x, locally_closed_tm (gamma x)) ->
      expression_relation eta rho T (instantiate theta gamma t).
Proof.
  intros Delta Gamma t T H. induction H;
    intros theta eta rho gamma Htheta Henv Hrel Hgamma.
  - simpl. eapply expression_value. eapply Hrel; eauto.
  - simpl. unfold expression_relation.
    split.
    + eapply term_inst_lc; eauto using has_type_lc.
    + apply value_sn. constructor; eauto.
    + intros v Hm Hv.
      rewrite (multi_value_same _ _ (v_abs _ _ (has_type_lc H)) Hm Hv).
      unfold value_relation. simpl. split; [constructor; eauto|].
      exists T1, t2. split; [reflexivity|]. intros arg Harg.
      destruct (not_in_exists (L ++ tm_atoms t2 ++ tm_atoms_ctx Gamma)) as [x Hx].
      assert (HxL : ~ In x L) by (intro Hx'; apply Hx; apply in_or_app; left; exact Hx').
      assert (Hxbody : ~ In x (tm_atoms t2)) by
        (intro Hx'; apply Hx; apply in_or_app; right; apply in_or_app; left; exact Hx').
      assert (HxG : ~ In x (tm_atoms_ctx Gamma)) by
        (intro Hx'; apply Hx; apply in_or_app; right; apply in_or_app; right; exact Hx').
      pose proof (IH x HxL theta eta rho (update gamma x arg)
        Htheta Henv (related_update rho Gamma gamma x T1 arg HxG Hrel Harg)) as Hb.
      - rewrite instantiate_open_tm by assumption in Hb.
        exact Hb.
      - intros y. unfold update. destruct (Nat.eqb x y); auto.
        apply Hgamma.
  - simpl. eapply expression_app; eauto.
  - simpl. unfold expression_relation.
    split.
    + eapply term_inst_lc; eauto using has_type_lc.
    + apply value_sn. constructor; eauto.
    + intros v Hm Hv. rewrite (multi_value_same _ _ (v_tabs _ (has_type_lc H)) Hm Hv).
      unfold value_relation. simpl. split; [constructor; eauto|]. exists t. split; [reflexivity|].
      intros U a HU Ha.
      destruct (not_in_exists (L ++ ty_atoms T ++ tm_ty_atoms t ++ Delta)) as [X HX].
      assert (HXL : ~ In X L) by (intro q; apply HX; simpl; tauto).
      assert (HXT : ~ In X (ty_atoms T)) by (intro q; apply HX; simpl; tauto).
      assert (HXtm : ~ In X (tm_ty_atoms t)) by (intro q; apply HX; simpl; tauto).
      assert (HXD : ~ In X Delta) by (intro q; apply HX; simpl; tauto).
      assert (Hbodyty : has_type (X :: Delta) Gamma
        (open_tm_ty t (Ty_FVar X)) (open_ty T (Ty_FVar X))) by (apply H; exact HXL).
      assert (HlcT : lc_ty_at 1 T).
      { eapply lc_ty_open_inv_rec. eapply wf_ty_lc. eapply has_type_wf; exact Hbodyty. }
      pose proof (IH X HXL (theta_update theta X U) eta
        (relation_update rho X a) gamma
        (theta_closed_update theta X U Htheta HU)
        (env_wf_update Delta rho X a Henv HXD) Hrel Hgamma) as Hb.
      rewrite instantiate_open_tm_ty by assumption in Hb.
      eapply (expression_lifting_ext
        (value_relation eta (relation_update rho X a)
          (open_ty T (Ty_FVar X)))
        (value_relation (a :: eta) rho T)
        (open_tm_ty (instantiate theta gamma t) U)).1.
      * intro z. eapply value_relation_open_rec; eauto.
      * exact Hb.
  - simpl. eapply expression_tapp_semantic; eauto using wf_ty_lc, lc_ty_instantiate.
  - simpl. eapply expression_value. simpl; tauto.
  - simpl. eapply expression_value. simpl; tauto.
  - simpl. eapply expression_if; eauto.
  - simpl. eapply expression_choice; eauto.
Qed.

Lemma tm_atoms_open_in : forall x t y,
    ~ In x (tm_atoms t) -> In y (tm_atoms t) ->
    In y (tm_atoms (open_tm t (tm_fvar x))).
Proof.
  intros x t. unfold open_tm. revert x.
  induction t as [i|z|T t IH|t1 IH1 t2 IH2|t IH|t IH| | |
                   t1 IH1 t2 IH2 t3 IH3|t1 IH1 t2 IH2];
    intros x y Hx Hy; simpl in *; try contradiction.
  - destruct (Nat.eqb 0 i); simpl in *; intuition.
  - destruct (in_app_or Hy) as [Hy|Hy]; [left; eapply IH1|right; eapply IH2];
      eauto using in_or_app.
  - eapply IH; eauto.
  - eapply IH; eauto.
  - destruct (in_app_or Hy) as [Hy|Hy].
    + left; eapply IH1; eauto using in_or_app.
    + destruct (in_app_or Hy) as [Hy|Hy].
      * right; left; eapply IH2; eauto using in_or_app.
      * right; right; eapply IH3; eauto using in_or_app.
  - destruct (in_app_or Hy) as [Hy|Hy]; [left; eapply IH1|right; eapply IH2];
      eauto using in_or_app.
Qed.

Lemma lookup_update_inv : forall Gamma x T y U,
    lookup_context y (update Gamma x T) = Some U ->
    y = x /\ U = T \/ lookup_context y Gamma = Some U.
Proof.
  intros Gamma x T y U H. simpl in H. destruct (Nat.eqb y x) eqn:E.
  - left. split; [apply Nat.eqb_eq in E; assumption|inversion H; reflexivity].
  - right. assumption.
Qed.

Lemma has_type_fvar_context : forall Delta Gamma t T y,
    has_type Delta Gamma t T -> In y (tm_atoms t) ->
    exists U, lookup_context y Gamma = Some U.
Proof.
  intros Delta Gamma t T y H. induction H; simpl in *.
  - exists T; assumption.
  - destruct (not_in_exists (L ++ tm_atoms t2)) as [x Hx].
    assert (HxL : ~ In x L) by (intro q; apply Hx; simpl; tauto).
    assert (Hxt : ~ In x (tm_atoms t2)) by (intro q; apply Hx; simpl; tauto).
    eapply IH; eauto using tm_atoms_open_in.
    destruct (lookup_update_inv Gamma x T1 y U H0) as [[-> ->]|Hold].
    + exists T1; reflexivity.
    + exists U; exact Hold.
  - destruct (in_app_or H) as [H|H].
    + eapply IH1; eauto.
    + eapply IH2; eauto.
  - destruct (not_in_exists (L ++ tm_atoms t)) as [x Hx].
    assert (HxL : ~ In x L) by (intro q; apply Hx; simpl; tauto).
    eapply IH; eauto.
  - eapply IH; eauto.
  - eapply IH; eauto.
  - eapply IH; eauto.
  - eapply IH; eauto.
  - destruct (in_app_or H) as [H|H].
    + eapply IH1; eauto.
    + destruct (in_app_or H) as [H|H].
      * eapply IH2; eauto.
      * eapply IH3; eauto.
  - destruct (in_app_or H) as [H|H].
    + eapply IH1; eauto.
    + eapply IH2; eauto.
Qed.

Lemma term_inst_no_atoms : forall gamma t,
    tm_atoms t = [] -> term_inst gamma t = t.
Proof.
  intros gamma t. induction t; simpl in *; try reflexivity.
  - destruct (tm_atoms t) eqn:E; simpl in *; subst; f_equal; eauto.
  - destruct (tm_atoms t1) eqn:E1, (tm_atoms t2) eqn:E2; simpl in *; subst; f_equal; eauto.
  - destruct (tm_atoms t) eqn:E; simpl in *; subst; f_equal; eauto.
  - destruct (tm_atoms t) eqn:E; simpl in *; subst; f_equal; eauto.
  - destruct (tm_atoms t1) eqn:E1, (tm_atoms t2) eqn:E2, (tm_atoms t3) eqn:E3;
      simpl in *; subst; f_equal; eauto.
  - destruct (tm_atoms t1) eqn:E1, (tm_atoms t2) eqn:E2; simpl in *; subst; f_equal; eauto.
Qed.

Lemma has_type_empty_no_atoms : forall t T,
    has_type [] empty t T -> tm_atoms t = [].
Proof.
  intros t T H. apply nil_eq. intros y Hy.
  destruct (has_type_fvar_context [] empty t T y H Hy) as [U HU]. inversion HU.
Qed.

Lemma instantiate_ty_id : forall T,
    instantiate_ty (fun X => Ty_FVar X) T = T.
Proof.
  induction T; simpl; try reflexivity; f_equal; eauto.
Qed.

Lemma instantiate_id_no_atoms : forall gamma t,
    tm_atoms t = [] ->
    instantiate (fun X => Ty_FVar X) gamma t = t.
Proof.
  intros gamma t. induction t; simpl in *; try reflexivity.
  - destruct (tm_atoms t) eqn:E; simpl in *; subst; rewrite instantiate_ty_id; f_equal; eauto.
  - destruct (tm_atoms t1) eqn:E1, (tm_atoms t2) eqn:E2; simpl in *; subst; f_equal; eauto.
  - destruct (tm_atoms t) eqn:E; simpl in *; subst; f_equal; eauto.
  - destruct (tm_atoms t) eqn:E; simpl in *; subst; rewrite instantiate_ty_id; f_equal; eauto.
  - destruct (tm_atoms t1) eqn:E1, (tm_atoms t2) eqn:E2, (tm_atoms t3) eqn:E3;
      simpl in *; subst; f_equal; eauto.
  - destruct (tm_atoms t1) eqn:E1, (tm_atoms t2) eqn:E2; simpl in *; subst; f_equal; eauto.
Qed.


Lemma lc_ty_open_inv_rec : forall k U T,
    lc_ty_at k (open_ty_rec k U T) -> lc_ty_at (S k) T.
Proof.
  intros k U T. revert k U.
  induction T as [i|X|T1 IH1 T2 IH2|T IH|];
    intros k U H; simpl in *; inversion H; subst; eauto.
  - destruct (Nat.eqb k i) eqn:E.
    + apply lc_ty_bvar. apply Nat.eqb_eq in E. lia.
    + apply lc_ty_bvar. apply Nat.eqb_neq in E. lia.
  - apply lc_ty_all. apply IH; eauto.
Qed.

Lemma lc_tm_open_inv_rec : forall K k u t,
    lc_tm_at K k (open_tm_rec k u t) -> lc_tm_at K (S k) t.
Proof.
  intros K k u t. revert K k u.
  induction t as [i|x|T t IH|t1 IH1 t2 IH2|t IH|t IH| | |
                   t1 IH1 t2 IH2 t3 IH3|t1 IH1 t2 IH2];
    intros K k u H; simpl in *; inversion H; subst; eauto.
  - destruct (Nat.eqb k i) eqn:E; apply lc_tm_bvar.
    + apply Nat.eqb_eq in E. lia.
    + apply Nat.eqb_neq in E. lia.
  - apply lc_tm_abs; eauto. apply IH; eauto.
  - apply lc_tm_tabs. apply IH; eauto using lc_tm_weaken_ty.
Qed.

Lemma lc_tm_ty_open_inv_rec : forall K k U t,
    lc_tm_at K k (open_tm_ty_rec K U t) -> lc_tm_at (S K) k t.
Proof.
  intros K k U t. revert K k U.
  induction t as [i|x|T t IH|t1 IH1 t2 IH2|t IH|t IH| | |
                   t1 IH1 t2 IH2 t3 IH3|t1 IH1 t2 IH2];
    intros K k U H; simpl in *; inversion H; subst; eauto.
  - apply lc_tm_abs.
    + eapply lc_ty_open_inv_rec; eauto.
    + apply IH; eauto.
  - apply lc_tm_tabs. apply IH; eauto using lc_ty_weaken_ty.
  - apply lc_tm_tapp.
    + apply IH; eauto.
    + eapply lc_ty_open_inv_rec; eauto.
Qed.

Lemma lc_open_tm_inv : forall t x,
    locally_closed_tm (open_tm t (tm_fvar x)) -> lc_tm_at 0 1 t.
Proof. intros; unfold locally_closed_tm, open_tm in H; eapply lc_tm_open_inv_rec; eauto. Qed.

Lemma lc_open_tm_ty_inv : forall t X,
    locally_closed_tm (open_tm_ty t (Ty_FVar X)) -> lc_tm_at 1 0 t.
Proof. intros; unfold locally_closed_tm, open_tm_ty in H; eapply lc_tm_ty_open_inv_rec; eauto. Qed.

Lemma has_type_lc : forall Delta Gamma t T,
    has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T H. induction H; unfold locally_closed_tm in *; eauto.
  - apply lc_tm_abs; eauto. destruct (not_in_exists L) as [x Hx].
    eapply lc_open_tm_inv. eapply IH; eauto.
  - apply lc_tm_tabs. destruct (not_in_exists L) as [X HX].
    eapply lc_open_tm_ty_inv. eapply IH; eauto.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H. induction H; unfold locally_closed_ty; eauto.
Qed.

Definition env_wf (Delta : ty_context) (rho : relation_env) : Prop :=
  forall X, In X Delta -> exists a, rho X = Some a.

Lemma env_wf_update : forall Delta rho X a,
    env_wf Delta rho -> ~ In X Delta ->
    env_wf (X :: Delta) (relation_update rho X a).
Proof.
  intros Delta rho X a Hw Hfresh Y HY.
  simpl in HY. destruct HY as [<-|HY].
  - exists a. unfold relation_update. rewrite Nat.eqb_refl. reflexivity.
  - destruct (Hw Y HY) as [b Hb]. exists b. unfold relation_update.
    destruct (Nat.eqb X Y) eqn:E; auto.
    apply Nat.eqb_neq in E. rewrite E. assumption.
Qed.

Lemma related_update : forall rho Gamma gamma x T arg,
    ~ In x (tm_atoms_ctx Gamma) ->
    related_substitution rho Gamma gamma ->
    value_relation [] rho T arg ->
    related_substitution rho (update Gamma x T) (update gamma x arg).
Proof.
  intros rho Gamma gamma x T arg Hfresh Hrel Harg y U Hlook.
  unfold update in Hlook. simpl in Hlook.
  destruct (Nat.eqb y x) eqn:E.
  - inversion Hlook; subst. exact Harg.
  - apply Hrel. apply Hlook.
Qed.

Lemma has_type_wf : forall Delta Gamma t T,
    has_type Delta Gamma t T -> wf_ty Delta T.
Proof.
  intros Delta Gamma t T H. induction H; eauto.
  - apply WF_Arrow; eauto.
  - apply WF_All with (L := L). intros X HX. eauto.
Qed.

Lemma sn_app_right : forall T body t2,
    strongly_normalizing t2 ->
    (forall v, t2 -->* v -> value v ->
      strongly_normalizing (open_tm body v)) ->
    strongly_normalizing (tm_app (tm_abs T body) t2).
Proof.
  intros T body t2 Hsn. revert body.
  induction Hsn as [t2 Hred IH]; intros body Hgood.
  constructor. intros u Hu. inversion Hu; subst.
  - eapply Hgood; [constructor|assumption].
  - exfalso. eapply value_no_step; eauto.
  - eapply IH. intros v Hv Hval. eapply Hgood; eauto using multi_step_l.
Qed.

Lemma sn_app : forall t1 t2,
    strongly_normalizing t1 -> strongly_normalizing t2 ->
    (forall v, t1 -->* v -> value v ->
      exists T body, v = tm_abs T body /\
        forall w, t2 -->* w -> value w ->
          strongly_normalizing (open_tm body w)) ->
    strongly_normalizing (tm_app t1 t2).
Proof.
  intros t1 t2 H1 H2. revert t2.
  induction H1 as [t1 Hred IH]; intros t2 H2 Hgood.
  constructor. intros u Hu. inversion Hu; subst.
  - apply IH with (t2 := t2) H2.
    intros v Hv Hval. eapply Hgood; eauto using multi_step_l.
  - destruct (Hgood t1 (multi_refl _) H) as [T [body [Heq Hb]]].
    subst t1. eapply sn_app_right; eauto.
  - exfalso. eapply value_no_step; eauto.
Qed.

Lemma sn_tapp : forall t U,
    locally_closed_ty U -> strongly_normalizing t ->
    (forall v, t -->* v -> value v ->
      exists body, v = tm_tabs body /\
        strongly_normalizing (open_tm_ty body U)) ->
    strongly_normalizing (tm_tapp t U).
Proof.
  intros t U HU Hsn. revert U HU.
  induction Hsn as [t Hred IH]; intros U HU Hgood.
  constructor. intros u Hu. inversion Hu; subst.
  - destruct (Hgood (multi_refl _) H) as [body [Heq Hbody]]. subst. exact Hbody.
  - apply IH; eauto. intros v Hv Hval. eapply Hgood; eauto using multi_step_l.
Qed.

Lemma sn_if : forall c t1 t2,
    strongly_normalizing c -> strongly_normalizing t1 ->
    strongly_normalizing t2 -> strongly_normalizing (tm_if c t1 t2).
Proof.
  intros c t1 t2 Hc H1 H2. revert t1 t2 H1 H2.
  induction Hc as [c Hred IH]; intros t1 t2 H1 H2.
  constructor. intros u Hu. inversion Hu; subst; eauto.
Qed.

Lemma sn_choice : forall t1 t2,
    strongly_normalizing t1 -> strongly_normalizing t2 ->
    strongly_normalizing (tm_choice t1 t2).
Proof.
  intros t1 t2 H1 H2. constructor. intros u Hu. inversion Hu; eauto.
Qed.

Lemma terminal_app : forall eta rho T1 T2 t1 t2 v,
    expression_lifting (value_relation eta rho (Ty_Arrow T1 T2)) t1 ->
    expression_lifting (value_relation eta rho T1) t2 ->
    tm_app t1 t2 -->* v -> value v ->
    value_relation eta rho T2 v.
Proof.
  intros eta rho T1 T2 t1 t2 v H1 H2 Hm. revert t1 t2 H1 H2.
  induction Hm as [x|x y z Hs Hrest IH]; intros t1 t2 H1 H2 Hv.
  - inversion Hv.
  - inversion Hs; subst.
    + destruct (proj2 (proj2 H1) _ (multi_refl _) H)
        as [U [body [Heq Hbody]]]. subst t1.
      destruct (proj2 (proj2 H2) _ (multi_refl _) H0) as [Hlc [Hsn Hterm]].
      eapply Hbody. eapply Hterm; eauto.
    + eapply IH; eauto using expression_lifting_step.
    + eapply IH; eauto using expression_lifting_step.
Qed.

Lemma terminal_tapp : forall R S t U v,
    expression_lifting R t ->
    locally_closed_ty U ->
    (forall z, R z ->
      exists body, z = tm_tabs body /\
        expression_lifting S
          (open_tm_ty body U)) ->
    tm_tapp t U -->* v -> value v ->
    S v.
Proof.
  intros R S t U v Ht HU Hgood Hm. revert t Ht Hgood.
  induction Hm as [x|x y z Hs Hrest IH]; intros t Ht Hgood Hv.
  - inversion Hv.
  - inversion Hs; subst.
    + destruct (Hgood t (proj2 (proj2 Ht) _ (multi_refl _) H))
        as [body [Heq Hbody]]. subst. eapply (proj2 (proj2 Hbody) v Hrest Hv).
    + eapply IH; eauto using expression_lifting_step.
      intros z Hz. eapply Hgood; eauto using multi_step_l.
Qed.

Lemma terminal_if : forall C R c t1 t2 v,
    expression_lifting C c ->
    expression_lifting R t1 ->
    expression_lifting R t2 ->
    (tm_if c t1 t2 -->* v) -> value v ->
    R v.
Proof.
  intros C R c t1 t2 v Hc H1 H2 Hm. revert c t1 t2 Hc H1 H2.
  induction Hm as [x|x y z Hs Hrest IH]; intros c t1 t2 Hc H1 H2 Hv.
  - inversion Hv.
  - inversion Hs; subst.
    + eapply (proj2 (proj2 H1) v Hrest Hv).
    + eapply (proj2 (proj2 H2) v Hrest Hv).
    + eapply IH; eauto using expression_lifting_step.
Qed.

Lemma terminal_choice : forall R t1 t2 v,
    expression_lifting R t1 ->
    expression_lifting R t2 ->
    tm_choice t1 t2 -->* v -> value v ->
    R v.
Proof.
  intros R t1 t2 v H1 H2 Hm. inversion Hm; subst.
  - inversion H0.
  - inversion H; subst.
    + eapply (proj2 (proj2 H1) v H2 H0).
    + eapply (proj2 (proj2 H2) v H1 H0).
Qed.

Lemma expression_app : forall eta rho T1 T2 t1 t2,
    expression_relation eta rho (Ty_Arrow T1 T2) t1 ->
    expression_relation eta rho T1 t2 ->
    expression_relation eta rho T2 (tm_app t1 t2).
Proof.
  intros eta rho T1 T2 t1 t2 H1 H2.
  unfold expression_relation in *.
  destruct H1 as [L1 [N1 F1]]. destruct H2 as [L2 [N2 F2]].
  repeat split.
  - constructor; assumption.
  - apply sn_app; try assumption.
    intros v Hv Hval.
    destruct (F1 v Hv Hval) as [U [body [Heq Hrel]]].
    destruct Hrel as [HbLc [HbSn HbTerm]].
    exists U, body. split; [assumption|].
    intros w Hw Hwval. eapply HbSn.
  - eapply terminal_app; eauto.
Qed.

Lemma expression_tapp : forall eta rho T U t S,
    expression_relation eta rho (Ty_All T) t ->
    locally_closed_ty U ->
    (forall v, value_relation eta rho (Ty_All T) v ->
      exists body, v = tm_tabs body /\
        expression_lifting S (open_tm_ty body U)) ->
    expression_relation eta rho S (tm_tapp t U).
Proof.
  intros eta rho T U t S Ht HU Hgood. unfold expression_relation in *.
  destruct Ht as [L [N F]]. repeat split.
  - constructor; assumption.
  - apply sn_tapp; assumption.
    intros v Hv Hvval. eapply Hgood; eapply F; eauto.
  - eapply terminal_tapp; eauto.
Qed.

Lemma expression_if : forall eta rho T c t1 t2,
    expression_relation eta rho Ty_Bool c ->
    expression_relation eta rho T t1 ->
    expression_relation eta rho T t2 ->
    expression_relation eta rho T (tm_if c t1 t2).
Proof.
  intros eta rho T c t1 t2 Hc H1 H2. unfold expression_relation in *.
  destruct Hc as [Lc Nc Fc]. destruct H1 as [L1 N1 F1]. destruct H2 as [L2 N2 F2].
  repeat split.
  - constructor; assumption.
  - eapply sn_if; eauto.
  - eapply terminal_if; eauto.
Qed.

Lemma expression_choice : forall eta rho T t1 t2,
    expression_relation eta rho T t1 ->
    expression_relation eta rho T t2 ->
    expression_relation eta rho T (tm_choice t1 t2).
Proof.
  intros eta rho T t1 t2 H1 H2. unfold expression_relation in *.
  destruct H1 as [L1 N1 F1]. destruct H2 as [L2 N2 F2].
  repeat split.
  - constructor; assumption.
  - eapply sn_choice; eauto.
  - eapply terminal_choice; eauto.
Qed.

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  intros t T Ht.
  pose proof (fundamental [] empty t T Ht
    (fun X => Ty_FVar X) [] (fun _ => None) (fun _ => tm_true)
    (fun X => lc_ty_fvar 0 X)
    (fun X HX => contradiction)
    (fun x U H => contradiction)
    (fun x => lc_tm_true 0 0)) as Hfund.
  rewrite (instantiate_id_no_atoms (fun _ => tm_true) t
    (has_type_empty_no_atoms t T Ht)) in Hfund.
  exact (proj2 (proj2 Hfund)).
Qed.

End SystemFNormalizationIfNondeterminismMediumTask.
