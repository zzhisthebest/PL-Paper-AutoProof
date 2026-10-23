(** System F CBV strong-normalization benchmark, Medium variant.
    Features: recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFNormalizationRecursionMediumTask.

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
  | Ty_Nat => Ty_Nat
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
  | tm_zero => tm_zero
  | tm_succ t => tm_succ (instantiate theta gamma t)
  | tm_natrec n b s => tm_natrec (instantiate theta gamma n) (instantiate theta gamma b) (instantiate theta gamma s)
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
  | Ty_Nat => value v /\ numeric_value v
  end.

Definition expression_relation eta rho T t :=
  expression_lifting (value_relation eta rho T) t.

Definition related_substitution (rho : relation_env) (Gamma : context)
    (gamma : term_substitution) : Prop :=
  forall x T, lookup_context x Gamma = Some T -> value_relation [] rho T (gamma x).

Lemma multi_trans : forall t u v, t -->* u -> u -->* v -> t -->* v.
Proof.
  intros t u v H; induction H; eauto using multi.
Qed.

Lemma value_no_step : forall v u, value v -> v --> u -> False.
Proof.
  intros v u Hv Hs; induction Hs; inversion Hv; subst;
    repeat match goal with
      | H : numeric_value (tm_app _ _) |- _ => inversion H
      | H : numeric_value (tm_tapp _ _) |- _ => inversion H
      | H : numeric_value (tm_natrec _ _ _) |- _ => inversion H
      | H : numeric_value (tm_succ _) |- _ => inversion H; clear H; subst
    end; eauto.
Qed.

Lemma value_multi : forall v w, value v -> v -->* w -> v = w.
Proof.
  intros v w Hv H; inversion H; subst; auto.
  exfalso; eapply value_no_step; eauto.
Qed.

Lemma lc_ty_weaken : forall k T, lc_ty_at k T ->
  forall j, k <= j -> lc_ty_at j T.
Proof.
  intros k T H; induction H; intros j Hj.
  - constructor; lia.
  - constructor.
  - constructor; eauto.
  - apply lc_ty_all. apply IHlc_ty_at. lia.
  - constructor.
Qed.

Lemma lc_tm_weaken : forall K k t, lc_tm_at K k t ->
  forall J j, K <= J -> k <= j -> lc_tm_at J j t.
Proof.
  intros K k t H; induction H; intros J j HJ Hj;
    econstructor; eauto using lc_ty_weaken; try lia;
    match goal with
    | H : forall J j, _ -> _ -> lc_tm_at J j ?t |- lc_tm_at ?J ?j ?t =>
        eapply H; lia
    end.
Qed.

Lemma lc_ty_open_rec : forall k T U, lc_ty_at k T ->
  open_ty_rec k U T = T.
Proof.
  intros k T U H; induction H; simpl; try (f_equal; eauto).
  destruct (Nat.eqb k i) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
Qed.

Lemma lc_tm_open_rec : forall K k t u,
  lc_tm_at K k t -> open_tm_rec k u t = t.
Proof.
  intros K k t u H; induction H; simpl; try (f_equal; eauto).
  destruct (Nat.eqb k i) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
Qed.

Lemma lc_tm_ty_open_rec : forall K k t U,
  lc_tm_at K k t -> open_tm_ty_rec K U t = t.
Proof.
  intros K k t U H; induction H; simpl; f_equal; eauto using lc_ty_open_rec.
Qed.

Lemma lc_ty_open_preserve : forall K T,
  lc_ty_at (S K) T -> forall U, lc_ty_at K U ->
  lc_ty_at K (open_ty_rec K U T).
Proof.
  intros K T H; remember (S K) as J eqn:E.
  revert K E; induction H; intros J EJ U HU; subst; simpl.
  - destruct (Nat.eqb J i) eqn:Ei; auto.
    apply lc_ty_bvar. apply Nat.eqb_neq in Ei. lia.
  - constructor.
  - constructor; eauto.
  - constructor. eapply IHlc_ty_at; eauto using lc_ty_weaken; lia.
  - constructor.
Qed.

Lemma lc_tm_open_preserve : forall K k t,
  lc_tm_at K (S k) t -> forall u, lc_tm_at K k u ->
  lc_tm_at K k (open_tm_rec k u t).
Proof.
  intros K k t H; remember (S k) as j eqn:E.
  revert k E; induction H; intros j Ej u Hu; subst; simpl.
  - destruct (Nat.eqb j i) eqn:Ei; auto.
    apply lc_tm_bvar. apply Nat.eqb_neq in Ei. lia.
  - constructor.
  - constructor; auto. eapply IHlc_tm_at; eauto using lc_tm_weaken; lia.
  - constructor; eauto.
  - constructor. eapply IHlc_tm_at; eauto using lc_tm_weaken; lia.
  - constructor; eauto.
  - constructor.
  - constructor; eauto.
  - constructor; eauto.
Qed.

Lemma lc_tm_ty_open_preserve : forall K k t,
  lc_tm_at (S K) k t -> forall U, lc_ty_at K U ->
  lc_tm_at K k (open_tm_ty_rec K U t).
Proof.
  intros K k t H; remember (S K) as J eqn:E.
  revert K E; induction H; intros J EJ U HU; subst; simpl.
  - constructor; auto.
  - constructor.
  - constructor; eauto using lc_ty_open_preserve.
  - constructor; eauto.
  - constructor. eapply IHlc_tm_at; eauto using lc_ty_weaken; lia.
  - constructor; eauto using lc_ty_open_preserve.
  - constructor.
  - constructor; eauto.
  - constructor; eauto.
Qed.

Lemma numeric_lc : forall n, numeric_value n -> locally_closed_tm n.
Proof.
  intros n H; induction H; constructor; auto.
Qed.

Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof.
  intros v H; inversion H; subst; auto using numeric_lc.
Qed.

Lemma value_relation_value : forall eta rho T v,
  value_relation eta rho T v -> value v.
Proof.
  induction T; simpl; intros v H;
    try (destruct (nth_error eta n) as [a|]; [eapply candidate_values|contradiction]; eauto);
    try (destruct (rho a) as [c|]; [eapply candidate_values|contradiction]; eauto);
    tauto.
Qed.

Lemma expression_value : forall eta rho T v,
  value_relation eta rho T v -> expression_relation eta rho T v.
Proof.
  intros eta rho T v H.
  unfold expression_relation, expression_lifting.
  split; [eapply value_lc, value_relation_value; eauto|].
  split; [constructor; intros u Hu; exfalso; eapply value_no_step; eauto using value_relation_value|].
  intros w Hw Hvw; rewrite <- (value_multi _ _ (value_relation_value _ _ _ _ H) Hw); exact H.
Qed.

Lemma step_lc : forall t u, t --> u -> locally_closed_tm t -> locally_closed_tm u.
Proof.
  intros t u Hstep; induction Hstep; intros Hlc; inversion Hlc; subst;
    repeat match goal with
      | H : lc_tm_at _ _ (tm_abs _ _) |- _ => inversion H; subst; clear H
      | H : lc_tm_at _ _ (tm_tabs _) |- _ => inversion H; subst; clear H
    end;
    unfold locally_closed_tm, open_tm, open_tm_ty in *;
    eauto 12 using lc_tm_open_preserve, lc_tm_ty_open_preserve,
      value_lc, numeric_lc, lc_tm_at.
  apply lc_tm_app.
  - apply lc_tm_app; auto. change (locally_closed_tm n). now apply numeric_lc.
  - apply lc_tm_rec; auto. change (locally_closed_tm n). now apply numeric_lc.
Qed.

Lemma expression_step : forall R t u,
  expression_lifting R t -> t --> u -> expression_lifting R u.
Proof.
  intros R t u [Hlc [Hsn Hr]] Hstep; split.
  - eauto using step_lc.
  - split.
    + inversion Hsn; subst; eauto.
    + intros v Hmulti Hv; apply Hr; eauto using multi_step.
Qed.

Lemma expression_intro : forall R t,
  locally_closed_tm t ->
  (forall u, t --> u -> expression_lifting R u) ->
  (value t -> R t) -> expression_lifting R t.
Proof.
  intros R t Hlc Hsteps Hvalue; unfold expression_lifting.
  split; [exact Hlc|]. split.
  - constructor; intros u Hu; exact (proj1 (proj2 (Hsteps u Hu))).
  - intros v Hmulti Hv; inversion Hmulti; subst; auto.
    eapply (proj2 (proj2 (Hsteps y H))); eauto.
Qed.

Lemma expression_app : forall eta rho A B f a,
  expression_relation eta rho (Ty_Arrow A B) f ->
  expression_relation eta rho A a ->
  expression_relation eta rho B (tm_app f a).
Proof.
  intros eta rho A B f a Hf Ha.
  unfold expression_relation in *.
  destruct Hf as [Hlf [Hsf Hrf]].
  revert a Ha; induction Hsf as [f Hsf IHf]; intros a Ha.
  destruct Ha as [Hla [Hsa Hra]].
  induction Hsa as [a Hsa IHa].
  eapply expression_intro.
  - constructor; assumption.
  - intros u Hu; inversion Hu; subst.
    + specialize (Hrf (tm_abs T t) (multi_refl _) (v_abs _ _ H1)).
      simpl in Hrf. destruct Hrf as [_ [U [body [Heq Hbody]]]].
      inversion Heq; subst.
      apply Hbody. apply Hra; eauto using multi_refl.
    + eapply IHf; eauto using step_lc.
      * intros v Hv Hvalue; apply Hrf; eauto using multi_step.
      * split; [exact Hla|]. split; [constructor; exact Hsa|exact Hra].
    + eapply IHa; eauto using step_lc.
      intros v Hv Hvalue; apply Hra; eauto using multi_step.
  - intros Hv; exfalso; inversion Hv; subst;
      repeat match goal with
      | H : numeric_value (tm_app _ _) |- _ => inversion H
      end.
Qed.

Lemma expression_succ : forall eta rho t,
  expression_relation eta rho Ty_Nat t ->
  expression_relation eta rho Ty_Nat (tm_succ t).
Proof.
  intros eta rho t [Hlc [Hsn Hr]].
  induction Hsn as [t Hsn IH].
  eapply expression_intro.
  - constructor; exact Hlc.
  - intros u Hu; inversion Hu; subst.
    apply IH; eauto using step_lc.
    intros v Hv Hvalue; apply Hr; eauto using multi_step.
  - intros Hv; inversion Hv; subst. simpl; auto.
Qed.

Fixpoint numeric_value_dec (t : tm) : {numeric_value t} + {~ numeric_value t}.
Proof.
  destruct t; try (right; intro H; inversion H; fail).
  - left; constructor.
  - destruct (numeric_value_dec t) as [H|H].
    + left; constructor; exact H.
    + right; intro Hnv; inversion Hnv; subst; contradiction.
Defined.

Lemma expression_rec_numeric : forall eta rho T n,
  numeric_value n -> forall b s,
  expression_relation eta rho T b ->
  expression_relation eta rho (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  expression_relation eta rho T (tm_natrec n b s).
Proof.
  intros eta rho T n Hn; induction Hn as [|n Hn IHn]; intros b s Hb Hs.
  all: destruct Hb as [Hlb [Hsb Hrb]];
    revert s Hs; induction Hsb as [b Hsb IHb]; intros s Hs;
    destruct Hs as [Hls [Hss Hrs]];
    induction Hss as [s Hss IHs];
    eapply expression_intro.
  - apply lc_tm_rec; eauto using numeric_lc, nv_zero.
  - intros u Hu; inversion Hu; subst;
      try solve [exfalso; eapply value_no_step; [eauto using v_nat, nv_zero, nv_succ | eassumption]].
    + apply IHb; eauto using step_lc.
      intros v Hv Hvalue; apply Hrb; eauto using multi_step.
      split; [exact Hls|]. split; [constructor; exact Hss|exact Hrs].
    + apply IHs; eauto using step_lc.
      intros v Hv Hvalue; apply Hrs; eauto using multi_step.
    + split; [exact Hlb|]. split; [constructor; exact Hsb|exact Hrb].
  - intros Hv; inversion Hv; subst; inversion H.
  - apply lc_tm_rec; eauto using numeric_lc, nv_succ, nv_zero.
    change (locally_closed_tm (tm_succ n)). apply numeric_lc.
    constructor; assumption.
  - intros u Hu; inversion Hu; subst;
      try solve [exfalso; eapply value_no_step; [eauto using v_nat, nv_zero, nv_succ | eassumption]].
    + exfalso. eapply value_no_step; [apply v_nat; constructor; exact Hn|eassumption].
    + apply IHb; eauto using step_lc.
      intros v Hv Hvalue; apply Hrb; eauto using multi_step.
      split; [exact Hls|]. split; [constructor; exact Hss|exact Hrs].
    + apply IHs; eauto using step_lc.
      intros v Hv Hvalue; apply Hrs; eauto using multi_step.
    + eapply expression_app.
      * eapply expression_app.
        -- split; [exact Hls|]. split; [constructor; exact Hss|exact Hrs].
        -- apply expression_value. simpl; split; [constructor; exact Hn|exact Hn].
      * apply IHn; [|].
        -- split; [exact Hlb|]. split; [constructor; exact Hsb|exact Hrb].
        -- split; [exact Hls|]. split; [constructor; exact Hss|exact Hrs].
  - intros Hv; inversion Hv; subst; inversion H.
Qed.

Lemma expression_rec : forall eta rho T n b s,
  expression_relation eta rho Ty_Nat n ->
  expression_relation eta rho T b ->
  expression_relation eta rho (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  expression_relation eta rho T (tm_natrec n b s).
Proof.
  intros eta rho T n b s [Hln [Hsn Hrn]] Hb Hs.
  induction Hsn as [n Hsn IHn].
  destruct (numeric_value_dec n) as [Hnum|Hnot].
  - apply expression_rec_numeric; auto.
  - eapply expression_intro.
    + apply lc_tm_rec; [exact Hln|exact (proj1 Hb)|exact (proj1 Hs)].
    + intros u Hu; inversion Hu; subst;
        try solve [exfalso; apply Hnot; eassumption | exfalso; apply Hnot; constructor; eassumption | exfalso; apply Hnot; constructor].
      apply IHn; eauto using step_lc.
      intros v Hv Hvalue; apply Hrn; eauto using multi_step.
    + intros Hv; exfalso; inversion Hv; subst; inversion H.
Qed.

Lemma list_max_bound : forall L x, In x L -> x <= fold_right Nat.max 0 L.
Proof.
  induction L as [|a L IH]; simpl; intros x Hin.
  - contradiction.
  - destruct Hin as [Heq|Hin]; subst; [lia|].
    specialize (IH x Hin); lia.
Qed.

Lemma fresh_exists : forall L : list atom, exists x, ~ In x L.
Proof.
  intro L. exists (S (fold_right Nat.max 0 L)).
  intro Hin. pose proof (list_max_bound L _ Hin). lia.
Qed.

Lemma lc_ty_open_inverse : forall K T X,
  lc_ty_at K (open_ty_rec K (Ty_FVar X) T) -> lc_ty_at (S K) T.
Proof.
  intros K T; revert K; induction T; intros K X H; simpl in *.
  - destruct (Nat.eqb K n) eqn:E.
    + apply Nat.eqb_eq in E; subst; constructor; lia.
    + inversion H; subst. constructor; lia.
  - constructor.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - constructor.
Qed.

Lemma lc_tm_open_inverse : forall K k t x,
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) ->
  lc_tm_at K (S k) t.
Proof.
  intros K k t; revert K k; induction t; intros K k x H; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst; constructor; lia.
    + inversion H; subst. constructor; lia.
  - constructor.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - constructor.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
Qed.

Lemma lc_tm_ty_open_inverse : forall K k t X,
  lc_tm_at K k (open_tm_ty_rec K (Ty_FVar X) t) ->
  lc_tm_at (S K) k t.
Proof.
  intros K k t; revert K k; induction t; intros K k X H; simpl in *.
  - inversion H; subst; constructor; auto.
  - constructor.
  - inversion H; subst; constructor; eauto using lc_ty_open_inverse.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto using lc_ty_open_inverse.
  - constructor.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H; induction H; try solve [constructor; auto].
  destruct (fresh_exists L) as [X HX].
  specialize (H X HX). specialize (H0 X HX).
  constructor. eapply lc_ty_open_inverse; exact H0.
Qed.

Lemma has_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T H; induction H;
    try solve [constructor; eauto using wf_ty_lc].
  - destruct (fresh_exists L) as [x Hx].
    specialize (H0 x Hx). specialize (H1 x Hx).
    apply lc_tm_abs. eapply wf_ty_lc; exact H.
    eapply lc_tm_open_inverse; exact H1.
  - destruct (fresh_exists L) as [X HX].
    specialize (H X HX). specialize (H0 X HX).
    apply lc_tm_tabs. eapply lc_tm_ty_open_inverse; exact H0.
  - apply lc_tm_tapp; auto. eapply wf_ty_lc; eauto.
Qed.

Lemma instantiate_ty_lc : forall theta K T,
  type_substitution_closed theta -> lc_ty_at K T ->
  lc_ty_at K (instantiate_ty theta T).
Proof.
  intros theta K T Htheta H; induction H; simpl.
  - apply lc_ty_bvar; assumption.
  - eapply lc_ty_weaken; [apply Htheta|lia].
  - constructor; assumption.
  - constructor; assumption.
  - constructor.
Qed.

Lemma instantiate_lc : forall theta gamma K k t,
  type_substitution_closed theta -> term_substitution_closed gamma ->
  lc_tm_at K k t -> lc_tm_at K k (instantiate theta gamma t).
Proof.
  intros theta gamma K k t Htheta Hgamma H; induction H; simpl;
    try solve [constructor; eauto using lc_tm_weaken, instantiate_ty_lc].
  - eapply lc_tm_weaken; [exact (Hgamma x)|lia|lia].
Qed.

Fixpoint free_ty (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow A B => free_ty A ++ free_ty B
  | Ty_All A => free_ty A
  | Ty_Nat => []
  end.

Fixpoint free_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs _ t => free_tm t
  | tm_app f a => free_tm f ++ free_tm a
  | tm_tabs t => free_tm t
  | tm_tapp t _ => free_tm t
  | tm_zero => []
  | tm_succ t => free_tm t
  | tm_natrec n b s => free_tm n ++ free_tm b ++ free_tm s
  end.

Fixpoint free_tm_types (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_fvar _ | tm_zero => []
  | tm_abs T t => free_ty T ++ free_tm_types t
  | tm_app f a => free_tm_types f ++ free_tm_types a
  | tm_tabs t | tm_succ t => free_tm_types t
  | tm_tapp t T => free_tm_types t ++ free_ty T
  | tm_natrec n b s => free_tm_types n ++ free_tm_types b ++ free_tm_types s
  end.

Fixpoint free_context_types (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (_, T) :: Gamma' => free_ty T ++ free_context_types Gamma'
  end.

Definition type_override (theta : type_substitution) X U : type_substitution :=
  fun Y => if Nat.eqb X Y then U else theta Y.

Definition term_override (gamma : term_substitution) x v : term_substitution :=
  fun y => if Nat.eqb x y then v else gamma y.

Lemma type_override_closed : forall theta X U,
  type_substitution_closed theta -> locally_closed_ty U ->
  type_substitution_closed (type_override theta X U).
Proof.
  intros theta X U Htheta HU Y. unfold type_override.
  destruct (Nat.eqb X Y); auto.
Qed.

Lemma term_override_closed : forall gamma x v,
  term_substitution_closed gamma -> locally_closed_tm v ->
  term_substitution_closed (term_override gamma x v).
Proof.
  intros gamma x v Hgamma Hv y. unfold term_override.
  destruct (Nat.eqb x y); auto.
Qed.

Lemma instantiate_ty_open : forall T k theta X U,
  ~ In X (free_ty T) -> type_substitution_closed theta ->
  instantiate_ty (type_override theta X U)
    (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k U (instantiate_ty theta T).
Proof.
  induction T; intros k theta X U HX Htheta; simpl in *.
  - destruct (Nat.eqb k n) eqn:E; simpl; auto.
    unfold type_override. now rewrite Nat.eqb_refl.
  - destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E; subst. tauto.
    + unfold type_override. rewrite E.
      symmetry. apply lc_ty_open_rec.
      eapply lc_ty_weaken; [apply Htheta|lia].
  - rewrite IHT1, IHT2; auto; intro H; apply HX; apply in_or_app; auto.
  - f_equal. apply IHT; auto.
  - reflexivity.
Qed.

Lemma instantiate_tm_open : forall t k theta gamma x arg,
  ~ In x (free_tm t) -> term_substitution_closed gamma ->
  locally_closed_tm arg ->
  instantiate theta (term_override gamma x arg)
    (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k arg (instantiate theta gamma t).
Proof.
  induction t; intros k theta gamma x arg Hx Hgamma Harg; simpl in *.
  - destruct (Nat.eqb k n); simpl; auto.
    unfold term_override. now rewrite Nat.eqb_refl.
  - destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E; subst; tauto.
    + unfold term_override; rewrite E. symmetry.
      eapply lc_tm_open_rec with (K := 0).
      eapply lc_tm_weaken with (K := 0) (k := 0);
        [exact (Hgamma a)|lia|lia].
  - f_equal. apply IHt; auto.
  - f_equal; [apply IHt1|apply IHt2]; auto;
      intro Hin; apply Hx; apply in_or_app; auto.
  - f_equal. apply IHt; auto.
  - f_equal. apply IHt; auto.
  - reflexivity.
  - f_equal. apply IHt; auto.
  - f_equal; [apply IHt1|apply IHt2|apply IHt3]; auto;
      intro Hin; apply Hx; rewrite !in_app_iff in *; tauto.
Qed.

Lemma instantiate_tm_ty_open : forall t K theta gamma X U,
  ~ In X (free_tm_types t) -> type_substitution_closed theta ->
  term_substitution_closed gamma ->
  instantiate (type_override theta X U) gamma
    (open_tm_ty_rec K (Ty_FVar X) t) =
  open_tm_ty_rec K U (instantiate theta gamma t).
Proof.
  induction t; intros K theta gamma X U HX Htheta Hgamma; simpl in *; auto.
  - symmetry. eapply lc_tm_ty_open_rec with (k := 0).
    eapply lc_tm_weaken with (K := 0) (k := 0);
      [exact (Hgamma a)|lia|lia].
  - f_equal.
    + apply instantiate_ty_open; auto. intro H; apply HX; apply in_or_app; auto.
    + apply IHt; auto. intro H; apply HX; apply in_or_app; auto.
  - f_equal; [apply IHt1|apply IHt2]; auto;
      intro H; apply HX; apply in_or_app; auto.
  - f_equal. apply IHt; auto.
  - f_equal.
    + apply IHt; auto. intro H; apply HX; apply in_or_app; auto.
    + apply instantiate_ty_open; auto. intro H; apply HX; apply in_or_app; auto.
  - f_equal. apply IHt; auto.
  - f_equal; [apply IHt1|apply IHt2|apply IHt3]; auto;
      intro H; apply HX; rewrite !in_app_iff in *; tauto.
Qed.

Lemma expression_lifting_iff : forall R S t,
  (forall v, R v <-> S v) ->
  expression_lifting R t <-> expression_lifting S t.
Proof.
  intros R S t H; unfold expression_lifting; firstorder.
Qed.

Lemma value_relation_eta_invariant : forall K T,
  lc_ty_at K T -> forall prefix suffix rho v,
  length prefix = K ->
  value_relation (prefix ++ suffix) rho T v <->
  value_relation prefix rho T v.
Proof.
  intros K T H; induction H; intros prefix suffix rho v Hlen; simpl.
  - rewrite nth_error_app1 by lia. tauto.
  - tauto.
  - split.
    + intros [Hv [U [body [Heq Hbody]]]].
      split; [exact Hv|]. exists U, body. split; [exact Heq|].
      intros arg Harg.
      apply (proj1 (expression_lifting_iff _ _ _
        (fun w => IHlc_ty_at2 prefix suffix rho w Hlen))).
      apply Hbody. apply (proj2 (IHlc_ty_at1 prefix suffix rho arg Hlen)); assumption.
    + intros [Hv [U [body [Heq Hbody]]]].
      split; [exact Hv|]. exists U, body. split; [exact Heq|].
      intros arg Harg.
      apply (proj2 (expression_lifting_iff _ _ _
        (fun w => IHlc_ty_at2 prefix suffix rho w Hlen))).
      apply Hbody. apply (proj1 (IHlc_ty_at1 prefix suffix rho arg Hlen)); assumption.
  - split.
    + intros [Hv [body [Heq Hbody]]].
      split; [exact Hv|]. exists body. split; [exact Heq|].
      intros U a HU.
      apply (proj1 (expression_lifting_iff _ _ _
        (fun w => IHlc_ty_at (a :: prefix) suffix rho w (f_equal S Hlen)))).
      apply Hbody; assumption.
    + intros [Hv [body [Heq Hbody]]].
      split; [exact Hv|]. exists body. split; [exact Heq|].
      intros U a HU.
      apply (proj2 (expression_lifting_iff _ _ _
        (fun w => IHlc_ty_at (a :: prefix) suffix rho w (f_equal S Hlen)))).
      apply Hbody; assumption.
  - tauto.
Qed.

Definition type_candidate (rho : relation_env) (U : ty) : value_candidate :=
  {| candidate_relation := value_relation [] rho U;
     candidate_values := value_relation_value [] rho U |}.

Lemma value_relation_open_free : forall K T,
  lc_ty_at (S K) T -> forall prefix suffix rho X a v,
  length prefix = K -> ~ In X (free_ty T) ->
  value_relation (prefix ++ suffix) (relation_update rho X a)
    (open_ty_rec K (Ty_FVar X) T) v <->
  value_relation (prefix ++ a :: suffix) rho T v.
Proof.
  intros K T H; remember (S K) as J eqn:EJ.
  revert K EJ; induction H;
    intros K EJ prefix suffix rho Y a v Hlen HY; subst k; simpl in *.
  - destruct (Nat.eqb K i) eqn:E.
    + apply Nat.eqb_eq in E; subst.
      rewrite nth_error_app2 by lia.
      rewrite Nat.sub_diag.
      simpl. unfold relation_update. rewrite Nat.eqb_refl. tauto.
    + apply Nat.eqb_neq in E.
      assert (Hi : i < K) by lia.
      simpl. rewrite !nth_error_app1 by lia. tauto.
  - assert (Y <> X) by (intro Heq; subst; apply HY; simpl; auto).
    unfold relation_update. destruct (Nat.eqb Y X) eqn:E;
      [apply Nat.eqb_eq in E; contradiction|tauto].
  - assert (HY1 : ~ In Y (free_ty T1))
      by (intro Hin; apply HY; apply in_or_app; left; exact Hin).
    assert (HY2 : ~ In Y (free_ty T2))
      by (intro Hin; apply HY; apply in_or_app; right; exact Hin).
    split.
    + intros [Hv [U [body [Heq Hbody]]]].
      split; [exact Hv|]. exists U, body. split; [exact Heq|].
      intros arg Harg.
      apply (proj1 (expression_lifting_iff _ _ _
        (fun w => IHlc_ty_at2 K eq_refl prefix suffix rho Y a w Hlen HY2))).
      apply Hbody. apply (proj2 (IHlc_ty_at1 K eq_refl prefix suffix rho Y a arg Hlen HY1)); assumption.
    + intros [Hv [U [body [Heq Hbody]]]].
      split; [exact Hv|]. exists U, body. split; [exact Heq|].
      intros arg Harg.
      apply (proj2 (expression_lifting_iff _ _ _
        (fun w => IHlc_ty_at2 K eq_refl prefix suffix rho Y a w Hlen HY2))).
      apply Hbody. apply (proj1 (IHlc_ty_at1 K eq_refl prefix suffix rho Y a arg Hlen HY1)); assumption.
  - split.
    + intros [Hv [body [Heq Hbody]]].
      split; [exact Hv|]. exists body. split; [exact Heq|].
      intros U c HU.
      apply (proj1 (expression_lifting_iff _ _ _
        (fun w => IHlc_ty_at (S K) eq_refl (c :: prefix) suffix rho Y a w (f_equal S Hlen) HY))).
      apply Hbody; assumption.
    + intros [Hv [body [Heq Hbody]]].
      split; [exact Hv|]. exists body. split; [exact Heq|].
      intros U c HU.
      apply (proj2 (expression_lifting_iff _ _ _
        (fun w => IHlc_ty_at (S K) eq_refl (c :: prefix) suffix rho Y a w (f_equal S Hlen) HY))).
      apply Hbody; assumption.
  - tauto.
Qed.

Lemma value_relation_open_type : forall K T,
  lc_ty_at (S K) T -> forall prefix suffix rho U v,
  length prefix = K -> locally_closed_ty U ->
  value_relation (prefix ++ suffix) rho (open_ty_rec K U T) v <->
  value_relation (prefix ++ type_candidate rho U :: suffix) rho T v.
Proof.
  intros K T H; remember (S K) as J eqn:EJ.
  revert K EJ; induction H;
    intros K EJ prefix suffix rho U v Hlen HU; subst k; simpl in *.
  - destruct (Nat.eqb K i) eqn:E.
    + apply Nat.eqb_eq in E; subst.
      rewrite nth_error_app2 by lia.
      rewrite Nat.sub_diag. simpl.
      unfold type_candidate. simpl.
      change (value_relation ([] ++ (prefix ++ suffix)) rho U v <->
              value_relation [] rho U v).
      apply value_relation_eta_invariant with (K := 0); auto.
    + apply Nat.eqb_neq in E.
      assert (Hi : i < K) by lia.
      simpl. rewrite !nth_error_app1 by lia. tauto.
  - tauto.
  - split.
    + intros [Hv [V [body [Heq Hbody]]]].
      split; [exact Hv|]. exists V, body. split; [exact Heq|].
      intros arg Harg.
      apply (proj1 (expression_lifting_iff _ _ _
        (fun w => IHlc_ty_at2 K eq_refl prefix suffix rho U w Hlen HU))).
      apply Hbody. apply (proj2 (IHlc_ty_at1 K eq_refl prefix suffix rho U arg Hlen HU)); assumption.
    + intros [Hv [V [body [Heq Hbody]]]].
      split; [exact Hv|]. exists V, body. split; [exact Heq|].
      intros arg Harg.
      apply (proj2 (expression_lifting_iff _ _ _
        (fun w => IHlc_ty_at2 K eq_refl prefix suffix rho U w Hlen HU))).
      apply Hbody. apply (proj1 (IHlc_ty_at1 K eq_refl prefix suffix rho U arg Hlen HU)); assumption.
  - split.
    + intros [Hv [body [Heq Hbody]]].
      split; [exact Hv|]. exists body. split; [exact Heq|].
      intros V c HV.
      apply (proj1 (expression_lifting_iff _ _ _
        (fun w => IHlc_ty_at (S K) eq_refl (c :: prefix) suffix rho U w (f_equal S Hlen) HU))).
      apply Hbody; assumption.
    + intros [Hv [body [Heq Hbody]]].
      split; [exact Hv|]. exists body. split; [exact Heq|].
      intros V c HV.
      apply (proj2 (expression_lifting_iff _ _ _
        (fun w => IHlc_ty_at (S K) eq_refl (c :: prefix) suffix rho U w (f_equal S Hlen) HU))).
      apply Hbody; assumption.
  - tauto.
Qed.

Lemma has_type_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_ty T.
Proof.
  intros Delta Gamma t T H; induction H; simpl.
  - eapply wf_ty_lc; exact H0.
  - constructor; [eapply wf_ty_lc; exact H|].
    destruct (fresh_exists L) as [x Hx]. exact (H1 x Hx).
  - inversion IHhas_type1; subst; assumption.
  - destruct (fresh_exists L) as [X HX].
    specialize (H0 X HX).
    constructor. eapply lc_ty_open_inverse; exact H0.
  - inversion IHhas_type; subst.
    eapply lc_ty_open_preserve; [eassumption|eapply wf_ty_lc; exact H0].
  - constructor.
  - constructor.
  - exact IHhas_type2.
Qed.

Lemma value_relation_rho_fresh : forall T eta rho X a v,
  ~ In X (free_ty T) ->
  value_relation eta (relation_update rho X a) T v <->
  value_relation eta rho T v.
Proof.
  induction T; intros eta rho X c v Hfree; simpl in *.
  - tauto.
  - unfold relation_update.
    destruct (Nat.eqb X a) eqn:E; [apply Nat.eqb_eq in E; subst; tauto|tauto].
  - assert (HA : ~ In X (free_ty T1))
      by (intro Hin; apply Hfree; apply in_or_app; left; exact Hin).
    assert (HB : ~ In X (free_ty T2))
      by (intro Hin; apply Hfree; apply in_or_app; right; exact Hin).
    split.
    + intros [Hv [U [body [Heq Hbody]]]].
      split; [exact Hv|]. exists U, body. split; [exact Heq|].
      intros arg Harg.
      apply (proj1 (expression_lifting_iff _ _ _ (fun w => IHT2 eta rho X c w HB))).
      apply Hbody. apply (proj2 (IHT1 eta rho X c arg HA)); exact Harg.
    + intros [Hv [U [body [Heq Hbody]]]].
      split; [exact Hv|]. exists U, body. split; [exact Heq|].
      intros arg Harg.
      apply (proj2 (expression_lifting_iff _ _ _ (fun w => IHT2 eta rho X c w HB))).
      apply Hbody. apply (proj1 (IHT1 eta rho X c arg HA)); exact Harg.
  - split.
    + intros [Hv [body [Heq Hbody]]].
      split; [exact Hv|]. exists body. split; [exact Heq|].
      intros U b HU.
      apply (proj1 (expression_lifting_iff _ _ _ (fun w => IHT (b :: eta) rho X c w Hfree))).
      apply Hbody; assumption.
    + intros [Hv [body [Heq Hbody]]].
      split; [exact Hv|]. exists body. split; [exact Heq|].
      intros U b HU.
      apply (proj2 (expression_lifting_iff _ _ _ (fun w => IHT (b :: eta) rho X c w Hfree))).
      apply Hbody; assumption.
  - tauto.
Qed.

Lemma related_term_override : forall rho Gamma gamma x A arg,
  related_substitution rho Gamma gamma ->
  value_relation [] rho A arg ->
  related_substitution rho (update Gamma x A) (term_override gamma x arg).
Proof.
  intros rho Gamma gamma x A arg Hgamma Harg y B Hlookup.
  unfold update in Hlookup. simpl in Hlookup.
  unfold term_override. destruct (Nat.eqb y x) eqn:E.
  - inversion Hlookup; subst. rewrite Nat.eqb_sym, E. exact Harg.
  - rewrite Nat.eqb_sym, E. eapply Hgamma; exact Hlookup.
Qed.

Lemma lookup_context_free : forall Gamma y B X,
  lookup_context y Gamma = Some B ->
  In X (free_ty B) -> In X (free_context_types Gamma).
Proof.
  induction Gamma as [|[z A] Gamma IH]; intros y B X Hlookup Hin.
  - discriminate.
  - simpl in *. destruct (Nat.eqb y z) eqn:E.
    + inversion Hlookup; subst. apply in_or_app; left; assumption.
    + apply in_or_app; right; eauto.
Qed.

Lemma related_type_update : forall Gamma rho gamma X a,
  ~ In X (free_context_types Gamma) ->
  related_substitution rho Gamma gamma ->
  related_substitution (relation_update rho X a) Gamma gamma.
Proof.
  intros Gamma rho gamma X c Hfree Hrel y B Hlookup.
  assert (HF : ~ In X (free_ty B))
    by (intro Hin; apply Hfree; eapply lookup_context_free; eauto).
  apply (proj2 (value_relation_rho_fresh B [] rho X c (gamma y) HF)).
  eapply Hrel; exact Hlookup.
Qed.

Lemma expression_tapp : forall rho T U V f,
  locally_closed_ty U -> locally_closed_ty V -> lc_ty_at 1 T ->
  expression_relation [] rho (Ty_All T) f ->
  expression_relation [] rho (open_ty T U) (tm_tapp f V).
Proof.
  intros rho T U V f HU HV HT [Hlf [Hsf Hrf]].
  induction Hsf as [f Hsf IHf].
  eapply expression_intro.
  - apply lc_tm_tapp; assumption.
  - intros u Hu; inversion Hu; subst.
    + specialize (Hrf (tm_tabs t) (multi_refl _) (v_tabs _ H1)).
      simpl in Hrf. destruct Hrf as [_ [body [Heq Hbody]]].
      inversion Heq; subst.
      apply (proj2 (expression_lifting_iff _ _ _
        (fun w => value_relation_open_type 0 T HT [] [] rho U w eq_refl HU))).
      apply Hbody; exact HV.
    + apply IHf; eauto using step_lc.
      intros v Hv Hvalue; apply Hrf; eauto using multi_step.
  - intros Hv; exfalso; inversion Hv; subst; inversion H.
Qed.

Theorem fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall theta gamma rho,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  related_substitution rho Gamma gamma ->
  expression_relation [] rho T (instantiate theta gamma t).
Proof.
  intros Delta Gamma t T Htyp; induction Htyp;
    intros theta gamma rho Htheta Hgamma Hrelated; simpl.
  - apply expression_value. eapply Hrelated; eassumption.
  - apply expression_value. simpl.
    assert (Hlc : locally_closed_tm (tm_abs (instantiate_ty theta T1)
      (instantiate theta gamma t2))).
    { change (lc_tm_at 0 0 (instantiate theta gamma (tm_abs T1 t2))).
      eapply instantiate_lc; eauto.
      eapply has_type_lc. eapply T_Abs; eauto. }
    split; [constructor; exact Hlc|].
    exists (instantiate_ty theta T1), (instantiate theta gamma t2).
    split; [reflexivity|].
    intros arg Harg.
    destruct (fresh_exists (L ++ free_tm t2)) as [x Hx].
    assert (HL : ~ In x L)
      by (intro Hin; apply Hx; apply in_or_app; left; exact Hin).
    assert (HF : ~ In x (free_tm t2))
      by (intro Hin; apply Hx; apply in_or_app; right; exact Hin).
    specialize (H1 x HL theta (term_override gamma x arg) rho Htheta).
    assert (Harglc : locally_closed_tm arg)
      by (eapply value_lc, value_relation_value; eauto).
    specialize (H1 (term_override_closed _ _ _ Hgamma Harglc)
      (related_term_override _ _ _ _ _ _ Hrelated Harg)).
    unfold open_tm in *.
    rewrite instantiate_tm_open in H1; auto.
  - eapply expression_app; eauto.
  - apply expression_value. simpl.
    assert (Hlc : locally_closed_tm (tm_tabs (instantiate theta gamma t))).
    { change (lc_tm_at 0 0 (instantiate theta gamma (tm_tabs t))).
      eapply instantiate_lc; eauto.
      eapply has_type_lc. eapply T_TAbs; eauto. }
    split; [constructor; exact Hlc|].
    exists (instantiate theta gamma t). split; [reflexivity|].
    intros U a HU.
    destruct (fresh_exists
      (L ++ free_tm_types t ++ free_ty T ++ free_context_types Gamma))
      as [X Hfresh].
    assert (HL : ~ In X L)
      by (intro Hin; apply Hfresh; rewrite !in_app_iff; tauto).
    assert (Hft : ~ In X (free_tm_types t))
      by (intro Hin; apply Hfresh; rewrite !in_app_iff; tauto).
    assert (HfT : ~ In X (free_ty T))
      by (intro Hin; apply Hfresh; rewrite !in_app_iff; tauto).
    assert (HfG : ~ In X (free_context_types Gamma))
      by (intro Hin; apply Hfresh; rewrite !in_app_iff; tauto).
    assert (HT : lc_ty_at 1 T).
    { pose proof (has_type_type_lc _ _ _ _ (T_TAbs L Delta Gamma t T H))
        as Hclosed. inversion Hclosed; assumption. }
    specialize (H0 X HL (type_override theta X U) gamma
      (relation_update rho X a)
      (type_override_closed _ _ _ Htheta HU) Hgamma
      (related_type_update _ _ _ _ _ HfG Hrelated)).
    unfold open_tm_ty, open_ty in H0.
    rewrite instantiate_tm_ty_open in H0; auto.
    apply (proj1 (expression_lifting_iff _ _ _
      (fun w => value_relation_open_free 0 T HT [] [] rho X a w
        eq_refl HfT))).
    exact H0.
  - eapply expression_tapp; eauto using wf_ty_lc, instantiate_ty_lc.
    + eapply instantiate_ty_lc; [exact Htheta|eapply wf_ty_lc; exact H].
    + pose proof (has_type_type_lc _ _ _ _ Htyp) as Hclosed.
      inversion Hclosed; assumption.
  - apply expression_value. simpl. split; constructor; constructor.
  - eapply expression_succ; eauto.
  - eapply expression_rec; eauto.
Qed.

Lemma instantiate_ty_identity : forall T,
  instantiate_ty Ty_FVar T = T.
Proof.
  induction T; simpl; f_equal; auto.
Qed.

Lemma instantiate_identity : forall t,
  instantiate Ty_FVar tm_fvar t = t.
Proof.
  induction t; simpl; f_equal; auto using instantiate_ty_identity.
Qed.

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  intros t T Htyp.
  pose proof (fundamental [] empty t T Htyp Ty_FVar tm_fvar
    (fun _ => None)) as Hfund.
  assert (Htheta : type_substitution_closed Ty_FVar)
    by (intro X; constructor).
  assert (Hgamma : term_substitution_closed tm_fvar)
    by (intro x; constructor).
  assert (Hrelated : related_substitution (fun _ => None) empty tm_fvar)
    by (intros x A Hlookup; discriminate).
  specialize (Hfund Htheta Hgamma Hrelated).
  rewrite instantiate_identity in Hfund.
  exact (proj1 (proj2 Hfund)).
Qed.

End SystemFNormalizationRecursionMediumTask.
