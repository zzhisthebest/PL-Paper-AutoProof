(** System F parametricity benchmark, Hard variant.
    Features: if. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFParametricityIfHardTask.

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

Definition type_instantiation := atom -> ty.

Fixpoint ty_instantiate (Theta : type_instantiation) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => Theta X
  | Ty_Arrow A B => Ty_Arrow (ty_instantiate Theta A) (ty_instantiate Theta B)
  | Ty_All A => Ty_All (ty_instantiate Theta A)
  | Ty_Bool => Ty_Bool
  end.

Fixpoint tm_ty_instantiate (Theta : type_instantiation) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T b => tm_abs (ty_instantiate Theta T) (tm_ty_instantiate Theta b)
  | tm_app f a => tm_app (tm_ty_instantiate Theta f) (tm_ty_instantiate Theta a)
  | tm_tabs b => tm_tabs (tm_ty_instantiate Theta b)
  | tm_tapp f T => tm_tapp (tm_ty_instantiate Theta f) (ty_instantiate Theta T)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if c a b => tm_if (tm_ty_instantiate Theta c) (tm_ty_instantiate Theta a) (tm_ty_instantiate Theta b)
  end.

Definition update_type_instantiation (Theta : type_instantiation) (X : atom) (U : ty)
    : type_instantiation := fun Y => if Nat.eqb X Y then U else Theta Y.

Lemma tm_ty_instantiate_open_tm_rec : forall Theta t k s,
    tm_ty_instantiate Theta (open_tm_rec k s t) =
    open_tm_rec k (tm_ty_instantiate Theta s) (tm_ty_instantiate Theta t).
Proof.
  intros Theta t; induction t; intros k s; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - reflexivity.
  - f_equal; apply IHt.
  - f_equal; [apply IHt1|apply IHt2].
  - f_equal; apply IHt.
  - f_equal; apply IHt.
  - reflexivity.
  - reflexivity.
  - f_equal; [apply IHt1|apply IHt2|apply IHt3].
Qed.

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

Fixpoint ty_fvars (T : ty) : list atom :=
  match T with
  | Ty_BVar _ | Ty_Bool => []
  | Ty_FVar X => [X]
  | Ty_Arrow A B => ty_fvars A ++ ty_fvars B
  | Ty_All A => ty_fvars A
  end.

Fixpoint tm_ty_fvars (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_fvar _ | tm_true | tm_false => []
  | tm_abs T b => ty_fvars T ++ tm_ty_fvars b
  | tm_app f a => tm_ty_fvars f ++ tm_ty_fvars a
  | tm_tabs b => tm_ty_fvars b
  | tm_tapp f T => tm_ty_fvars f ++ ty_fvars T
  | tm_if c a b => tm_ty_fvars c ++ tm_ty_fvars a ++ tm_ty_fvars b
  end.

Lemma ty_subst_fresh_identity : forall T X U,
    ~ In X (ty_fvars T) -> ty_subst X U T = T.
Proof.
  induction T; intros X U Hfresh; simpl in *.
  - reflexivity.
  - destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E; subst. exfalso; apply Hfresh; simpl; auto.
    + reflexivity.
  - f_equal; [apply IHT1|apply IHT2]; intro Hin; apply Hfresh;
      repeat rewrite in_app_iff; intuition.
  - f_equal; apply IHT; exact Hfresh.
  - reflexivity.
Qed.

Lemma tm_ty_subst_fresh_identity : forall t X U,
    ~ In X (tm_ty_fvars t) -> tm_ty_subst X U t = t.
Proof.
  induction t; intros X U Hfresh; simpl in *; try reflexivity.
  - f_equal.
    + apply ty_subst_fresh_identity. intro Hin; apply Hfresh; repeat rewrite in_app_iff; intuition.
    + apply IHt. intro Hin; apply Hfresh; repeat rewrite in_app_iff; intuition.
  - f_equal.
    + apply IHt1. intro Hin; apply Hfresh; repeat rewrite in_app_iff; intuition.
    + apply IHt2. intro Hin; apply Hfresh; repeat rewrite in_app_iff; intuition.
  - f_equal; apply IHt; exact Hfresh.
  - f_equal.
    + apply IHt. intro Hin; apply Hfresh; repeat rewrite in_app_iff; intuition.
    + apply ty_subst_fresh_identity. intro Hin; apply Hfresh; repeat rewrite in_app_iff; intuition.
  - f_equal.
    + apply IHt1. intro Hin; apply Hfresh; repeat rewrite in_app_iff; intuition.
    + apply IHt2. intro Hin; apply Hfresh; repeat rewrite in_app_iff; intuition.
    + apply IHt3. intro Hin; apply Hfresh; repeat rewrite in_app_iff; intuition.
Qed.

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

(* A binary, call-by-value logical relation.  The list [Rho] gives the
   interpretations of bound type variables, with the most recently opened
   variable at the head. *)
Definition related_after_steps (R : tm -> tm -> Prop) (t1 t2 : tm) : Prop :=
  exists v1 v2, multi t1 v1 /\ multi t2 v2 /\ value v1 /\ value v2 /\ R v1 v2.

Definition type_relation_env := atom -> option (tm -> tm -> Prop).

Definition update_type_relation (Xi : type_relation_env) (X : atom)
    (R : tm -> tm -> Prop) : type_relation_env :=
  fun Y => if Nat.eqb X Y then Some R else Xi Y.

Definition type_context_interpretation (Delta : ty_context)
    (Xi : type_relation_env) : Prop :=
  forall X, In X Delta -> exists R, Xi X = Some R.

Fixpoint value_relation (Rho : list (tm -> tm -> Prop)) (Xi : type_relation_env) (T : ty)
    (v1 v2 : tm) : Prop :=
  match T with
  | Ty_BVar i => match nth_error Rho i with
                 | Some R => R v1 v2
                 | None => False
                 end
  | Ty_FVar X => match Xi X with
                 | Some R => R v1 v2
                 | None => False
                 end
  | Ty_Bool => (v1 = tm_true /\ v2 = tm_true) \/ (v1 = tm_false /\ v2 = tm_false)
  | Ty_Arrow T1 T2 =>
      forall a1 a2, value a1 -> value a2 ->
        value_relation Rho Xi T1 a1 a2 ->
        related_after_steps (value_relation Rho Xi T2)
          (tm_app v1 a1) (tm_app v2 a2)
  | Ty_All T1 =>
      forall (U : ty), locally_closed_ty U -> forall (R : tm -> tm -> Prop),
        related_after_steps (value_relation (R :: Rho) Xi T1)
          (tm_tapp v1 U) (tm_tapp v2 U)
  end.

Lemma related_after_steps_iff : forall R S t u,
    (forall a b, R a b <-> S a b) ->
    (related_after_steps R t u <-> related_after_steps S t u).
Proof.
  intros R S t u Hrel; split;
    intros [v1 [v2 [Ht [Hu [Hv1 [Hv2 H]]]]]];
    exists v1, v2; repeat split; try assumption; apply Hrel; assumption.
Qed.

Lemma value_relation_update_fresh : forall Rho Xi X R T v1 v2,
    ~ In X (ty_fvars T) ->
    (value_relation Rho Xi T v1 v2 <->
     value_relation Rho (update_type_relation Xi X R) T v1 v2).
Proof.
  intros Rho Xi X R T; revert Rho Xi X R; induction T;
    intros Rho Xi X R v1 v2 Hfresh; simpl in *.
  - tauto.
  - destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E; subst. exfalso; apply Hfresh; simpl; auto.
    + unfold update_type_relation. rewrite E. split; trivial.
  - split.
    + intros H a1 a2 Ha1 Ha2 Harg.
      pose proof (proj2 (IHT1 Rho Xi X R a1 a2
        (fun Hin => Hfresh (in_or_app _ _ _ (or_introl Hin)))) Harg) as Harg'.
      specialize (H a1 a2 Ha1 Ha2 Harg').
      apply (proj1 (related_after_steps_iff
        (value_relation Rho Xi T2)
        (value_relation Rho (update_type_relation Xi X R) T2)
        (tm_app v1 a1) (tm_app v2 a2)
        (fun b1 b2 => IHT2 Rho Xi X R b1 b2
          (fun Hin => Hfresh (in_or_app _ _ _ (or_intror Hin)))))).
      exact H.
    + intros H a1 a2 Ha1 Ha2 Harg.
      pose proof (proj1 (IHT1 Rho Xi X R a1 a2
        (fun Hin => Hfresh (in_or_app _ _ _ (or_introl Hin)))) Harg) as Harg'.
      specialize (H a1 a2 Ha1 Ha2 Harg').
      apply (proj2 (related_after_steps_iff
        (value_relation Rho Xi T2)
        (value_relation Rho (update_type_relation Xi X R) T2)
        (tm_app v1 a1) (tm_app v2 a2)
        (fun b1 b2 => IHT2 Rho Xi X R b1 b2
          (fun Hin => Hfresh (in_or_app _ _ _ (or_intror Hin)))))).
      exact H.
  - split.
    + intros H U HU Q.
      specialize (H U HU Q).
      apply (proj1 (related_after_steps_iff
        (value_relation (Q :: Rho) Xi T)
        (value_relation (Q :: Rho) (update_type_relation Xi X R) T)
        (tm_tapp v1 U) (tm_tapp v2 U)
        (fun a b => IHT (Q :: Rho) Xi X R a b Hfresh))).
      exact H.
    + intros H U HU Q.
      specialize (H U HU Q).
      apply (proj2 (related_after_steps_iff
        (value_relation (Q :: Rho) Xi T)
        (value_relation (Q :: Rho) (update_type_relation Xi X R) T)
        (tm_tapp v1 U) (tm_tapp v2 U)
        (fun a b => IHT (Q :: Rho) Xi X R a b Hfresh))).
      exact H.
  - tauto.
Qed.

Lemma lc_ty_arrow_inv1 : forall k A B,
    lc_ty_at k (Ty_Arrow A B) -> lc_ty_at k A.
Proof. intros; inversion H; assumption. Qed.
Lemma lc_ty_arrow_inv2 : forall k A B,
    lc_ty_at k (Ty_Arrow A B) -> lc_ty_at k B.
Proof. intros; inversion H; assumption. Qed.
Lemma lc_ty_all_inv : forall k T,
    lc_ty_at k (Ty_All T) -> lc_ty_at (S k) T.
Proof. intros; inversion H; assumption. Qed.

Lemma nth_error_cons_agree : forall (q : tm -> tm -> Prop)
    (L1 L2 : list (tm -> tm -> Prop)) k,
    (forall i, i < k -> nth_error L1 i = nth_error L2 i) ->
    forall i, i < S k -> nth_error (q :: L1) i = nth_error (q :: L2) i.
Proof.
  intros q L1 L2 k Hagree i Hi; destruct i; simpl; [reflexivity|].
  apply Hagree; lia.
Qed.

Lemma value_relation_env_agree : forall T,
  forall k Rho1 Rho2 Xi v1 v2,
    lc_ty_at k T ->
    (forall i, i < k -> nth_error Rho1 i = nth_error Rho2 i) ->
    (value_relation Rho1 Xi T v1 v2 <->
     value_relation Rho2 Xi T v1 v2).
Proof.
  induction T; intros k Rho1 Rho2 Xi v1 v2 Hlc Hagree; simpl in *.
  - inversion Hlc; subst. specialize (Hagree n H1). rewrite Hagree. tauto.
  - tauto.
  - split.
    + intros H a1 a2 Ha1 Ha2 Harg.
      pose proof (IHT1 k Rho1 Rho2 Xi a1 a2
        (lc_ty_arrow_inv1 k T1 T2 Hlc) Hagree) as Hdom.
      assert (Harg' : value_relation Rho1 Xi T1 a1 a2) by (apply (proj2 Hdom); exact Harg).
      specialize (H a1 a2 Ha1 Ha2 Harg').
      apply (proj1 (related_after_steps_iff
        (value_relation Rho1 Xi T2) (value_relation Rho2 Xi T2)
        (tm_app v1 a1) (tm_app v2 a2)
        (fun b1 b2 => IHT2 k Rho1 Rho2 Xi b1 b2
          (lc_ty_arrow_inv2 k T1 T2 Hlc) Hagree))).
      exact H.
    + intros H a1 a2 Ha1 Ha2 Harg.
      pose proof (IHT1 k Rho1 Rho2 Xi a1 a2
        (lc_ty_arrow_inv1 k T1 T2 Hlc) Hagree) as Hdom.
      assert (Harg' : value_relation Rho2 Xi T1 a1 a2) by (apply (proj1 Hdom); exact Harg).
      specialize (H a1 a2 Ha1 Ha2 Harg').
      apply (proj2 (related_after_steps_iff
        (value_relation Rho1 Xi T2) (value_relation Rho2 Xi T2)
        (tm_app v1 a1) (tm_app v2 a2)
        (fun b1 b2 => IHT2 k Rho1 Rho2 Xi b1 b2
          (lc_ty_arrow_inv2 k T1 T2 Hlc) Hagree))).
      exact H.
  - split; intros H U HU Q; specialize (H U HU Q).
    + assert (Henv : forall a b,
          value_relation (Q :: Rho1) Xi T a b <->
          value_relation (Q :: Rho2) Xi T a b).
      { intros a b. exact (IHT (S k) (Q :: Rho1) (Q :: Rho2) Xi a b
          (lc_ty_all_inv k T Hlc)
          (nth_error_cons_agree Q Rho1 Rho2 k Hagree)). }
      apply (proj1 (related_after_steps_iff
        (value_relation (Q :: Rho1) Xi T) (value_relation (Q :: Rho2) Xi T)
        (tm_tapp v1 U) (tm_tapp v2 U) Henv)); exact H.
    + assert (Henv : forall a b,
          value_relation (Q :: Rho1) Xi T a b <->
          value_relation (Q :: Rho2) Xi T a b).
      { intros a b. exact (IHT (S k) (Q :: Rho1) (Q :: Rho2) Xi a b
          (lc_ty_all_inv k T Hlc)
          (nth_error_cons_agree Q Rho1 Rho2 k Hagree)). }
      apply (proj2 (related_after_steps_iff
        (value_relation (Q :: Rho1) Xi T) (value_relation (Q :: Rho2) Xi T)
        (tm_tapp v1 U) (tm_tapp v2 U) Henv)); exact H.
  - tauto.
Qed.

Lemma value_relation_open_ty : forall T,
  forall d Rho Xi X R p q,
    length Rho = d ->
    lc_ty_at (S d) T ->
    ~ In X (ty_fvars T) ->
    (value_relation (Rho ++ [R]) Xi T p q <->
     value_relation Rho (update_type_relation Xi X R)
       (open_ty_rec d (Ty_FVar X) T) p q).
Proof.
  induction T; intros d Rho Xi X R p q Hlen Hlc Hfresh; simpl in *.
  - inversion Hlc as [kk nn Hbound | | | |]; subst kk; simpl in *.
    destruct (Nat.eqb d n) eqn:Ed.
    + apply Nat.eqb_eq in Ed; subst n. rewrite nth_error_app2 by lia.
      replace (nn - length Rho) with 0 by lia. simpl.
      unfold update_type_relation. destruct (Nat.eqb X X) eqn:EX; simpl.
      * tauto.
      * apply Nat.eqb_neq in EX; contradiction.
    + apply Nat.eqb_neq in Ed. assert (n < length Rho) by lia.
      rewrite nth_error_app1 by assumption. simpl.
      unfold update_type_relation. destruct (Nat.eqb X X) eqn:EX; simpl.
      * reflexivity.
      * apply Nat.eqb_neq in EX; contradiction.
  - destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E; subst a. exfalso. apply Hfresh. simpl; auto.
    + unfold update_type_relation. rewrite E. tauto.
  - split.
    + intros H a1 a2 Ha1 Ha2 Harg.
      pose proof (IHT1 d Rho Xi X R a1 a2 Hlen
        (lc_ty_arrow_inv1 (S d) T1 T2 Hlc)
        (fun Hin => Hfresh (in_or_app _ _ _ (or_introl Hin)))) as Hdom.
      specialize (H a1 a2 Ha1 Ha2 (proj2 Hdom Harg)).
      apply (proj1 (related_after_steps_iff
        (value_relation (Rho ++ [R]) Xi T2)
        (value_relation Rho (update_type_relation Xi X R)
          (open_ty_rec d (Ty_FVar X) T2))
        (tm_app p a1) (tm_app q a2)
        (fun x y => IHT2 d Rho Xi X R x y Hlen
          (lc_ty_arrow_inv2 (S d) T1 T2 Hlc)
          (fun Hin => Hfresh (in_or_app _ _ _ (or_intror Hin)))))).
      exact H.
    + intros H a1 a2 Ha1 Ha2 Harg.
      pose proof (IHT1 d Rho Xi X R a1 a2 Hlen
        (lc_ty_arrow_inv1 (S d) T1 T2 Hlc)
        (fun Hin => Hfresh (in_or_app _ _ _ (or_introl Hin)))) as Hdom.
      specialize (H a1 a2 Ha1 Ha2 (proj1 Hdom Harg)).
      apply (proj2 (related_after_steps_iff
        (value_relation (Rho ++ [R]) Xi T2)
        (value_relation Rho (update_type_relation Xi X R)
          (open_ty_rec d (Ty_FVar X) T2))
        (tm_app p a1) (tm_app q a2)
        (fun x y => IHT2 d Rho Xi X R x y Hlen
          (lc_ty_arrow_inv2 (S d) T1 T2 Hlc)
          (fun Hin => Hfresh (in_or_app _ _ _ (or_intror Hin)))))).
      exact H.
  - split; intros H U HU Q; specialize (H U HU Q).
    + assert (Hbody : forall x y,
          value_relation ((Q :: Rho) ++ [R]) Xi T x y <->
          value_relation (Q :: Rho) (update_type_relation Xi X R)
            (open_ty_rec (S d) (Ty_FVar X) T) x y).
      { intros x y. exact (IHT (S d) (Q :: Rho) Xi X R x y
          (f_equal S Hlen) (lc_ty_all_inv (S d) T Hlc) Hfresh). }
      apply (proj1 (related_after_steps_iff
        (value_relation ((Q :: Rho) ++ [R]) Xi T)
        (value_relation (Q :: Rho) (update_type_relation Xi X R)
          (open_ty_rec (S d) (Ty_FVar X) T))
        (tm_tapp p U) (tm_tapp q U) Hbody)); exact H.
    + assert (Hbody : forall x y,
          value_relation ((Q :: Rho) ++ [R]) Xi T x y <->
          value_relation (Q :: Rho) (update_type_relation Xi X R)
            (open_ty_rec (S d) (Ty_FVar X) T) x y).
      { intros x y. exact (IHT (S d) (Q :: Rho) Xi X R x y
          (f_equal S Hlen) (lc_ty_all_inv (S d) T Hlc) Hfresh). }
      apply (proj2 (related_after_steps_iff
        (value_relation ((Q :: Rho) ++ [R]) Xi T)
        (value_relation (Q :: Rho) (update_type_relation Xi X R)
          (open_ty_rec (S d) (Ty_FVar X) T))
        (tm_tapp p U) (tm_tapp q U) Hbody)); exact H.
  - tauto.
Qed.

Lemma value_relation_open_ty_rel : forall T,
  forall d Rho Xi U Q p q,
    length Rho = d ->
    lc_ty_at (S d) T ->
    locally_closed_ty U ->
    (forall p q, value_relation [] Xi U p q <-> Q p q) ->
    (value_relation (Rho ++ [Q]) Xi T p q <->
     value_relation Rho Xi (open_ty_rec d U T) p q).
Proof.
  induction T; intros d Rho Xi U Q p q Hlen Hlc HU HQ; simpl in *.
  - inversion Hlc as [kk nn Hbound | | | |]; subst kk; simpl in *.
    destruct (Nat.eqb d n) eqn:Ed.
    + apply Nat.eqb_eq in Ed; subst n. rewrite nth_error_app2 by lia.
      replace (nn - length Rho) with 0 by lia. simpl.
      pose proof (value_relation_env_agree U 0 [] Rho Xi p q HU
        (fun i Hi => False_rect _ (Nat.nlt_0_r i Hi))) as Henv.
      specialize (HQ p q). tauto.
    + apply Nat.eqb_neq in Ed. assert (n < length Rho) by lia.
      rewrite nth_error_app1 by assumption. simpl.
      reflexivity.
  - reflexivity.
  - split; intros H a1 a2 Ha1 Ha2 Harg.
    + pose proof (IHT1 d Rho Xi U Q a1 a2 Hlen
        (lc_ty_arrow_inv1 (S d) T1 T2 Hlc) HU HQ) as Hdom.
      specialize (H a1 a2 Ha1 Ha2 (proj2 Hdom Harg)).
      apply (proj1 (related_after_steps_iff
        (value_relation (Rho ++ [Q]) Xi T2)
        (value_relation Rho Xi (open_ty_rec d U T2))
        (tm_app p a1) (tm_app q a2)
        (fun x y => IHT2 d Rho Xi U Q x y Hlen
          (lc_ty_arrow_inv2 (S d) T1 T2 Hlc) HU HQ))). exact H.
    + pose proof (IHT1 d Rho Xi U Q a1 a2 Hlen
        (lc_ty_arrow_inv1 (S d) T1 T2 Hlc) HU HQ) as Hdom.
      specialize (H a1 a2 Ha1 Ha2 (proj1 Hdom Harg)).
      apply (proj2 (related_after_steps_iff
        (value_relation (Rho ++ [Q]) Xi T2)
        (value_relation Rho Xi (open_ty_rec d U T2))
        (tm_app p a1) (tm_app q a2)
        (fun x y => IHT2 d Rho Xi U Q x y Hlen
          (lc_ty_arrow_inv2 (S d) T1 T2 Hlc) HU HQ))). exact H.
  - split; intros H V HUinner Rinner; specialize (H V HUinner Rinner).
    + assert (Hbody : forall x y,
          value_relation ((Rinner :: Rho) ++ [Q]) Xi T x y <->
          value_relation (Rinner :: Rho) Xi (open_ty_rec (S d) U T) x y).
      { intros x y. exact (IHT (S d) (Rinner :: Rho) Xi U Q x y
          (f_equal S Hlen) (lc_ty_all_inv (S d) T Hlc) HU HQ). }
      apply (proj1 (related_after_steps_iff
        (value_relation ((Rinner :: Rho) ++ [Q]) Xi T)
        (value_relation (Rinner :: Rho) Xi (open_ty_rec (S d) U T))
        (tm_tapp p V) (tm_tapp q V) Hbody)); exact H.
    + assert (Hbody : forall x y,
          value_relation ((Rinner :: Rho) ++ [Q]) Xi T x y <->
          value_relation (Rinner :: Rho) Xi (open_ty_rec (S d) U T) x y).
      { intros x y. exact (IHT (S d) (Rinner :: Rho) Xi U Q x y
          (f_equal S Hlen) (lc_ty_all_inv (S d) T Hlc) HU HQ). }
      apply (proj2 (related_after_steps_iff
        (value_relation ((Rinner :: Rho) ++ [Q]) Xi T)
        (value_relation (Rinner :: Rho) Xi (open_ty_rec (S d) U T))
        (tm_tapp p V) (tm_tapp q V) Hbody)); exact H.
  - tauto.
Qed.

Definition term_relation_env := atom -> option (tm * tm).

Definition update_term_relation (Eta : term_relation_env) (x : atom)
    (v1 v2 : tm) : term_relation_env :=
  fun y => if Nat.eqb x y then Some (v1, v2) else Eta y.

Definition term_env_left (Eta : term_relation_env) : atom -> option tm :=
  fun x => match Eta x with Some (v, _) => Some v | None => None end.
Definition term_env_right (Eta : term_relation_env) : atom -> option tm :=
  fun x => match Eta x with Some (_, v) => Some v | None => None end.

Lemma value_locally_closed_early : forall v, value v -> locally_closed_tm v.
Proof.
  intros v Hv; inversion Hv; subst; try assumption; unfold locally_closed_tm; constructor.
Qed.

Fixpoint instantiate_tm (Eta : atom -> option tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => match Eta x with Some v => v | None => tm_fvar x end
  | tm_abs T b => tm_abs T (instantiate_tm Eta b)
  | tm_app f a => tm_app (instantiate_tm Eta f) (instantiate_tm Eta a)
  | tm_tabs b => tm_tabs (instantiate_tm Eta b)
  | tm_tapp f T => tm_tapp (instantiate_tm Eta f) T
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if c a b => tm_if (instantiate_tm Eta c) (instantiate_tm Eta a) (instantiate_tm Eta b)
  end.

Fixpoint tm_fvars (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_true | tm_false => []
  | tm_fvar x => [x]
  | tm_abs _ b | tm_tabs b => tm_fvars b
  | tm_app f a => tm_fvars f ++ tm_fvars a
  | tm_tapp f _ => tm_fvars f
  | tm_if c a b => tm_fvars c ++ tm_fvars a ++ tm_fvars b
  end.

Lemma tm_fvars_ty_instantiate : forall Theta t,
    tm_fvars (tm_ty_instantiate Theta t) = tm_fvars t.
Proof.
  intros Theta t; induction t; simpl; try reflexivity.
  - exact IHt.
  - rewrite IHt1, IHt2. reflexivity.
  - exact IHt.
  - exact IHt.
  - rewrite IHt1, IHt2, IHt3. reflexivity.
Qed.

Lemma ty_instantiate_update_fresh : forall Theta X U T,
    ~ In X (ty_fvars T) ->
    ty_instantiate (update_type_instantiation Theta X U) T = ty_instantiate Theta T.
Proof.
  intros Theta X U T; induction T; intros Hfresh; simpl in *.
  - reflexivity.
  - destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E; subst. exfalso; apply Hfresh; simpl; auto.
    + unfold update_type_instantiation. rewrite E. reflexivity.
  - rewrite IHT1, IHT2; try (intro Hin; apply Hfresh; apply in_or_app; auto). reflexivity.
  - f_equal. apply IHT. exact Hfresh.
  - reflexivity.
Qed.

Lemma tm_ty_instantiate_update_fresh : forall Theta X U t,
    ~ In X (tm_ty_fvars t) ->
    tm_ty_instantiate (update_type_instantiation Theta X U) t = tm_ty_instantiate Theta t.
Proof.
  intros Theta X U t; induction t; intros Hfresh; simpl in *; try reflexivity.
  - f_equal.
    + apply ty_instantiate_update_fresh. intro Hin. apply Hfresh. apply in_or_app; left; exact Hin.
    + apply IHt. intro Hin. apply Hfresh. apply in_or_app; right; exact Hin.
  - rewrite IHt1, IHt2; try (intro Hin; apply Hfresh; apply in_or_app; auto). reflexivity.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal.
    + apply IHt.
      intro Hin. apply Hfresh. apply in_or_app; left; exact Hin.
    + apply ty_instantiate_update_fresh. intro Hin. apply Hfresh. apply in_or_app; right; exact Hin.
  - rewrite IHt1, IHt2, IHt3; try (intro Hin; apply Hfresh; repeat rewrite in_app_iff; intuition). reflexivity.
Qed.

Definition instantiate_left (Eta : term_relation_env) (t : tm) : tm :=
  instantiate_tm (term_env_left Eta) t.
Definition instantiate_right (Eta : term_relation_env) (t : tm) : tm :=
  instantiate_tm (term_env_right Eta) t.

Lemma instantiate_tm_update_unused : forall t Eta x v,
    ~ In x (tm_fvars t) ->
    instantiate_tm (fun y => if Nat.eqb x y then Some v else Eta y) t =
    instantiate_tm Eta t.
Proof.
  induction t; intros Eta x v Hfresh; simpl in *.
  - reflexivity.
  - destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E; subst a. exfalso. apply Hfresh. simpl; auto.
    + reflexivity.
  - f_equal. apply IHt. exact Hfresh.
  - rewrite IHt1, IHt2; try (intro Hin; apply Hfresh; apply in_or_app; auto).
    reflexivity.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal. apply IHt. exact Hfresh.
  - reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2, IHt3; try (intro Hin; apply Hfresh; repeat rewrite in_app_iff; intuition).
    reflexivity.
Qed.

Lemma lc_ty_at_mono : forall k T, lc_ty_at k T ->
    forall k', k <= k' -> lc_ty_at k' T.
Proof.
  intros k T H; induction H; intros k' Hle.
  - constructor; lia.
  - constructor.
  - constructor; eauto.
  - constructor. eapply IHlc_ty_at. lia.
  - constructor.
Qed.

Lemma lc_tm_at_ty_mono : forall K k t, lc_tm_at K k t ->
    forall K', K <= K' -> lc_tm_at K' k t.
Proof.
  intros K k t H; induction H; intros K' Hle.
  - constructor; assumption.
  - constructor.
  - econstructor.
    + eapply lc_ty_at_mono; eauto.
    + eapply IHlc_tm_at; eauto.
  - constructor; eauto.
  - constructor. eapply IHlc_tm_at. lia.
  - econstructor; eauto using lc_ty_at_mono.
  - constructor.
  - constructor.
  - constructor; eauto.
Qed.

Lemma lc_tm_at_tm_mono : forall K k t, lc_tm_at K k t ->
    forall k', k <= k' -> lc_tm_at K k' t.
Proof.
  intros K k t H; induction H; intros k' Hle.
  - constructor; lia.
  - constructor.
  - econstructor.
    + assumption.
    + eapply IHlc_tm_at. lia.
  - constructor; eauto.
  - constructor; eauto.
  - econstructor; eauto.
  - constructor.
  - constructor.
  - constructor; eauto.
Qed.

Lemma instantiate_tm_lc : forall Eta K k t,
    lc_tm_at K k t ->
    (forall x v, Eta x = Some v -> locally_closed_tm v) ->
    lc_tm_at K k (instantiate_tm Eta t).
Proof.
  intros Eta K k t Hlc; induction Hlc; intros Heta; simpl;
    try (constructor; eauto).
  destruct (Eta x) as [v|] eqn:E.
  - eapply lc_tm_at_tm_mono with (k := 0); [|lia].
    eapply lc_tm_at_ty_mono with (K := 0); [apply Heta with x; exact E|lia].
  - constructor.
Qed.

Definition term_context_interpretation (Delta : ty_context) (Gamma : context)
    (Xi : type_relation_env) (Eta : term_relation_env) : Prop :=
  type_context_interpretation Delta Xi /\
  (forall x T, lookup_context x Gamma = Some T ->
    exists v1 v2, Eta x = Some (v1, v2) /\ value v1 /\ value v2 /\
      value_relation [] Xi T v1 v2) /\
  (forall x v1 v2, Eta x = Some (v1, v2) -> value v1 /\ value v2).

Lemma lookup_context_update_neq : forall Gamma x y T,
    y <> x -> lookup_context y (update Gamma x T) = lookup_context y Gamma.
Proof.
  intros Gamma x y T Hneq. unfold update. simpl.
  destruct (Nat.eqb y x) eqn:E; [apply Nat.eqb_eq in E; contradiction|reflexivity].
Qed.

Lemma type_context_interpretation_update : forall Delta Xi X R,
    type_context_interpretation Delta Xi -> ~ In X Delta ->
    type_context_interpretation (X :: Delta) (update_type_relation Xi X R).
Proof.
  intros Delta Xi X R Hctx Hnot Y [->|Hin].
  - exists R. unfold update_type_relation. rewrite Nat.eqb_refl. reflexivity.
  - destruct (Nat.eqb X Y) eqn:E.
    + apply Nat.eqb_eq in E; subst. contradiction.
    + specialize (Hctx Y Hin) as [Q HQ]. exists Q.
      unfold update_type_relation. rewrite E. exact HQ.
Qed.

Lemma term_context_interpretation_update : forall Delta Gamma Xi Eta x T a b,
    term_context_interpretation Delta Gamma Xi Eta ->
    ~ In x (map fst Gamma) ->
    value a -> value b -> value_relation [] Xi T a b ->
    term_context_interpretation Delta (update Gamma x T) Xi
      (update_term_relation Eta x a b).
Proof.
  intros Delta Gamma Xi Eta x T a b Hctx Hfresh Ha Hb Hrel.
  destruct Hctx as [Hty [Hvars Hvals]].
  split; [exact Hty|]. split.
  - intros y S Hlookup.
    destruct (Nat.eqb y x) eqn:Eyx.
    + unfold lookup_context, update in Hlookup. simpl in Hlookup.
      rewrite Eyx in Hlookup. injection Hlookup as Heq. subst S.
      apply Nat.eqb_eq in Eyx; subst y.
      exists a, b. unfold update_term_relation. rewrite Nat.eqb_refl.
      repeat split; assumption.
    + assert (Hyx : y <> x) by (intro Heq; subst; rewrite Nat.eqb_refl in Eyx; discriminate).
      rewrite lookup_context_update_neq in Hlookup by exact Hyx.
      destruct (Hvars y S Hlookup) as [c [d [Hcd [Hc [Hd Hrd]]]]].
      exists c, d. unfold update_term_relation.
      destruct (Nat.eqb x y) eqn:Exy.
      * apply Nat.eqb_eq in Exy; subst y. contradiction.
      * repeat split; assumption.
  - intros y c d Hy.
    unfold update_term_relation in Hy.
    destruct (Nat.eqb x y) eqn:Exy.
    + inversion Hy; subst. split; assumption.
    + destruct (Hvals y c d Hy) as [Hc Hd]. split; assumption.
Qed.

Lemma term_env_left_locally_closed : forall Eta,
    (forall x a b, Eta x = Some (a, b) -> value a /\ value b) ->
    forall x a, term_env_left Eta x = Some a -> locally_closed_tm a.
Proof.
  intros Eta H x a. unfold term_env_left.
  destruct (Eta x) as [[va vb]|] eqn:E; simpl; try discriminate.
  intro Heq; inversion Heq; subst a. destruct (H x va vb E); eapply value_locally_closed_early; eauto.
Qed.

Lemma term_env_right_locally_closed : forall Eta,
    (forall x a b, Eta x = Some (a, b) -> value a /\ value b) ->
    forall x b, term_env_right Eta x = Some b -> locally_closed_tm b.
Proof.
  intros Eta H x b. unfold term_env_right.
  destruct (Eta x) as [[va vb]|] eqn:E; simpl; try discriminate.
  intro Heq; inversion Heq; subst b. destruct (H x va vb E); eapply value_locally_closed_early; eauto.
Qed.

Lemma instantiate_left_update_unused : forall t Eta x a b,
    ~ In x (tm_fvars t) ->
    instantiate_left (update_term_relation Eta x a b) t = instantiate_left Eta t.
Proof.
  intros t; induction t; intros Eta x va vb Hfresh; unfold instantiate_left, term_env_left,
    update_term_relation in *; simpl in *.
  - reflexivity.
  - destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E. subst a. exfalso. apply Hfresh. simpl. left; reflexivity.
    + reflexivity.
  - f_equal. apply IHt. exact Hfresh.
  - rewrite IHt1, IHt2; try (intro Hin; apply Hfresh; apply in_or_app; auto). reflexivity.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal. apply IHt. exact Hfresh.
  - reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2, IHt3; try (intro Hin; apply Hfresh; repeat rewrite in_app_iff; intuition). reflexivity.
Qed.

Lemma instantiate_right_update_unused : forall t Eta x a b,
    ~ In x (tm_fvars t) ->
    instantiate_right (update_term_relation Eta x a b) t = instantiate_right Eta t.
Proof.
  intros t; induction t; intros Eta x va vb Hfresh; unfold instantiate_right, term_env_right,
    update_term_relation in *; simpl in *.
  - reflexivity.
  - destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E. subst a. exfalso. apply Hfresh. simpl. left; reflexivity.
    + reflexivity.
  - f_equal. apply IHt. exact Hfresh.
  - rewrite IHt1, IHt2; try (intro Hin; apply Hfresh; apply in_or_app; auto). reflexivity.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal. apply IHt. exact Hfresh.
  - reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2, IHt3; try (intro Hin; apply Hfresh; repeat rewrite in_app_iff; intuition). reflexivity.
Qed.

Lemma instantiate_left_update_self : forall Eta x a b,
    instantiate_left (update_term_relation Eta x a b) (tm_fvar x) = a.
Proof.
  intros. unfold instantiate_left, term_env_left, update_term_relation. simpl.
  destruct (Nat.eqb x x) eqn:E; [reflexivity|]. apply Nat.eqb_neq in E; contradiction.
Qed.

Lemma instantiate_right_update_self : forall Eta x a b,
    instantiate_right (update_term_relation Eta x a b) (tm_fvar x) = b.
Proof.
  intros. unfold instantiate_right, term_env_right, update_term_relation. simpl.
  destruct (Nat.eqb x x) eqn:E; [reflexivity|]. apply Nat.eqb_neq in E; contradiction.
Qed.

Lemma related_after_steps_prepend : forall R t t' u u',
    t --> t' -> u --> u' -> related_after_steps R t' u' ->
    related_after_steps R t u.
Proof.
  intros R t t' u u' Ht Hu [v1 [v2 [Ht' [Hu' [Hv1 [Hv2 HR]]]]]].
  exists v1, v2. repeat split; try assumption; econstructor; eauto.
Qed.

Lemma multi_trans_early : forall t u v, multi t u -> multi u v -> multi t v.
Proof.
  intros t u v H; induction H; intros Huv; [exact Huv|econstructor; eauto].
Qed.

Lemma multi_if_condition : forall c c' a b,
    multi c c' -> locally_closed_tm a -> locally_closed_tm b ->
    multi (tm_if c a b) (tm_if c' a b).
Proof.
  intros c c' a b H; induction H; intros Ha Hb.
  - constructor.
  - econstructor. eapply ST_If; eauto. apply IHmulti; assumption.
Qed.

Lemma related_after_steps_if : forall R c1 c2 a1 a2 b1 b2,
    related_after_steps (value_relation [] (fun _ => None) Ty_Bool) c1 c2 ->
    related_after_steps R a1 a2 -> related_after_steps R b1 b2 ->
    locally_closed_tm a1 -> locally_closed_tm a2 ->
    locally_closed_tm b1 -> locally_closed_tm b2 ->
    related_after_steps R (tm_if c1 a1 b1) (tm_if c2 a2 b2).
Proof.
  intros R c1 c2 a1 a2 b1 b2
    [cv1 [cv2 [Hc1 [Hc2 [Hcv1 [Hcv2 Hbool]]]]]] Ha Hb Hla1 Hla2 Hlb1 Hlb2.
  destruct Hbool as [[-> ->]|[-> ->]].
  - destruct Ha as [v1 [v2 [H1 [H2 [Hv1 [Hv2 HR]]]]]].
    exists v1, v2. repeat split; try assumption.
    + eapply multi_trans_early.
      * eapply multi_if_condition; eauto using value_locally_closed_early.
      * econstructor; [eapply ST_IfTrue; eauto|exact H1].
    + eapply multi_trans_early.
      * eapply multi_if_condition; eauto using value_locally_closed_early.
      * econstructor; [eapply ST_IfTrue; eauto|exact H2].
  - destruct Hb as [v1 [v2 [H1 [H2 [Hv1 [Hv2 HR]]]]]].
    exists v1, v2. repeat split; try assumption.
    + eapply multi_trans_early.
      * eapply multi_if_condition; eauto using value_locally_closed_early.
      * econstructor; [eapply ST_IfFalse; eauto|exact H1].
    + eapply multi_trans_early.
      * eapply multi_if_condition; eauto using value_locally_closed_early.
      * econstructor; [eapply ST_IfFalse; eauto|exact H2].
Qed.

Lemma multi_trans : forall t u v, multi t u -> multi u v -> multi t v.
Proof.
  intros t u v H; induction H; intros Huv.
  - exact Huv.
  - econstructor; eauto.
Qed.

Lemma value_locally_closed : forall v, value v -> locally_closed_tm v.
Proof.
  intros v Hv; inversion Hv; subst; try assumption;
    unfold locally_closed_tm; eauto.
Qed.

Lemma multi_app_left : forall t t' u,
    multi t t' -> locally_closed_tm u ->
    multi (tm_app t u) (tm_app t' u).
Proof.
  intros t t' u H; induction H; intros Hu.
  - constructor.
  - econstructor.
    + eapply ST_App1; eauto.
    + apply IHmulti; assumption.
Qed.

Lemma multi_app_right : forall v t t',
    value v -> multi t t' ->
    multi (tm_app v t) (tm_app v t').
Proof.
  intros v t t' Hv H; induction H.
  - constructor.
  - econstructor.
    + eapply ST_App2; eauto.
    + apply IHmulti; exact Hv.
Qed.

Lemma related_after_steps_app : forall R1 R2 t1 t2 u1 u2,
    related_after_steps
      (fun f1 f2 => forall a1 a2, value a1 -> value a2 -> R1 a1 a2 ->
        related_after_steps R2 (tm_app f1 a1) (tm_app f2 a2)) t1 t2 ->
    related_after_steps R1 u1 u2 ->
    locally_closed_tm u1 -> locally_closed_tm u2 ->
    related_after_steps R2 (tm_app t1 u1) (tm_app t2 u2).
Proof.
  intros R1 R2 t1 t2 u1 u2
    [f1 [f2 [Ht1 [Ht2 [Hf1 [Hf2 Hfun]]]]]]
    [a1 [a2 [Hu1 [Hu2 [Ha1 [Ha2 Ha]]]]]] Hu1lc Hu2lc.
  destruct (Hfun a1 a2 Ha1 Ha2 Ha)
    as [r1 [r2 [Hfr1 [Hfr2 [Hr1 [Hr2 Hrel]]]]]].
  exists r1, r2. repeat split; try assumption.
  - eapply multi_trans.
    + eapply multi_trans.
      * eapply multi_app_left.
        -- exact Ht1.
        -- exact Hu1lc.
      * eapply multi_app_right.
        -- exact Hf1.
        -- exact Hu1.
    + exact Hfr1.
  - eapply multi_trans.
    + eapply multi_trans.
      * eapply multi_app_left.
        -- exact Ht2.
        -- exact Hu2lc.
      * eapply multi_app_right.
        -- exact Hf2.
        -- exact Hu2.
    + exact Hfr2.
Qed.

Lemma multi_tapp : forall t t' U,
    multi t t' -> locally_closed_ty U ->
    multi (tm_tapp t U) (tm_tapp t' U).
Proof.
  intros t t' U H; induction H; intros HU.
  - constructor.
  - econstructor.
    + eapply ST_TApp; eauto.
    + apply IHmulti; assumption.
Qed.

Lemma open_ty_lc_inv : forall k T X,
    lc_ty_at k (open_ty_rec k (Ty_FVar X) T) -> lc_ty_at (S k) T.
Proof.
  intros k T; revert k; induction T; intros k X Hlc; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst. constructor; lia.
    + apply Nat.eqb_neq in E. inversion Hlc; subst. constructor; lia.
  - constructor.
  - inversion Hlc; subst. constructor; eauto.
  - inversion Hlc; subst. constructor. eauto.
  - constructor.
Qed.

Lemma lc_tm_open_inv : forall K k t x,
    lc_tm_at K k (open_tm_rec k (tm_fvar x) t) -> lc_tm_at K (S k) t.
Proof.
  intros K k t; revert K k; induction t; intros K k x Hlc; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst. constructor; lia.
    + apply Nat.eqb_neq in E. inversion Hlc; subst. constructor; lia.
  - constructor.
  - inversion Hlc; subst. econstructor; eauto.
  - inversion Hlc; subst. constructor; eauto.
  - inversion Hlc; subst. constructor. eapply IHt; eauto.
  - inversion Hlc; subst. econstructor; eauto.
  - constructor.
  - constructor.
  - inversion Hlc; subst. constructor; eauto.
Qed.

Lemma lc_tm_ty_open_inv : forall K k t X,
    lc_tm_at K k (open_tm_ty_rec K (Ty_FVar X) t) -> lc_tm_at (S K) k t.
Proof.
  intros K k t; revert K k; induction t; intros K k X Hlc; simpl in *.
  - constructor; inversion Hlc; assumption.
  - constructor; inversion Hlc; assumption.
  - inversion Hlc; subst. econstructor.
    + eapply open_ty_lc_inv; eauto.
    + eapply IHt; eauto.
  - inversion Hlc; subst. constructor; eauto.
  - inversion Hlc; subst. constructor. eapply IHt; eauto.
  - inversion Hlc; subst. econstructor; eauto.
    eapply open_ty_lc_inv; eauto.
  - constructor.
  - constructor.
  - inversion Hlc; subst. constructor; eauto.
Qed.

Lemma open_tm_rec_lc_identity : forall K k t u,
    lc_tm_at K k t -> open_tm_rec k u t = t.
Proof.
  intros K k t u Hlc; revert K k Hlc; induction t; intros K k Hlc; simpl.
  - inversion Hlc; subst. destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; lia.
    + reflexivity.
  - reflexivity.
  - inversion Hlc; subst. f_equal. eapply IHt; eauto.
  - inversion Hlc; subst. f_equal; eauto.
  - inversion Hlc; subst. f_equal. eapply IHt; eauto.
  - inversion Hlc; subst. f_equal. eapply IHt; eauto.
  - reflexivity.
  - reflexivity.
  - inversion Hlc; subst. f_equal; eauto.
Qed.

Lemma open_tm_env_commute_rec : forall Eta t k u,
    (forall x v, Eta x = Some v -> locally_closed_tm v) ->
    instantiate_tm Eta (open_tm_rec k u t) =
    open_tm_rec k (instantiate_tm Eta u) (instantiate_tm Eta t).
Proof.
  intros Eta t; induction t; intros k u Heta; simpl; try (f_equal; eauto).
  - destruct (Nat.eqb k n); simpl; reflexivity.
  - destruct (Eta a) as [v|] eqn:E; simpl.
    + assert (Hlv : lc_tm_at 0 k v).
      { eapply lc_tm_at_tm_mono with (K := 0) (k := 0) (k' := k).
        - apply Heta with a; exact E.
        - lia. }
      rewrite (open_tm_rec_lc_identity 0 k v (instantiate_tm Eta u) Hlv).
      reflexivity.
    + reflexivity.
Qed.

Lemma open_tm_env_commute : forall Eta t u,
    (forall x v, Eta x = Some v -> locally_closed_tm v) ->
    instantiate_tm Eta (open_tm t u) =
    open_tm (instantiate_tm Eta t) (instantiate_tm Eta u).
Proof. intros; apply open_tm_env_commute_rec; assumption. Qed.

Lemma in_le_fold_max : forall L x, In x L -> x <= fold_right Nat.max 0 L.
Proof.
  induction L as [|a L IH]; intros x Hin; simpl in *.
  - contradiction.
  - destruct Hin as [->|Hin].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [eapply IH; eauto|apply Nat.le_max_r].
Qed.

Lemma fresh_max_notin : forall L,
    ~ In (S (fold_right Nat.max 0 L)) L.
Proof.
  intros L Hin. pose proof (in_le_fold_max L _ Hin). lia.
Qed.

Lemma wf_ty_lc : forall Delta U, wf_ty Delta U -> locally_closed_ty U.
Proof.
  intros Delta U H; induction H.
  - unfold locally_closed_ty; constructor.
  - unfold locally_closed_ty; constructor; assumption.
  - (* The cofinite WF premise opens the top type binder with a fresh name. *)
    unfold locally_closed_ty; apply lc_ty_all.
    specialize (H0 (S (fold_right Nat.max 0 L)) (fresh_max_notin L)).
    eapply open_ty_lc_inv; exact H0.
  - unfold locally_closed_ty; constructor.
Qed.

Lemma lc_ty_subst : forall K T, lc_ty_at K T ->
    forall X U, locally_closed_ty U -> lc_ty_at K (ty_subst X U T).
Proof.
  intros K T Hlc; induction Hlc; intros Y U HU; simpl.
  - constructor; assumption.
  - destruct (Nat.eqb Y X).
    + eapply lc_ty_at_mono; [exact HU|lia].
    + constructor.
  - constructor; eauto.
  - constructor; eauto.
  - constructor.
Qed.

Lemma open_ty_rec_lc_identity : forall k T U,
    lc_ty_at k T -> open_ty_rec k U T = T.
Proof.
  intros k T U Hlc; revert k Hlc; induction T; intros k Hlc; simpl.
  - inversion Hlc; subst. destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; lia.
    + reflexivity.
  - reflexivity.
  - inversion Hlc; subst. f_equal; eauto.
  - inversion Hlc; subst. f_equal; eauto.
  - reflexivity.
Qed.

Lemma ty_instantiate_open_ty : forall Theta T k U,
    (forall X, locally_closed_ty (Theta X)) ->
    ty_instantiate Theta (open_ty_rec k U T) =
    open_ty_rec k (ty_instantiate Theta U) (ty_instantiate Theta T).
Proof.
  intros Theta T; induction T; intros k U Htheta; simpl; try reflexivity.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. eapply open_ty_rec_lc_identity.
    eapply lc_ty_at_mono; [apply Htheta|lia].
  - f_equal; [apply IHT1|apply IHT2]; assumption.
  - f_equal. apply IHT. exact Htheta.
Qed.

Lemma tm_ty_instantiate_open_tm_ty : forall Theta t k U,
    (forall X, locally_closed_ty (Theta X)) ->
    tm_ty_instantiate Theta (open_tm_ty_rec k U t) =
    open_tm_ty_rec k (ty_instantiate Theta U) (tm_ty_instantiate Theta t).
Proof.
  intros Theta t; induction t; intros k U Htheta; simpl; try reflexivity.
  - rewrite ty_instantiate_open_ty by exact Htheta. f_equal. apply IHt; exact Htheta.
  - f_equal; [apply IHt1|apply IHt2]; exact Htheta.
  - f_equal. apply IHt; exact Htheta.
  - rewrite ty_instantiate_open_ty by exact Htheta. f_equal. apply IHt; exact Htheta.
  - f_equal; [apply IHt1|apply IHt2|apply IHt3]; exact Htheta.
Qed.

Lemma open_tm_ty_rec_lc_identity_gen : forall t k j U,
    lc_tm_at k j t -> open_tm_ty_rec k U t = t.
Proof.
  intros t; induction t; intros k j U Hlc; simpl in *.
  - reflexivity.
  - reflexivity.
  - inversion Hlc; subst. f_equal.
    + eapply open_ty_rec_lc_identity; eassumption.
    + eapply IHt; eassumption.
  - inversion Hlc; subst. f_equal; [eapply IHt1|eapply IHt2]; eassumption.
  - inversion Hlc; subst. f_equal. eapply IHt; eassumption.
  - inversion Hlc; subst. f_equal.
    + eapply IHt; eassumption.
    + eapply open_ty_rec_lc_identity; eassumption.
  - reflexivity.
  - reflexivity.
  - inversion Hlc; subst. f_equal; [eapply IHt1|eapply IHt2|eapply IHt3]; eassumption.
Qed.

Lemma open_tm_ty_rec_lc_identity : forall t k U,
    locally_closed_tm t -> open_tm_ty_rec k U t = t.
Proof.
  intros t k U Hlc. eapply open_tm_ty_rec_lc_identity_gen with (j := 0).
  eapply lc_tm_at_ty_mono with (K := 0); [exact Hlc|lia].
Qed.

Lemma instantiate_tm_open_ty_commute : forall Eta t k U,
    (forall x v, Eta x = Some v -> locally_closed_tm v) ->
    instantiate_tm Eta (open_tm_ty_rec k U t) =
    open_tm_ty_rec k U (instantiate_tm Eta t).
Proof.
  intros Eta t; induction t; intros k U Heta; simpl.
  - reflexivity.
  - destruct (Eta a) as [v|] eqn:E; simpl.
    + rewrite (open_tm_ty_rec_lc_identity v k U (Heta a v E)). reflexivity.
    + reflexivity.
  - f_equal. apply IHt. exact Heta.
  - f_equal; [apply IHt1|apply IHt2]; assumption.
  - f_equal. apply IHt. exact Heta.
  - f_equal. apply IHt. exact Heta.
  - reflexivity.
  - reflexivity.
  - f_equal; [apply IHt1|apply IHt2|apply IHt3]; assumption.
Qed.

Lemma ty_subst_open_ty_rec : forall T k A X U,
    ~ In X (ty_fvars U) ->
    locally_closed_ty U ->
    ty_subst X U (open_ty_rec k A T) =
    open_ty_rec k (ty_subst X U A) (ty_subst X U T).
Proof.
  induction T; intros k A X U Hfresh HU; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - destruct (Nat.eqb X a).
    + f_equal. symmetry. eapply open_ty_rec_lc_identity.
      eapply lc_ty_at_mono; [exact HU|lia].
    + reflexivity.
  - f_equal; [apply IHT1|apply IHT2]; assumption.
  - f_equal; apply IHT; assumption.
  - reflexivity.
Qed.

Lemma tm_ty_subst_open_tm_ty_rec : forall t k A X U,
    ~ In X (ty_fvars U) ->
    locally_closed_ty U ->
    tm_ty_subst X U (open_tm_ty_rec k A t) =
    open_tm_ty_rec k (ty_subst X U A) (tm_ty_subst X U t).
Proof.
  induction t; intros k A X U Hfresh HU; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite ty_subst_open_ty_rec by eauto. f_equal; apply IHt; assumption.
  - f_equal; [apply IHt1|apply IHt2]; assumption.
  - f_equal; apply IHt; assumption.
  - rewrite ty_subst_open_ty_rec by eauto. f_equal; apply IHt; assumption.
  - reflexivity.
  - reflexivity.
  - f_equal; [apply IHt1|apply IHt2|apply IHt3]; assumption.
Qed.

Lemma tm_ty_subst_open_tm_rec : forall t k s X U,
    tm_ty_subst X U (open_tm_rec k s t) =
    open_tm_rec k (tm_ty_subst X U s) (tm_ty_subst X U t).
Proof.
  induction t; intros k s X U; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - reflexivity.
  - f_equal; apply IHt.
  - f_equal; [apply IHt1|apply IHt2].
  - f_equal; apply IHt.
  - f_equal; apply IHt.
  - reflexivity.
  - reflexivity.
  - f_equal; [apply IHt1|apply IHt2|apply IHt3].
Qed.

Lemma lc_tm_ty_subst : forall K k t, lc_tm_at K k t ->
    forall X U, locally_closed_ty U ->
      lc_tm_at K k (tm_ty_subst X U t).
Proof.
  intros K k t Hlc; revert K k Hlc; induction t;
    intros K k Hlc Y U HU; simpl in *.
  - inversion Hlc; subst; constructor; assumption.
  - inversion Hlc; subst; constructor.
  - inversion Hlc; subst. econstructor.
    + eapply lc_ty_subst; eauto.
    + eapply IHt; eauto.
  - inversion Hlc; subst. constructor; eauto.
  - inversion Hlc; subst. constructor. eapply IHt; eauto.
  - inversion Hlc; subst. econstructor; eauto using lc_ty_subst.
  - constructor.
  - constructor.
  - inversion Hlc; subst. constructor; eauto.
Qed.

Lemma ty_instantiate_lc : forall K T, lc_ty_at K T ->
    forall Theta, (forall X, locally_closed_ty (Theta X)) ->
      lc_ty_at K (ty_instantiate Theta T).
Proof.
  intros K T Hlc; induction Hlc; intros Theta Htheta; simpl.
  - constructor; assumption.
  - eapply lc_ty_at_mono; [apply Htheta|lia].
  - constructor; eauto.
  - constructor. eapply IHHlc. exact Htheta.
  - constructor.
Qed.

Lemma tm_ty_instantiate_lc : forall K k t, lc_tm_at K k t ->
    forall Theta, (forall X, locally_closed_ty (Theta X)) ->
      lc_tm_at K k (tm_ty_instantiate Theta t).
Proof.
  intros K k t Hlc; induction Hlc; intros Theta Htheta; simpl.
  - constructor; assumption.
  - constructor.
  - econstructor.
    + eapply ty_instantiate_lc; eauto.
    + eapply IHHlc; exact Htheta.
  - constructor; eauto.
  - constructor. eapply IHHlc; exact Htheta.
  - econstructor; eauto using ty_instantiate_lc.
  - constructor.
  - constructor.
  - constructor; eauto.
Qed.

Lemma value_ty_subst : forall v, value v -> forall X U,
    locally_closed_ty U -> value (tm_ty_subst X U v).
Proof.
  intros v Hv; inversion Hv; subst; intros X U HU; simpl.
  - constructor. unfold locally_closed_tm in *.
    change (lc_tm_at 0 0 (tm_ty_subst X U (tm_abs T t))).
    eapply lc_tm_ty_subst; eauto.
  - constructor. unfold locally_closed_tm in *.
    change (lc_tm_at 0 0 (tm_ty_subst X U (tm_tabs t))).
    eapply lc_tm_ty_subst; eauto.
  - constructor.
  - constructor.
Qed.

Lemma step_ty_subst : forall t t', t --> t' -> forall X U,
    locally_closed_ty U -> ~ In X (ty_fvars U) ->
    tm_ty_subst X U t --> tm_ty_subst X U t'.
Proof.
  intros t t' Hstep; induction Hstep; intros X U HU Hfresh; cbn [tm_ty_subst].
  - change (tm_app (tm_abs (ty_subst X U T) (tm_ty_subst X U t))
        (tm_ty_subst X U v) --> tm_ty_subst X U (open_tm_rec 0 v t)).
    rewrite tm_ty_subst_open_tm_rec.
    eapply ST_AppAbs.
    + change (locally_closed_tm (tm_ty_subst X U (tm_abs T t))).
      unfold locally_closed_tm in *.
      eapply lc_tm_ty_subst; eauto.
    + eapply value_ty_subst; eauto.
  - eapply ST_App1.
    + eapply IHHstep; eauto.
    + eapply lc_tm_ty_subst; eauto.
  - eapply ST_App2.
    + eapply value_ty_subst; eauto.
    + eapply IHHstep; eauto.
  - change (tm_tapp (tm_tabs (tm_ty_subst X U t)) (ty_subst X U T) -->
        tm_ty_subst X U (open_tm_ty_rec 0 T t)).
    rewrite tm_ty_subst_open_tm_ty_rec by assumption.
    eapply ST_TAppTabs.
    + change (locally_closed_tm (tm_ty_subst X U (tm_tabs t))).
      unfold locally_closed_tm in *.
      eapply lc_tm_ty_subst; eauto.
    + eapply lc_ty_subst; eauto.
  - eapply ST_TApp.
    + eapply IHHstep; eauto.
    + eapply lc_ty_subst; eauto.
  - eapply ST_IfTrue.
    + eapply lc_tm_ty_subst; eauto.
    + eapply lc_tm_ty_subst; eauto.
  - eapply ST_IfFalse.
    + eapply lc_tm_ty_subst; eauto.
    + eapply lc_tm_ty_subst; eauto.
  - eapply ST_If.
    + eapply IHHstep; eauto.
    + eapply lc_tm_ty_subst; eauto.
    + eapply lc_tm_ty_subst; eauto.
Qed.

Lemma multi_ty_subst : forall t t', t -->* t' -> forall X U,
    locally_closed_ty U -> ~ In X (ty_fvars U) ->
    tm_ty_subst X U t -->* tm_ty_subst X U t'.
Proof.
  intros t t' H; induction H; intros X U HU Hfresh.
  - constructor.
  - econstructor.
    + eapply step_ty_subst; eauto.
    + eapply IHmulti; eauto.
Qed.

Lemma has_type_lc : forall Delta Gamma t T,
    has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T H; induction H.
  - unfold locally_closed_tm; constructor.
  - unfold locally_closed_tm. econstructor.
    + eapply wf_ty_lc; eauto.
    + match goal with
      | IH : forall x, ~ In x L -> locally_closed_tm (open_tm t2 (tm_fvar x)) |- _ =>
          specialize (IH (S (fold_right Nat.max 0 L)) (fresh_max_notin L));
          unfold locally_closed_tm in IH;
          eapply lc_tm_open_inv; exact IH
      end.
  - unfold locally_closed_tm; constructor; eauto.
  - unfold locally_closed_tm; constructor.
    match goal with
    | IH : forall X, ~ In X L -> locally_closed_tm (open_tm_ty t (Ty_FVar X)) |- _ =>
        specialize (IH (S (fold_right Nat.max 0 L)) (fresh_max_notin L));
        unfold locally_closed_tm in IH;
        eapply lc_tm_ty_open_inv; exact IH
    end.
  - unfold locally_closed_tm. eapply lc_tm_tapp.
    + exact IHhas_type.
    + exact (wf_ty_lc Delta U H0).
  - unfold locally_closed_tm; constructor.
  - unfold locally_closed_tm; constructor.
  - unfold locally_closed_tm; constructor; eauto.
Qed.

Lemma lc_ty_open : forall k T, lc_ty_at (S k) T ->
    forall U, locally_closed_ty U ->
      lc_ty_at k (open_ty_rec k U T).
Proof.
  intros k T Hlc; revert k Hlc; induction T; intros k Hlc U HU; simpl.
  - inversion Hlc; subst.
    destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst n. simpl.
      eapply lc_ty_at_mono; [exact HU|lia].
    + apply Nat.eqb_neq in E. constructor; lia.
  - constructor.
  - inversion Hlc; subst. constructor; [eapply IHT1|eapply IHT2]; eauto.
  - inversion Hlc; subst. constructor. eapply IHT; eauto.
  - constructor.
Qed.

Lemma has_type_lc_ty : forall Delta Gamma t T,
    has_type Delta Gamma t T -> locally_closed_ty T.
Proof.
  intros Delta Gamma t T H; induction H.
  - eapply wf_ty_lc; eauto.
  - unfold locally_closed_ty. constructor.
    + eapply wf_ty_lc; eauto.
    + specialize (H1 (S (fold_right Nat.max 0 L)) (fresh_max_notin L)).
      exact H1.
  - inversion IHhas_type1; assumption.
  - unfold locally_closed_ty. constructor.
    specialize (H0 (S (fold_right Nat.max 0 L)) (fresh_max_notin L)).
    eapply open_ty_lc_inv. exact H0.
  - unfold locally_closed_ty in *.
    eapply lc_ty_open; [|eapply wf_ty_lc; eauto].
    inversion IHhas_type; assumption.
  - unfold locally_closed_ty; constructor.
  - unfold locally_closed_ty; constructor.
  - exact IHhas_type2.
Qed.

Fixpoint context_type_fvars (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (_, T) :: Gamma' => ty_fvars T ++ context_type_fvars Gamma'
  end.

Lemma lookup_context_type_fvars : forall Gamma x T,
    lookup_context x Gamma = Some T ->
    forall X, In X (ty_fvars T) -> In X (context_type_fvars Gamma).
Proof.
  induction Gamma as [|[y S] Gamma IH]; intros x T Hlook X HX; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + inversion Hlook; subst. apply in_or_app; left; exact HX.
    + apply in_or_app; right. eapply IH; eauto.
Qed.

Lemma fundamental_theorem : forall Delta Gamma t T,
    has_type Delta Gamma t T ->
    forall Theta, (forall X, locally_closed_ty (Theta X)) ->
    forall Xi Eta,
      type_context_interpretation Delta Xi ->
      term_context_interpretation Delta Gamma Xi Eta ->
      related_after_steps (value_relation [] Xi T)
        (instantiate_left Eta (tm_ty_instantiate Theta t))
        (instantiate_right Eta (tm_ty_instantiate Theta t)).
Proof.
  intros Delta Gamma t T H Theta Htheta Xi Eta HXi HEta.
  revert Theta Htheta Xi Eta HXi HEta. induction H; intros Theta Htheta Xi Eta HXi HEta.
  - destruct HEta as [_ [Hvars Hvals]].
    destruct (Hvars x T H) as [a [b [Hab [Ha [Hb Hrel]]]]].
    unfold instantiate_left, instantiate_right. simpl.
    unfold term_env_left, term_env_right. rewrite Hab. simpl.
    exists a, b. repeat split; try assumption; constructor.
  - set (Fresh := L ++ (map fst Gamma ++ tm_fvars t2)).
    set (x := S (fold_right Nat.max 0 Fresh)).
    assert (HfreshAll : ~ In x Fresh) by (unfold x, Fresh; apply fresh_max_notin).
    assert (HxL : ~ In x L).
    { intro Hin. apply HfreshAll. unfold Fresh. apply in_or_app; left; exact Hin. }
    assert (HxGamma : ~ In x (map fst Gamma)).
    { intro Hin. apply HfreshAll. unfold Fresh. apply in_or_app; right; apply in_or_app; left; exact Hin. }
    assert (HxBody : ~ In x (tm_fvars t2)).
    { intro Hin. apply HfreshAll. unfold Fresh. apply in_or_app; right; apply in_or_app; right; exact Hin. }
    destruct HEta as [Htyped [Hvars Hvals]].
    assert (Htyabs : has_type Delta Gamma (tm_abs T1 t2) (Ty_Arrow T1 T2)).
    { econstructor; eauto. }
    pose proof (has_type_lc _ _ _ _ Htyabs) as Hlcabs.
    assert (Hvl : value (instantiate_left Eta (tm_ty_instantiate Theta (tm_abs T1 t2)))).
    { apply v_abs. unfold locally_closed_tm in *.
      change (lc_tm_at 0 0 (instantiate_tm (term_env_left Eta)
        (tm_ty_instantiate Theta (tm_abs T1 t2)))).
      eapply instantiate_tm_lc.
      - eapply tm_ty_instantiate_lc; [exact Hlcabs|exact Htheta].
      -
      eapply term_env_left_locally_closed; exact Hvals. }
    assert (Hvr : value (instantiate_right Eta (tm_ty_instantiate Theta (tm_abs T1 t2)))).
    { apply v_abs. unfold locally_closed_tm in *.
      change (lc_tm_at 0 0 (instantiate_tm (term_env_right Eta)
        (tm_ty_instantiate Theta (tm_abs T1 t2)))).
      eapply instantiate_tm_lc.
      - eapply tm_ty_instantiate_lc; [exact Hlcabs|exact Htheta].
      -
      eapply term_env_right_locally_closed; exact Hvals. }
    exists (instantiate_left Eta (tm_ty_instantiate Theta (tm_abs T1 t2))),
      (instantiate_right Eta (tm_ty_instantiate Theta (tm_abs T1 t2))).
    split; [apply multi_refl|]. split; [apply multi_refl|]. split; [exact Hvl|]. split; [exact Hvr|].
    intros a b Ha Hb Harg.
    pose proof (H0 x HxL) as HbodyTyping.
    pose proof (term_context_interpretation_update Delta Gamma Xi Eta x T1 a b
      (conj Htyped (conj Hvars Hvals)) HxGamma Ha Hb Harg) as HbodyCtx.
    specialize (H1 x HxL Theta Htheta Xi (update_term_relation Eta x a b) HXi HbodyCtx).
    assert (Eleft : instantiate_left (update_term_relation Eta x a b)
        (tm_ty_instantiate Theta (open_tm t2 (tm_fvar x))) =
        open_tm (instantiate_left Eta (tm_ty_instantiate Theta t2)) a).
    { unfold instantiate_left. unfold open_tm at 1.
      rewrite tm_ty_instantiate_open_tm_rec.
      cbn [tm_ty_instantiate].
      change (instantiate_tm (term_env_left (update_term_relation Eta x a b))
        (open_tm (tm_ty_instantiate Theta t2) (tm_fvar x)) =
        open_tm (instantiate_tm (term_env_left Eta) (tm_ty_instantiate Theta t2)) a).
      rewrite (open_tm_env_commute (term_env_left (update_term_relation Eta x a b))
        (tm_ty_instantiate Theta t2) (tm_fvar x)).
      - change (open_tm
          (instantiate_left (update_term_relation Eta x a b) (tm_ty_instantiate Theta t2))
          (instantiate_left (update_term_relation Eta x a b) (tm_fvar x)) =
          open_tm (instantiate_left Eta (tm_ty_instantiate Theta t2)) a).
        rewrite instantiate_left_update_unused by (rewrite tm_fvars_ty_instantiate; exact HxBody).
        rewrite instantiate_left_update_self. reflexivity.
      - intros y w Hw. unfold term_env_left, update_term_relation in Hw.
        destruct (Nat.eqb x y) eqn:E.
        + simpl in Hw. inversion Hw; subst. eapply value_locally_closed_early; exact Ha.
        + eapply term_env_left_locally_closed; [exact Hvals|exact Hw]. }
    assert (Eright : instantiate_right (update_term_relation Eta x a b)
        (tm_ty_instantiate Theta (open_tm t2 (tm_fvar x))) =
        open_tm (instantiate_right Eta (tm_ty_instantiate Theta t2)) b).
    { unfold instantiate_right. unfold open_tm at 1.
      rewrite tm_ty_instantiate_open_tm_rec.
      cbn [tm_ty_instantiate].
      change (instantiate_tm (term_env_right (update_term_relation Eta x a b))
        (open_tm (tm_ty_instantiate Theta t2) (tm_fvar x)) =
        open_tm (instantiate_tm (term_env_right Eta) (tm_ty_instantiate Theta t2)) b).
      rewrite (open_tm_env_commute (term_env_right (update_term_relation Eta x a b))
        (tm_ty_instantiate Theta t2) (tm_fvar x)).
      - change (open_tm
          (instantiate_right (update_term_relation Eta x a b) (tm_ty_instantiate Theta t2))
          (instantiate_right (update_term_relation Eta x a b) (tm_fvar x)) =
          open_tm (instantiate_right Eta (tm_ty_instantiate Theta t2)) b).
        rewrite instantiate_right_update_unused by (rewrite tm_fvars_ty_instantiate; exact HxBody).
        rewrite instantiate_right_update_self. reflexivity.
      - intros y w Hw. unfold term_env_right, update_term_relation in Hw.
        destruct (Nat.eqb x y) eqn:E.
        + simpl in Hw. inversion Hw; subst. eapply value_locally_closed_early; exact Hb.
        + eapply term_env_right_locally_closed; [exact Hvals|exact Hw]. }
    rewrite Eleft, Eright in H1.
    destruct H1 as [o1 [o2 [Ho1 [Ho2 [Ho1v [Ho2v Hrel]]]]]].
    eapply related_after_steps_prepend.
    + eapply ST_AppAbs; [inversion Hvl; assumption|exact Ha].
    + eapply ST_AppAbs; [inversion Hvr; assumption|exact Hb].
    + exact (ex_intro _ o1 (ex_intro _ o2 (conj Ho1 (conj Ho2 (conj Ho1v (conj Ho2v Hrel)))))).
  - destruct HEta as [_ [Hvars Hvals]].
    specialize (IHhas_type1 Theta Htheta Xi Eta HXi (conj HXi (conj Hvars Hvals))).
    specialize (IHhas_type2 Theta Htheta Xi Eta HXi (conj HXi (conj Hvars Hvals))).
    assert (HlcL : locally_closed_tm (instantiate_left Eta (tm_ty_instantiate Theta t2))).
    { unfold instantiate_left. eapply instantiate_tm_lc.
      - eapply tm_ty_instantiate_lc; [eapply has_type_lc; exact H0|exact Htheta].
      - eapply term_env_left_locally_closed; exact Hvals. }
    assert (HlcR : locally_closed_tm (instantiate_right Eta (tm_ty_instantiate Theta t2))).
    { unfold instantiate_right. eapply instantiate_tm_lc.
      - eapply tm_ty_instantiate_lc; [eapply has_type_lc; exact H0|exact Htheta].
      - eapply term_env_right_locally_closed; exact Hvals. }
    change (related_after_steps (value_relation [] Xi T2)
      (tm_app (instantiate_left Eta (tm_ty_instantiate Theta t1)) (instantiate_left Eta (tm_ty_instantiate Theta t2)))
      (tm_app (instantiate_right Eta (tm_ty_instantiate Theta t1)) (instantiate_right Eta (tm_ty_instantiate Theta t2)))).
    eapply related_after_steps_app; eauto.
  - set (Fresh := L ++ (Delta ++ (context_type_fvars Gamma ++ (ty_fvars T ++ tm_ty_fvars t)))).
    set (x := S (fold_right Nat.max 0 Fresh)).
    assert (HfreshAll : ~ In x Fresh) by (unfold x, Fresh; apply fresh_max_notin).
    assert (HxL : ~ In x L).
    { intro Hin. apply HfreshAll. unfold Fresh. apply in_or_app; left; exact Hin. }
    assert (HxDelta : ~ In x Delta).
    { intro Hin. apply HfreshAll. unfold Fresh. apply in_or_app; right; apply in_or_app; left; exact Hin. }
    assert (HxGammaTypes : ~ In x (context_type_fvars Gamma)).
    { intro Hin. apply HfreshAll. unfold Fresh. apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hin. }
    assert (HxType : ~ In x (ty_fvars T)).
    { intro Hin. apply HfreshAll. unfold Fresh. apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hin. }
    assert (HxTerm : ~ In x (tm_ty_fvars t)).
    { intro Hin. apply HfreshAll. unfold Fresh. apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hin. }
    destruct HEta as [Htyped [Hvars Hvals]].
    pose proof (H x HxL) as HtypedBody.
    pose proof (has_type_lc_ty _ _ _ _ HtypedBody) as HlcOpenTy.
    pose proof (open_ty_lc_inv 0 T x HlcOpenTy) as HlcT.
    assert (HtabsTy : has_type Delta Gamma (tm_tabs t) (Ty_All T)).
    { econstructor; eauto. }
    pose proof (has_type_lc _ _ _ _ HtabsTy) as HlcTabs.
    assert (HtabsL : value (instantiate_left Eta (tm_ty_instantiate Theta (tm_tabs t)))).
    { apply v_tabs. unfold locally_closed_tm in *.
      change (lc_tm_at 0 0 (instantiate_tm (term_env_left Eta)
        (tm_ty_instantiate Theta (tm_tabs t)))).
      eapply instantiate_tm_lc.
      - eapply tm_ty_instantiate_lc; [exact HlcTabs|exact Htheta].
      - eapply term_env_left_locally_closed; exact Hvals. }
    assert (HtabsR : value (instantiate_right Eta (tm_ty_instantiate Theta (tm_tabs t)))).
    { apply v_tabs. unfold locally_closed_tm in *.
      change (lc_tm_at 0 0 (instantiate_tm (term_env_right Eta)
        (tm_ty_instantiate Theta (tm_tabs t)))).
      eapply instantiate_tm_lc.
      - eapply tm_ty_instantiate_lc; [exact HlcTabs|exact Htheta].
      - eapply term_env_right_locally_closed; exact Hvals. }
    exists (instantiate_left Eta (tm_ty_instantiate Theta (tm_tabs t))),
      (instantiate_right Eta (tm_ty_instantiate Theta (tm_tabs t))).
    split; [apply multi_refl|]. split; [apply multi_refl|].
    split; [exact HtabsL|]. split; [exact HtabsR|].
    intros U HU R.
    set (ThetaX := update_type_instantiation Theta x U).
    set (XiX := update_type_relation Xi x R).
    assert (HthetaX : forall Y, locally_closed_ty (ThetaX Y)).
    { intro Y. unfold ThetaX, update_type_instantiation. destruct (Nat.eqb x Y); [exact HU|apply Htheta]. }
    pose proof (type_context_interpretation_update Delta Xi x R HXi HxDelta) as HXiUpdate.
    assert (HEtaUpdate : term_context_interpretation (x :: Delta) Gamma XiX Eta).
    { split; [exact HXiUpdate|]. split.
      - intros y S Hlookup.
        destruct (Hvars y S Hlookup) as [a [b [Hab [Ha [Hb Hrel]]]]].
        exists a, b. repeat split; try assumption.
        assert (HfreshS : ~ In x (ty_fvars S)).
        { intro Hin. apply HxGammaTypes. eapply lookup_context_type_fvars; eauto. }
        exact (proj1 (value_relation_update_fresh [] Xi x R S a b HfreshS) Hrel).
      - exact Hvals. }
    specialize (H0 x HxL ThetaX HthetaX XiX Eta HXiUpdate HEtaUpdate).
    assert (EleftX : instantiate_left Eta
      (tm_ty_instantiate ThetaX (open_tm_ty t (Ty_FVar x))) =
      open_tm_ty (instantiate_left Eta (tm_ty_instantiate Theta t)) U).
    { unfold instantiate_left, open_tm_ty. rewrite tm_ty_instantiate_open_tm_ty by exact HthetaX.
      assert (Ex : ty_instantiate ThetaX (Ty_FVar x) = U).
      { unfold ty_instantiate, ThetaX, update_type_instantiation. rewrite Nat.eqb_refl. reflexivity. }
      rewrite Ex. unfold ThetaX. rewrite tm_ty_instantiate_update_fresh by exact HxTerm.
      rewrite (instantiate_tm_open_ty_commute (term_env_left Eta)
        (tm_ty_instantiate Theta t) 0 U).
      - reflexivity.
      - eapply term_env_left_locally_closed; exact Hvals. }
    assert (ErightX : instantiate_right Eta
      (tm_ty_instantiate ThetaX (open_tm_ty t (Ty_FVar x))) =
      open_tm_ty (instantiate_right Eta (tm_ty_instantiate Theta t)) U).
    { unfold instantiate_right, open_tm_ty. rewrite tm_ty_instantiate_open_tm_ty by exact HthetaX.
      assert (Ex : ty_instantiate ThetaX (Ty_FVar x) = U).
      { unfold ty_instantiate, ThetaX, update_type_instantiation. rewrite Nat.eqb_refl. reflexivity. }
      rewrite Ex. unfold ThetaX. rewrite tm_ty_instantiate_update_fresh by exact HxTerm.
      rewrite (instantiate_tm_open_ty_commute (term_env_right Eta)
        (tm_ty_instantiate Theta t) 0 U).
      - reflexivity.
      - eapply term_env_right_locally_closed; exact Hvals. }
    rewrite EleftX, ErightX in H0.
    pose proof (proj2 (related_after_steps_iff
      (value_relation [R] Xi T) (value_relation [] XiX (open_ty T (Ty_FVar x)))
      (open_tm_ty (instantiate_left Eta (tm_ty_instantiate Theta t)) U)
      (open_tm_ty (instantiate_right Eta (tm_ty_instantiate Theta t)) U)
      (fun a b => value_relation_open_ty T 0 [] Xi x R a b eq_refl HlcT HxType)) H0) as HbodyR.
    eapply related_after_steps_prepend.
    + eapply ST_TAppTabs; [inversion HtabsL; assumption|exact HU].
    + eapply ST_TAppTabs; [inversion HtabsR; assumption|exact HU].
    + exact HbodyR.
  - destruct HEta as [_ [Hvars Hvals]].
    specialize (IHhas_type Theta Htheta Xi Eta HXi (conj HXi (conj Hvars Hvals))).
    pose proof (has_type_lc_ty _ _ _ _ H) as HlcAll.
    inversion HlcAll as [| | |HlcT|]; subst.
    assert (HUtheta : locally_closed_ty (ty_instantiate Theta U)).
    { eapply ty_instantiate_lc; [eapply wf_ty_lc; exact H0|exact Htheta]. }
    destruct IHhas_type as [f1 [f2 [Hf1 [Hf2 [Hf1v [Hf2v Hall]]]]]].
    specialize (Hall (ty_instantiate Theta U) HUtheta (value_relation [] Xi U)).
    assert (HbodyR : related_after_steps (value_relation [] Xi (open_ty T U))
        (tm_tapp f1 (ty_instantiate Theta U)) (tm_tapp f2 (ty_instantiate Theta U))).
    { eapply (proj1 (related_after_steps_iff
        (value_relation [value_relation [] Xi U] Xi T)
        (value_relation [] Xi (open_ty T U))
        (tm_tapp f1 (ty_instantiate Theta U)) (tm_tapp f2 (ty_instantiate Theta U))
        (fun a b => value_relation_open_ty_rel T 0 [] Xi U
          (value_relation [] Xi U) a b eq_refl
          (lc_ty_all_inv 0 T HlcAll) (wf_ty_lc Delta U H0)
          (fun _ _ => iff_refl _)))); exact Hall. }
    change (related_after_steps (value_relation [] Xi (open_ty T U))
      (tm_tapp (instantiate_left Eta (tm_ty_instantiate Theta t)) (ty_instantiate Theta U))
      (tm_tapp (instantiate_right Eta (tm_ty_instantiate Theta t)) (ty_instantiate Theta U))).
    destruct HbodyR as [o1 [o2 [Ho1 [Ho2 [Ho1v [Ho2v Hor]]]]]].
    exists o1, o2. repeat split; try assumption.
    + eapply multi_trans.
      * eapply multi_tapp; [exact Hf1|exact HUtheta].
      * exact Ho1.
    + eapply multi_trans.
      * eapply multi_tapp; [exact Hf2|exact HUtheta].
      * exact Ho2.
  - simpl. exists tm_true, tm_true. split; [apply multi_refl|]. split; [apply multi_refl|].
    split; [apply v_true|]. split; [apply v_true|]. left; split; reflexivity.
  - simpl. exists tm_false, tm_false. split; [apply multi_refl|]. split; [apply multi_refl|].
    split; [apply v_false|]. split; [apply v_false|]. right; split; reflexivity.
  - destruct HEta as [_ [Hvars Hvals]].
    specialize (IHhas_type1 Theta Htheta Xi Eta HXi (conj HXi (conj Hvars Hvals))).
    specialize (IHhas_type2 Theta Htheta Xi Eta HXi (conj HXi (conj Hvars Hvals))).
    specialize (IHhas_type3 Theta Htheta Xi Eta HXi (conj HXi (conj Hvars Hvals))).
    assert (Hla : locally_closed_tm (instantiate_left Eta (tm_ty_instantiate Theta t2))).
    { unfold instantiate_left. eapply instantiate_tm_lc.
      - eapply tm_ty_instantiate_lc; [eapply has_type_lc; exact H0|exact Htheta].
      - eapply term_env_left_locally_closed; exact Hvals. }
    assert (Hra : locally_closed_tm (instantiate_right Eta (tm_ty_instantiate Theta t2))).
    { unfold instantiate_right. eapply instantiate_tm_lc.
      - eapply tm_ty_instantiate_lc; [eapply has_type_lc; exact H0|exact Htheta].
      - eapply term_env_right_locally_closed; exact Hvals. }
    assert (Hlb : locally_closed_tm (instantiate_left Eta (tm_ty_instantiate Theta t3))).
    { unfold instantiate_left. eapply instantiate_tm_lc.
      - eapply tm_ty_instantiate_lc; [eapply has_type_lc; exact H1|exact Htheta].
      - eapply term_env_left_locally_closed; exact Hvals. }
    assert (Hrb : locally_closed_tm (instantiate_right Eta (tm_ty_instantiate Theta t3))).
    { unfold instantiate_right. eapply instantiate_tm_lc.
      - eapply tm_ty_instantiate_lc; [eapply has_type_lc; exact H1|exact Htheta].
      - eapply term_env_right_locally_closed; exact Hvals. }
    change (related_after_steps (value_relation [] Xi T)
      (tm_if (instantiate_left Eta (tm_ty_instantiate Theta t1))
        (instantiate_left Eta (tm_ty_instantiate Theta t2))
        (instantiate_left Eta (tm_ty_instantiate Theta t3)))
      (tm_if (instantiate_right Eta (tm_ty_instantiate Theta t1))
        (instantiate_right Eta (tm_ty_instantiate Theta t2))
        (instantiate_right Eta (tm_ty_instantiate Theta t3)))).
    eapply related_after_steps_if; eauto.
Qed.

Lemma identity_from_fundamental_relation :
  (forall t, has_type [] empty t
      (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) ->
    related_after_steps
      (value_relation [] (fun _ => None)
        (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0)))) t t) ->
  forall t, has_type [] empty t
      (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) ->
  forall U v, wf_ty [] U -> value v -> has_type [] empty v U ->
    tm_app (tm_tapp t U) v -->* v.
Proof.
  intros Hfund t Ht U v HU Hv Htv.
  destruct (Hfund t Ht) as [f1 [f2 [Htf1 [Htf2 [Hf1 [Hf2 Hff]]]]]].
  assert (HlcU : locally_closed_ty U) by (eapply wf_ty_lc; eauto).
  assert (HlcV : locally_closed_tm v) by (eapply value_locally_closed; eauto).
  specialize (Hff U HlcU (fun a b => a = v /\ b = v)).
  destruct Hff as [g1 [g2 [Hfg1 [Hfg2 [Hg1 [Hg2 Hgg]]]]]].
  assert (Hrv : (fun a b => a = v /\ b = v) v v) by (split; reflexivity).
  specialize (Hgg v v Hv Hv Hrv).
  destruct Hgg as [o1 [o2 [Hgo1 [Hgo2 [Ho1 [Ho2 Hor]]]]]].
  assert (Ho1v : o1 = v) by exact (proj1 Hor).
  subst o1.
  eapply multi_trans.
  - apply multi_app_left.
    + eapply multi_tapp; [exact Htf1 | exact HlcU].
    + exact HlcV.
  - eapply multi_trans.
    + apply multi_app_left; [exact Hfg1 | exact HlcV].
    + eapply multi_trans; [exact Hgo1 | constructor].
Qed.

Lemma ty_instantiate_identity : forall T,
    ty_instantiate (fun X => Ty_FVar X) T = T.
Proof. induction T; simpl; try reflexivity; f_equal; assumption. Qed.

Lemma tm_ty_instantiate_identity : forall t,
    tm_ty_instantiate (fun X => Ty_FVar X) t = t.
Proof.
  induction t; simpl; try reflexivity.
  - rewrite ty_instantiate_identity, IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt, ty_instantiate_identity. reflexivity.
  - rewrite IHt1, IHt2, IHt3. reflexivity.
Qed.

Lemma instantiate_tm_none_identity : forall t,
    instantiate_tm (fun _ => None) t = t.
Proof.
  induction t; simpl; try reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2, IHt3. reflexivity.
Qed.

Lemma fundamental_top : forall t,
    has_type [] empty t (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) ->
    related_after_steps
      (value_relation [] (fun _ => None)
        (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0)))) t t.
Proof.
  intros t Ht.
  pose proof (fundamental_theorem [] [] t
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) Ht
    (fun X => Ty_FVar X) (fun X => lc_ty_fvar 0 X)
    (fun _ => None) (fun _ => None)) as Hfund.
  assert (HXi0 : type_context_interpretation [] (fun _ => None)).
  { intros X Hin; contradiction. }
  assert (HEta0 : term_context_interpretation [] [] (fun _ => None) (fun _ => None)).
  { split.
    - exact HXi0.
    - split.
      + intros x T Hlookup; discriminate.
      + intros x a b Heta; discriminate. }
  specialize (Hfund HXi0 HEta0).
  rewrite !tm_ty_instantiate_identity in Hfund.
  unfold instantiate_left, instantiate_right in Hfund.
  rewrite !instantiate_tm_none_identity in Hfund. exact Hfund.
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
  eapply identity_from_fundamental_relation.
  apply fundamental_top.
Qed.

End SystemFParametricityIfHardTask.
