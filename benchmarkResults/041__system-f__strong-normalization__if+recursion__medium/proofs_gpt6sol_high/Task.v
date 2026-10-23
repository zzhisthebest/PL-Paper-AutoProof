(** System F CBV strong-normalization benchmark, Medium variant.
    Features: if-recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFNormalizationIfRecursionMediumTask.

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
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (instantiate theta gamma t1) (instantiate theta gamma t2) (instantiate theta gamma t3)
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
  | Ty_Bool => value v /\ (v = tm_true \/ v = tm_false)
  | Ty_Nat => value v /\ numeric_value v
  end.

Definition expression_relation eta rho T t :=
  expression_lifting (value_relation eta rho T) t.

Definition related_substitution (rho : relation_env) (Gamma : context)
    (gamma : term_substitution) : Prop :=
  forall x T, lookup_context x Gamma = Some T -> value_relation [] rho T (gamma x).

Lemma numeric_value_closed : forall n, numeric_value n -> locally_closed_tm n.
Proof.
  intros n H; induction H; unfold locally_closed_tm in *; eauto.
Qed.

Lemma value_closed : forall v, value v -> locally_closed_tm v.
Proof.
  intros v H; destruct H; auto using numeric_value_closed;
    unfold locally_closed_tm; auto.
Qed.

Lemma numeric_value_no_step : forall n u,
  numeric_value n -> ~ n --> u.
Proof.
  intros n u H; revert u; induction H; intros u E; inversion E; subst;
    eauto; eapply IHnumeric_value; eauto.
Qed.

Lemma value_no_step : forall v u, value v -> ~ v --> u.
Proof.
  intros v u H; destruct H; intros E; try solve [inversion E].
  eapply numeric_value_no_step; eauto.
Qed.

Lemma value_normalizes : forall v, value v -> strongly_normalizing v.
Proof.
  intros v H; constructor; intros u E; exfalso;
    eapply value_no_step; eauto.
Qed.

Lemma multi_trans : forall t u v, t -->* u -> u -->* v -> t -->* v.
Proof.
  intros t u v H; induction H; intros E; auto.
  eapply multi_step; eauto.
Qed.

Lemma sn_step : forall t u,
  strongly_normalizing t -> t --> u -> strongly_normalizing u.
Proof.
  intros t u H E; inversion H; eauto.
Qed.

Lemma sn_multi : forall t u,
  strongly_normalizing t -> t -->* u -> strongly_normalizing u.
Proof.
  intros t u H E; induction E; auto.
  apply IHE; eauto using sn_step.
Qed.

Lemma expression_value : forall R v,
  value v -> R v -> expression_lifting R v.
Proof.
  intros R v Hval HR; unfold expression_lifting.
  split; [exact (value_closed v Hval)|].
  split; [exact (value_normalizes v Hval)|].
  intros w Hmulti Hw; inversion Hmulti; subst; auto.
  exfalso; exact (value_no_step v y Hval H).
Qed.

Lemma lc_ty_weaken : forall K T, lc_ty_at K T ->
  forall K', K <= K' -> lc_ty_at K' T.
Proof.
  intros K T H; induction H; intros K' Hle.
  - constructor; lia.
  - constructor.
  - constructor; eauto.
  - constructor; apply IHlc_ty_at; lia.
  - constructor.
  - constructor.
Qed.

Lemma lc_tm_weaken : forall K k t, lc_tm_at K k t ->
  forall K' k', K <= K' -> k <= k' -> lc_tm_at K' k' t.
Proof.
  intros K k t H; induction H; intros K' k' HK Hk.
  - constructor; lia.
  - constructor.
  - constructor; eauto using lc_ty_weaken; apply IHlc_tm_at; lia.
  - constructor; eauto.
  - constructor; apply IHlc_tm_at; lia.
  - constructor; eauto using lc_ty_weaken.
  - constructor.
  - constructor.
  - constructor; eauto.
  - constructor.
  - constructor; eauto.
  - constructor; eauto.
Qed.

Lemma lc_tm_open_rec : forall K k t u,
  lc_tm_at K (S k) t -> lc_tm_at K k u ->
  lc_tm_at K k (open_tm_rec k u t).
Proof.
  intros K k t u H; remember (S k) as depth eqn:Heq.
  revert k Heq u; induction H; intros depth Heq u Hu; subst; simpl;
    try solve [econstructor; eauto using lc_tm_weaken, lc_ty_weaken].
  - destruct (Nat.eqb depth i) eqn:E.
    + exact Hu.
    + constructor; apply Nat.eqb_neq in E; lia.
Qed.

Lemma lc_ty_open_rec : forall K T U,
  lc_ty_at (S K) T -> lc_ty_at K U ->
  lc_ty_at K (open_ty_rec K U T).
Proof.
  intros K T U H; remember (S K) as depth eqn:Heq.
  revert K Heq U; induction H; intros depth Heq U Hu; subst; simpl;
    try solve [constructor; eauto].
  - destruct (Nat.eqb depth i) eqn:E.
    + exact Hu.
    + constructor; apply Nat.eqb_neq in E; lia.
  - apply lc_ty_all; apply IHlc_ty_at with (K := S depth); auto.
    eapply lc_ty_weaken; eauto; lia.
Qed.

Lemma lc_tm_ty_open_rec : forall K k t U,
  lc_tm_at (S K) k t -> lc_ty_at K U ->
  lc_tm_at K k (open_tm_ty_rec K U t).
Proof.
  intros K k t U H; remember (S K) as depth eqn:Heq.
  revert K Heq U; induction H; intros depth Heq U Hu; subst; simpl;
    try solve [constructor; eauto using lc_ty_open_rec].
  apply lc_tm_tabs; apply IHlc_tm_at with (K := S depth); auto.
  eapply lc_ty_weaken; eauto; lia.
Qed.

Lemma step_closed : forall t u,
  t --> u -> locally_closed_tm t -> locally_closed_tm u.
Proof.
  intros t u H; induction H; intros Hlc;
    unfold locally_closed_tm in *; inversion Hlc; subst;
    try solve [eauto 8 using lc_tm_at, value_closed, numeric_value_closed].
  - match goal with Habs : lc_tm_at 0 0 (tm_abs T t) |- _ =>
      inversion Habs; subst end.
    eapply lc_tm_open_rec; eauto using value_closed.
  - match goal with Htabs : lc_tm_at 0 0 (tm_tabs t) |- _ =>
      inversion Htabs; subst end.
    eapply lc_tm_ty_open_rec; eauto.
  - apply lc_tm_app.
    + apply lc_tm_app; [exact (value_closed s H1)|exact (numeric_value_closed n H)].
    + apply lc_tm_rec; [exact (numeric_value_closed n H)|
         exact (value_closed b H0)|exact (value_closed s H1)].
Qed.

Lemma expression_reduct : forall R t u,
  expression_lifting R t -> t --> u -> expression_lifting R u.
Proof.
  intros R t u [Hlc [Hsn HR]] E.
  split; [|split].
  - eauto using step_closed.
  - eauto using sn_step.
  - intros v Hmulti Hv; apply HR with (v := v); auto.
    eapply multi_step; eauto.
Qed.

Lemma value_relation_value : forall eta rho T v,
  value_relation eta rho T v -> value v.
Proof.
  intros eta rho T; induction T; intros v H; simpl in H;
    try destruct (nth_error eta n) as [a|];
    try destruct (rho a) as [c|];
    try contradiction;
    try exact (candidate_values _ _ H);
    try exact (proj1 H).
Qed.

Lemma value_relation_closed : forall eta rho T v,
  value_relation eta rho T v -> locally_closed_tm v.
Proof.
  intros eta rho T v H; apply value_closed;
    eapply value_relation_value; eauto.
Qed.

Lemma value_relation_normalizes : forall eta rho T v,
  value_relation eta rho T v -> strongly_normalizing v.
Proof.
  intros eta rho T v H; apply value_normalizes;
    eapply value_relation_value; eauto.
Qed.

Lemma expression_lifting_intro : forall R t,
  locally_closed_tm t ->
  (forall u, t --> u -> expression_lifting R u) ->
  (forall v, t = v -> value v -> R v) ->
  expression_lifting R t.
Proof.
  intros R t Hlc Hstep Hvalue; unfold expression_lifting.
  split; [exact Hlc|].
  split.
  - constructor; intros u E; exact (proj1 (proj2 (Hstep u E))).
  - intros v Hmulti Hv; inversion Hmulti; subst.
    + eapply Hvalue; eauto.
    + eapply (proj2 (proj2 (Hstep y H))); eauto.
Qed.

Lemma expression_if : forall eta rho T c l r,
  expression_relation eta rho Ty_Bool c ->
  expression_relation eta rho T l ->
  expression_relation eta rho T r ->
  expression_relation eta rho T (tm_if c l r).
Proof.
  intros eta rho T c l r [Hlc [Hsn Hfinal]] Hl Hr.
  induction Hsn as [c Hsteps IH];
    unfold expression_relation, expression_lifting in *.
  apply expression_lifting_intro.
  - destruct Hl as [Hll _]; destruct Hr as [Hlr _].
    unfold locally_closed_tm in *; eauto.
  - intros u E; inversion E; subst.
    + exact Hl.
    + exact Hr.
    + apply IH.
      * exact H2.
      * eapply step_closed; eauto.
      * intros v Hv Hval; apply Hfinal; auto.
        eapply multi_step; eauto.
  - intros v E Hv; subst; inversion Hv; subst; inversion H.
Qed.

Lemma expression_succ : forall eta rho n,
  expression_relation eta rho Ty_Nat n ->
  expression_relation eta rho Ty_Nat (tm_succ n).
Proof.
  intros eta rho n [Hlc [Hsn Hfinal]].
  induction Hsn as [n Hsteps IH];
    unfold expression_relation, expression_lifting in *.
  apply expression_lifting_intro.
  - unfold locally_closed_tm in *; constructor; exact Hlc.
  - intros u E; inversion E; subst; apply IH.
    + assumption.
    + eapply step_closed; eauto.
    + intros v Hv Hval; apply Hfinal; auto; eapply multi_step; eauto.
  - intros v E Hv; subst; split.
    + exact Hv.
    + inversion Hv; subst; inversion H; subst; constructor; assumption.
Qed.

Lemma expression_app : forall eta rho A B f a,
  expression_relation eta rho (Ty_Arrow A B) f ->
  expression_relation eta rho A a ->
  expression_relation eta rho B (tm_app f a).
Proof.
  intros eta rho A B f a [Hflc [Hfsn Hfval]].
  revert a.
  induction Hfsn as [f Hfsteps IHf]; intros a Ha.
  destruct Ha as [Halc [Hasn Haval]].
  induction Hasn as [a Hasteps IHa] in Hflc, Hfval, Halc, Haval, IHf |- *.
  unfold expression_relation, expression_lifting in *.
  apply expression_lifting_intro.
  - unfold locally_closed_tm in *; constructor; assumption.
  - intros u E; inversion E; subst.
    + assert (Hfun : value_relation eta rho (Ty_Arrow A B) (tm_abs T t))
        by (apply Hfval; [constructor|constructor; assumption]).
      assert (Harg : value_relation eta rho A a)
        by (apply Haval; [constructor|assumption]).
      simpl in Hfun.
      destruct Hfun as [_ [U [body [Heq Hbody]]]].
      inversion Heq; subst; apply Hbody; exact Harg.
    + apply IHf; auto.
      * eapply step_closed; eauto.
      * intros v Hmulti Hv; apply Hfval; auto.
        eapply multi_step; eauto.
      * split; [exact Halc|].
        split; [constructor; exact Hasteps|exact Haval].
    + apply IHa; auto.
      * eapply step_closed; eauto.
      * intros v Hmulti Hv; apply Haval; auto.
        eapply multi_step; eauto.
  - intros v E Hv; subst; inversion Hv; subst; inversion H.
Qed.

Lemma expression_natrec_values : forall eta rho T n b s,
  numeric_value n ->
  value_relation eta rho T b ->
  value_relation eta rho (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  expression_relation eta rho T (tm_natrec n b s).
Proof.
  intros eta rho T n b s Hnum; induction Hnum; intros Hb Hs.
  - apply expression_lifting_intro.
    + unfold locally_closed_tm; apply lc_tm_rec;
        [constructor|exact (value_relation_closed _ _ _ _ Hb)|
         exact (value_relation_closed _ _ _ _ Hs)].
    + intros u E; inversion E; subst;
        try solve [exfalso; multimatch goal with
          | Hbad : ?v --> ?w |- _ =>
              exact (value_no_step v w ltac:(eauto using value_relation_value,
                v_nat, nv_zero, nv_succ) Hbad)
          end].
      apply expression_value; eauto using value_relation_value.
    + intros v E Hv; subst; inversion Hv; subst; inversion H.
  - apply expression_lifting_intro.
    + unfold locally_closed_tm; apply lc_tm_rec.
      * apply lc_tm_succ; exact (numeric_value_closed _ Hnum).
      * exact (value_relation_closed _ _ _ _ Hb).
      * exact (value_relation_closed _ _ _ _ Hs).
    + intros u E; inversion E; subst;
        try solve [exfalso; multimatch goal with
          | Hbad : ?v --> ?w |- _ =>
              exact (value_no_step v w ltac:(eauto using value_relation_value,
                v_nat, nv_zero, nv_succ) Hbad)
          end].
      eapply (expression_app eta rho T T).
      * eapply (expression_app eta rho Ty_Nat (Ty_Arrow T T)).
        -- apply expression_value; eauto using value_relation_value.
        -- apply expression_value.
           ++ constructor; exact Hnum.
           ++ simpl; split; [constructor; exact Hnum|exact Hnum].
      * apply IHHnum; assumption.
    + intros v E Hv; subst; inversion Hv; subst; inversion H.
Qed.

Lemma expression_natrec : forall eta rho T n b s,
  expression_relation eta rho Ty_Nat n ->
  expression_relation eta rho T b ->
  expression_relation eta rho (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  expression_relation eta rho T (tm_natrec n b s).
Proof.
  intros eta rho T n b s [Hnlc [Hnsn Hnval]].
  revert b s.
  induction Hnsn as [n Hnsteps IHn]; intros b s Hb Hs.
  destruct Hb as [Hblc [Hbsn Hbval]].
  revert s Hs.
  induction Hbsn as [b Hbsteps IHb]; intros s Hs.
  destruct Hs as [Hslc [Hssn Hsval]].
  induction Hssn as [s Hssteps IHs]
    in Hnlc, Hnval, Hblc, Hbval, Hslc, Hsval, IHn, IHb |- *.
  unfold expression_relation, expression_lifting in *.
  apply expression_lifting_intro.
  - unfold locally_closed_tm in *; constructor; assumption.
  - intros u E; inversion E; subst.
    + apply IHn; auto.
      * eapply step_closed; eauto.
      * intros v Hmulti Hv; apply Hnval; auto; eapply multi_step; eauto.
      * split; [exact Hblc|split; [constructor; exact Hbsteps|exact Hbval]].
      * split; [exact Hslc|split; [constructor; exact Hssteps|exact Hsval]].
    + apply IHb; auto.
      * eapply step_closed; eauto.
      * intros v Hmulti Hv; apply Hbval; auto; eapply multi_step; eauto.
      * split; [exact Hslc|split; [constructor; exact Hssteps|exact Hsval]].
    + apply IHs; auto.
      * eapply step_closed; eauto.
      * intros v Hmulti Hv; apply Hsval; auto; eapply multi_step; eauto.
    + apply expression_value.
      * assumption.
      * apply Hbval; [constructor|assumption].
    + eapply (expression_app eta rho T T).
      * eapply (expression_app eta rho Ty_Nat (Ty_Arrow T T)).
        -- apply expression_value; [exact H5|].
           apply Hsval; [constructor|exact H5].
        -- apply expression_value.
           ++ constructor; exact H2.
           ++ simpl; split; [constructor; exact H2|exact H2].
      * apply expression_natrec_values; [exact H2| |].
        -- apply Hbval; [constructor|exact H4].
        -- apply Hsval; [constructor|exact H5].
  - intros v E Hv; subst; inversion Hv; subst; inversion H.
Qed.

Lemma expression_tapp : forall eta rho T f U (a : value_candidate),
  expression_relation eta rho (Ty_All T) f ->
  locally_closed_ty U ->
  expression_relation (a :: eta) rho T (tm_tapp f U).
Proof.
  intros eta rho T f U a [Hflc [Hfsn Hfinal]] HU.
  induction Hfsn as [f Hsteps IH] in Hflc, Hfinal |- *.
  unfold expression_relation, expression_lifting in *.
  apply expression_lifting_intro.
  - unfold locally_closed_tm in *; constructor; assumption.
  - intros u E; inversion E; subst.
    + assert (Hfun : value_relation eta rho (Ty_All T) (tm_tabs t))
        by (apply Hfinal; [constructor|constructor; assumption]).
      simpl in Hfun.
      destruct Hfun as [_ [body [Heq Hbody]]].
      inversion Heq; subst; apply Hbody; exact HU.
    + apply IH.
      * assumption.
      * eapply step_closed; eauto.
      * intros v Hmulti Hv; apply Hfinal; auto; eapply multi_step; eauto.
  - intros v E Hv; subst; inversion Hv; subst; inversion H.
Qed.

Lemma expression_abs : forall eta rho A B U body,
  locally_closed_tm (tm_abs U body) ->
  (forall arg, value_relation eta rho A arg ->
     expression_relation eta rho B (open_tm body arg)) ->
  expression_relation eta rho (Ty_Arrow A B) (tm_abs U body).
Proof.
  intros eta rho A B U body Hlc Hbody.
  apply expression_value.
  - constructor; exact Hlc.
  - simpl; split.
    + constructor; exact Hlc.
    + exists U, body; split; [reflexivity|exact Hbody].
Qed.

Lemma expression_tabs : forall eta rho T body,
  locally_closed_tm (tm_tabs body) ->
  (forall U (a : value_candidate), locally_closed_ty U ->
     expression_relation (a :: eta) rho T (open_tm_ty body U)) ->
  expression_relation eta rho (Ty_All T) (tm_tabs body).
Proof.
  intros eta rho T body Hlc Hbody.
  apply expression_value.
  - constructor; exact Hlc.
  - simpl; split.
    + constructor; exact Hlc.
    + exists body; split; [reflexivity|exact Hbody].
Qed.

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  (* Complete the proof of normalization. *)
Qed.

End SystemFNormalizationIfRecursionMediumTask.
