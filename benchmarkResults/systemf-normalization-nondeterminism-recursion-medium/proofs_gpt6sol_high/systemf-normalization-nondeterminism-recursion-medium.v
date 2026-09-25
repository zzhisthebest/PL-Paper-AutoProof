(** System F CBV strong-normalization benchmark, Medium variant.
    Features: nondeterminism-recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFNormalizationNondeterminismRecursionMediumTask.

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
  | Ty_Nat => value v /\ numeric_value v
  end.

Definition expression_relation eta rho T t :=
  expression_lifting (value_relation eta rho T) t.

Definition related_substitution (rho : relation_env) (Gamma : context)
    (gamma : term_substitution) : Prop :=
  forall x T, lookup_context x Gamma = Some T -> value_relation [] rho T (gamma x).

Lemma numeric_closed : forall n, numeric_value n -> locally_closed_tm n.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma value_closed : forall v, value v -> locally_closed_tm v.
Proof.
  intros v Hv; destruct Hv; auto using numeric_closed.
Qed.

Lemma numeric_normal : forall n u, numeric_value n -> n --> u -> False.
Proof.
  intros n u Hn; revert u; induction Hn; intros u Hs.
  - inversion Hs.
  - inversion Hs; subst; eauto.
Qed.

Lemma value_normal : forall v u, value v -> v --> u -> False.
Proof.
  intros v u Hv Hs; destruct Hv; try solve [inversion Hs].
  eauto using numeric_normal.
Qed.

Lemma multi_trans : forall t u v, t -->* u -> u -->* v -> t -->* v.
Proof.
  intros t u v H; induction H; intros Huv.
  - exact Huv.
  - eapply multi_step; eauto.
Qed.

Lemma multi_value : forall t v, value t -> t -->* v -> v = t.
Proof.
  intros t v Hval H; inversion H; subst; auto.
  exfalso; eauto using value_normal.
Qed.

Lemma value_sn : forall v, value v -> strongly_normalizing v.
Proof.
  intros v Hv; constructor; intros u Hu; exfalso; eauto using value_normal.
Qed.

Lemma lift_value : forall R v, value v -> R v -> expression_lifting R v.
Proof.
  intros R v Hv Hr; split.
  - exact (value_closed _ Hv).
  - split.
    + exact (value_sn _ Hv).
    + intros w Hm _; pose proof (multi_value _ _ Hv Hm); subst; assumption.
Qed.

Lemma lc_ty_weaken : forall K T, lc_ty_at K T ->
    forall K', K <= K' -> lc_ty_at K' T.
Proof.
  intros K T H; induction H; intros K' Hle.
  - apply lc_ty_bvar; lia.
  - constructor.
  - constructor; eauto.
  - constructor; apply IHlc_ty_at; lia.
  - constructor.
Qed.

Lemma lc_tm_weaken : forall K k t, lc_tm_at K k t ->
    forall K' k', K <= K' -> k <= k' -> lc_tm_at K' k' t.
Proof.
  intros K k t H; induction H; intros K' k' HK Hk; constructor;
    eauto using lc_ty_weaken; try lia;
    match goal with
    | IH : forall _ _, _ -> _ -> lc_tm_at _ _ _ |- lc_tm_at _ _ _ =>
        eapply IH; lia
    end.
Qed.

Lemma open_ty_lc : forall K U T,
  lc_ty_at (S K) T -> lc_ty_at K U ->
  lc_ty_at K (open_ty_rec K U T).
Proof.
  intros K U T; revert K U; induction T; intros K U H Hval;
    inversion H; subst; simpl; try constructor; eauto.
  - destruct (Nat.eqb K n) eqn:Heq.
    + exact Hval.
    + constructor; apply Nat.eqb_neq in Heq; lia.
  - apply IHT; eauto using lc_ty_weaken.
Qed.

Lemma open_tm_lc : forall K k u t,
  lc_tm_at K (S k) t -> lc_tm_at K k u ->
  lc_tm_at K k (open_tm_rec k u t).
Proof.
  intros K k u t; revert K k u; induction t;
    intros K k u H Hval; inversion H; subst; simpl; try constructor;
      eauto using lc_tm_weaken.
  - destruct (Nat.eqb k n) eqn:Heq.
    + exact Hval.
    + constructor; apply Nat.eqb_neq in Heq; lia.
Qed.

Lemma open_tm_ty_lc : forall K k U t,
  lc_tm_at (S K) k t -> lc_ty_at K U ->
  lc_tm_at K k (open_tm_ty_rec K U t).
Proof.
  intros K k U t; revert K k U; induction t;
    intros K k U H Hval; inversion H; subst; simpl; try constructor;
      eauto using open_ty_lc.
  - eapply IHt; eauto using lc_ty_weaken.
Qed.

Lemma step_closed : forall t u,
  locally_closed_tm t -> t --> u -> locally_closed_tm u.
Proof.
  intros t u Hlc Hs; revert Hlc; induction Hs; intros Hlc;
    inversion Hlc; subst; eauto using value_closed.
  - eapply open_tm_lc; eauto using value_closed.
    inversion H; assumption.
  - constructor; [apply IHHs; exact H4 | exact H5].
  - constructor; [eauto using value_closed | apply IHHs; exact H5].
  - eapply open_tm_ty_lc; eauto.
    inversion H; assumption.
  - constructor; [apply IHHs; exact H4 | exact H5].
  - constructor; apply IHHs; assumption.
  - constructor; [apply IHHs; assumption | assumption | assumption].
  - constructor; [assumption | apply IHHs; assumption | assumption].
  - constructor; [assumption | assumption | apply IHHs; assumption].
  - apply lc_tm_app.
    + apply lc_tm_app.
      * exact (value_closed _ H1).
      * exact (numeric_closed _ H).
    + apply lc_tm_rec.
      * exact (numeric_closed _ H).
      * exact (value_closed _ H0).
      * exact (value_closed _ H1).
Qed.

Lemma lift_reduct : forall R t u,
  expression_lifting R t -> t --> u -> expression_lifting R u.
Proof.
  intros R t u [Hlc [Hsn Hall]] Hstep.
  split.
  - eauto using step_closed.
  - split.
    + inversion Hsn; eauto.
    + intros v Hmulti Hv; apply Hall; auto.
      eapply multi_step; eauto.
Qed.

Lemma value_relation_value : forall eta rho T v,
  value_relation eta rho T v -> value v.
Proof.
  intros eta rho T; induction T; intros v H; simpl in H.
  - destruct (nth_error eta n) as [candidate|]; [eapply candidate_values|contradiction]; eassumption.
  - destruct (rho a) as [candidate|]; [eapply candidate_values|contradiction]; eassumption.
  - exact (proj1 H).
  - exact (proj1 H).
  - exact (proj1 H).
Qed.

Lemma lift_nonvalue : forall R t,
  locally_closed_tm t -> ~ value t ->
  (forall u, t --> u -> expression_lifting R u) ->
  expression_lifting R t.
Proof.
  intros R t Hlc Hnot Hnext; split; [exact Hlc|split].
  - constructor; intros u Hstep; exact (proj1 (proj2 (Hnext u Hstep))).
  - intros v Hmulti Hval; inversion Hmulti; subst.
    + contradiction.
    + exact ((proj2 (proj2 (Hnext _ H))) _ H0 Hval).
Qed.

Lemma choice_related : forall R t1 t2,
  expression_lifting R t1 -> expression_lifting R t2 ->
  expression_lifting R (tm_choice t1 t2).
Proof.
  intros R t1 t2 Hleft Hright.
  apply lift_nonvalue.
  - constructor; [exact (proj1 Hleft)|exact (proj1 Hright)].
  - intro H; inversion H; subst; match goal with
      | Hn : numeric_value (tm_choice _ _) |- _ => inversion Hn
      end.
  - intros u Hstep; inversion Hstep; subst; assumption.
Qed.

Lemma app_related : forall eta rho A B t1 t2,
  expression_relation eta rho (Ty_Arrow A B) t1 ->
  expression_relation eta rho A t2 ->
  expression_relation eta rho B (tm_app t1 t2).
Proof.
  intros eta rho A B t1 t2 Hfun Harg.
  destruct Hfun as [Hlc1 [Hsn1 Hvalues1]].
  revert t2 Harg; induction Hsn1 as [t1 Hstep1 IH1]; intros t2 Harg.
  destruct Harg as [Hlc2 [Hsn2 Hvalues2]].
  induction Hsn2 as [t2 Hstep2 IH2].
  apply lift_nonvalue.
  - constructor; assumption.
  - intro H; inversion H; subst; match goal with
      | Hn : numeric_value (tm_app _ _) |- _ => inversion Hn
      end.
  - intros u Hstep; inversion Hstep; subst.
    + specialize (Hvalues1 _ (multi_refl _) (v_abs _ _ H1)).
      destruct Hvalues1 as [_ [U [body [Heq Happly]]]].
      inversion Heq; subst.
      apply Happly; apply Hvalues2; [constructor|exact H3].
    + apply IH1.
      * exact H1.
      * exact (proj1 (lift_reduct _ _ _
          (conj Hlc1 (conj (SN_intro _ Hstep1) Hvalues1)) H1)).
      * exact (proj2 (proj2 (lift_reduct _ _ _
          (conj Hlc1 (conj (SN_intro _ Hstep1) Hvalues1)) H1))).
      * split; [assumption|split; [exact (SN_intro _ Hstep2)|exact Hvalues2]].
    + apply IH2.
      * exact H3.
      * exact (proj1 (lift_reduct _ _ _
          (conj Hlc2 (conj (SN_intro _ Hstep2) Hvalues2)) H3)).
      * exact (proj2 (proj2 (lift_reduct _ _ _
          (conj Hlc2 (conj (SN_intro _ Hstep2) Hvalues2)) H3))).
Qed.

Lemma zero_related : forall eta rho,
  expression_relation eta rho Ty_Nat tm_zero.
Proof.
  intros eta rho; apply lift_value.
  - apply v_nat; constructor.
  - simpl; split; [apply v_nat; constructor | constructor].
Qed.

Lemma multi_succ : forall n v, tm_succ n -->* v ->
  exists m, v = tm_succ m /\ n -->* m.
Proof.
  intros n v H; remember (tm_succ n) as t eqn:Heq.
  revert n Heq; induction H; intros n Heq; subst.
  - exists n; split; [reflexivity|constructor].
  - inversion H; subst.
    destruct (IHmulti _ eq_refl) as [m [Hshape Hpath]].
    exists m; split; [exact Hshape|].
    eapply multi_step; eauto.
Qed.

Lemma succ_related : forall eta rho n,
  expression_relation eta rho Ty_Nat n ->
  expression_relation eta rho Ty_Nat (tm_succ n).
Proof.
  intros eta rho n [Hlc [Hsn Hall]].
  induction Hsn as [n Hstep IH].
  split.
  - constructor; exact Hlc.
  - split.
    + constructor; intros u Hu; inversion Hu; subst.
      apply IH.
      * exact H0.
      * exact (step_closed _ _ Hlc H0).
      * intros v Hmulti Hv; apply Hall; auto.
        eapply multi_step; eauto.
    + intros v Hmulti Hv.
      destruct (multi_succ _ _ Hmulti) as [m [Heq Hpath]].
      subst; simpl; split; [exact Hv|].
      destruct (Hall _ Hpath) as [_ Hnumeric].
      * inversion Hv; subst; try solve [inversion H].
        inversion H; subst; apply v_nat; assumption.
      * constructor; exact Hnumeric.
Qed.

Lemma numeric_related : forall eta rho n,
  numeric_value n -> expression_relation eta rho Ty_Nat n.
Proof.
  intros eta rho n Hn; apply lift_value.
  - constructor; exact Hn.
  - simpl; split; [constructor; exact Hn | exact Hn].
Qed.

Lemma rec_numeric_related : forall eta rho T n,
  numeric_value n -> forall b s,
  expression_relation eta rho T b ->
  expression_relation eta rho
    (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  expression_relation eta rho T (tm_natrec n b s).
Proof.
  intros eta rho T n Hnum; induction Hnum as [|n Hnum IHnum];
    intros b s Hb Hs.
  all: destruct Hb as [HlcB [HsnB HallB]];
    revert s Hs; induction HsnB as [b HstepB IHB];
    intros s Hs; destruct Hs as [HlcS [HsnS HallS]];
    induction HsnS as [s HstepS IHS];
    apply lift_nonvalue.
  all: try solve [constructor; auto using numeric_closed].
  all: try solve [intro H; inversion H; subst;
    match goal with Hn : numeric_value (tm_natrec _ _ _) |- _ => inversion Hn end].
  all: try solve [apply lc_tm_rec;
    [apply numeric_closed; constructor; auto|exact HlcB|exact HlcS]].
  all: intros u Hstep; inversion Hstep; subst;
    try solve [exfalso; eapply numeric_normal;
      [constructor; eauto|eassumption]].
  all: try (match goal with
    | Hred : ?base --> ?next |- expression_lifting _ (tm_natrec _ ?next _) =>
        let Hrel := fresh "Hrel" in
        pose proof (lift_reduct _ _ _
          (conj HlcB (conj (SN_intro _ HstepB) HallB)) Hred) as Hrel;
        eapply IHB; [exact Hred|exact (proj1 Hrel)|
          exact (proj2 (proj2 Hrel))|
          exact (conj HlcS (conj (SN_intro _ HstepS) HallS))]
    end).
  all: try (match goal with
    | Hred : ?function_term --> ?next |- expression_lifting _ (tm_natrec _ _ ?next) =>
        let Hrel := fresh "Hrel" in
        pose proof (lift_reduct _ _ _
          (conj HlcS (conj (SN_intro _ HstepS) HallS)) Hred) as Hrel;
        eapply IHS; [exact Hred|exact (proj1 Hrel)|
          exact (proj2 (proj2 Hrel))]
    end).
  all: try (apply lift_value; [assumption|apply HallB; [constructor|assumption]]).
  all: try (eapply app_related; [eapply app_related|];
    [ split; [exact HlcS|split; [constructor; exact HstepS|exact HallS]]
    | apply numeric_related; exact Hnum
    | apply IHnum;
      [split; [exact HlcB|split; [constructor; exact HstepB|exact HallB]]
      |split; [exact HlcS|split; [constructor; exact HstepS|exact HallS]]]]).
Qed.

Fixpoint numeric_value_dec (n : tm) : {numeric_value n} + {~ numeric_value n}.
Proof.
  destruct n; try (right; intro H; inversion H; subst; discriminate).
  - left; constructor.
  - destruct (numeric_value_dec n) as [Hyes|Hno].
    + left; constructor; assumption.
    + right; intro H; inversion H; subst; contradiction.
Defined.

Lemma rec_related : forall eta rho T n b s,
  expression_relation eta rho Ty_Nat n ->
  expression_relation eta rho T b ->
  expression_relation eta rho (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  expression_relation eta rho T (tm_natrec n b s).
Proof.
  intros eta rho T n b s [HlcN [HsnN HallN]] Hb Hs.
  induction HsnN as [n HstepN IH].
  destruct (numeric_value_dec n) as [Hnumeric|Hnot].
  - apply rec_numeric_related; assumption.
  - apply lift_nonvalue.
    + apply lc_tm_rec; [exact HlcN|exact (proj1 Hb)|exact (proj1 Hs)].
    + intro H; inversion H; subst;
        match goal with Hn : numeric_value (tm_natrec _ _ _) |- _ => inversion Hn end.
    + intros u Hstep; inversion Hstep; subst;
        try solve [exfalso; apply Hnot; assumption];
        try solve [exfalso; apply Hnot; constructor; assumption].
      apply IH.
      * assumption.
      * exact (proj1 (lift_reduct _ _ _
            (conj HlcN (conj (SN_intro _ HstepN) HallN)) H2)).
      * exact (proj2 (proj2 (lift_reduct _ _ _
            (conj HlcN (conj (SN_intro _ HstepN) HallN)) H2))).
Qed.

Definition fresh (L : list atom) : atom :=
  S (fold_right Nat.max 0 L).

Lemma fresh_not_in : forall L, ~ In (fresh L) L.
Proof.
  assert (Hbound : forall L y, In y L -> y <= fold_right Nat.max 0 L).
  { induction L as [|x xs IH]; intros y Hy; simpl in *.
    - contradiction.
    - destruct Hy as [<-|Hy].
      + apply Nat.le_max_l.
      + eapply Nat.le_trans; [apply IH; exact Hy|apply Nat.le_max_r]. }
  intros L H; unfold fresh in H.
  pose proof (Hbound L _ H); lia.
Qed.

Lemma open_ty_lc_reverse : forall K X T,
  lc_ty_at K (open_ty_rec K (Ty_FVar X) T) -> lc_ty_at (S K) T.
Proof.
  intros K X T; revert K; induction T; intros K H; simpl in H.
  - destruct (Nat.eqb K n) eqn:Heq.
    + apply Nat.eqb_eq in Heq; subst; constructor; lia.
    + inversion H; subst; constructor; lia.
  - constructor.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - constructor.
Qed.

Lemma open_tm_lc_reverse : forall K k x t,
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) ->
  lc_tm_at K (S k) t.
Proof.
  intros K k x t; revert K k; induction t;
    intros K k H; simpl in H; try solve [inversion H; subst; constructor; eauto].
  - destruct (Nat.eqb k n) eqn:Heq.
    + apply Nat.eqb_eq in Heq; subst; constructor; lia.
    + inversion H; subst; constructor; lia.
Qed.

Lemma open_tm_ty_lc_reverse : forall K k X t,
  lc_tm_at K k (open_tm_ty_rec K (Ty_FVar X) t) ->
  lc_tm_at (S K) k t.
Proof.
  intros K k X t; revert K k; induction t;
    intros K k H; simpl in H; inversion H; subst; constructor;
      eauto using open_ty_lc_reverse.
Qed.

Lemma wf_ty_closed : forall Delta T,
  wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H; induction H; try solve [constructor; eauto].
  specialize (H0 (fresh L) (fresh_not_in L)).
  apply lc_ty_all.
  eapply open_ty_lc_reverse; exact H0.
Qed.

Lemma has_type_closed : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T H; induction H;
    try solve [constructor; eauto using wf_ty_closed].
  - apply lc_tm_abs.
    + eapply wf_ty_closed; eassumption.
    + specialize (H1 (fresh L) (fresh_not_in L)).
      eapply open_tm_lc_reverse; exact H1.
  - apply lc_tm_tabs.
    specialize (H0 (fresh L) (fresh_not_in L)).
    eapply open_tm_ty_lc_reverse; exact H0.
  - constructor; [exact IHhas_type | exact (wf_ty_closed _ _ H0)].
Qed.

Lemma instantiate_ty_lc : forall theta K T,
  type_substitution_closed theta -> lc_ty_at K T ->
  lc_ty_at K (instantiate_ty theta T).
Proof.
  intros theta K T Hclosed Hlc; induction Hlc; simpl;
    try solve [constructor; eauto].
  - eapply lc_ty_weaken; [apply Hclosed|lia].
Qed.

Lemma instantiate_lc : forall theta gamma K k t,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  lc_tm_at K k t -> lc_tm_at K k (instantiate theta gamma t).
Proof.
  intros theta gamma K k t Htheta Hgamma Hlc;
    induction Hlc; simpl; try solve [constructor; eauto using instantiate_ty_lc].
  - eapply lc_tm_weaken; [apply Hgamma|lia|lia].
Qed.

Lemma instantiate_ty_at_closed : forall theta T,
  type_substitution_closed theta -> locally_closed_ty T ->
  locally_closed_ty (instantiate_ty theta T).
Proof.
  intros theta T Htheta HT; eapply instantiate_ty_lc; eauto.
Qed.

Lemma instantiate_at_closed : forall theta gamma t,
  type_substitution_closed theta ->
  term_substitution_closed gamma -> locally_closed_tm t ->
  locally_closed_tm (instantiate theta gamma t).
Proof.
  intros theta gamma t Htheta Hgamma HT;
    eapply instantiate_lc; eauto.
Qed.

Lemma lift_equiv : forall (R S : relation) t,
  (forall v, R v <-> S v) ->
  expression_lifting R t <-> expression_lifting S t.
Proof.
  intros R S t Heq; split; intros [Hlc [Hsn Hall]].
  - split; [exact Hlc|split; [exact Hsn|]].
    intros v Hmulti Hv; apply (proj1 (Heq v)); eauto.
  - split; [exact Hlc|split; [exact Hsn|]].
    intros v Hmulti Hv; apply (proj2 (Heq v)); eauto.
Qed.

Lemma value_relation_eta_ext : forall T k eta1 eta2 rho v,
  lc_ty_at k T ->
  (forall i, i < k -> nth_error eta1 i = nth_error eta2 i) ->
  (value_relation eta1 rho T v <-> value_relation eta2 rho T v).
Proof.
  induction T; intros k eta1 eta2 rho v Hlc Heq;
    inversion Hlc; subst; simpl.
  - rewrite (Heq n); [reflexivity|assumption].
  - reflexivity.
  - split; intros [Hv [U [body [Heqv Happly]]]].
    + split; [exact Hv|exists U, body; split; [exact Heqv|]].
      intros arg Harg.
      apply (proj1 (lift_equiv _ _ _
        (fun w => IHT2 k eta1 eta2 rho w H3 Heq))).
      apply Happly; apply (proj2 (IHT1 k eta1 eta2 rho arg H2 Heq)); exact Harg.
    + split; [exact Hv|exists U, body; split; [exact Heqv|]].
      intros arg Harg.
      apply (proj2 (lift_equiv _ _ _
        (fun w => IHT2 k eta1 eta2 rho w H3 Heq))).
      apply Happly; apply (proj1 (IHT1 k eta1 eta2 rho arg H2 Heq)); exact Harg.
  - split; intros [Hv [body [Heqv Happly]]].
    + split; [exact Hv|exists body; split; [exact Heqv|]].
      intros U a Hclosed.
      assert (Hcons : forall i, i < S k ->
        nth_error (a :: eta1) i = nth_error (a :: eta2) i).
      { intros [|i] Hi; simpl; [reflexivity|apply Heq; lia]. }
      apply (proj1 (lift_equiv _ _ _
        (fun w => IHT (S k) (a :: eta1) (a :: eta2) rho w H1 Hcons))).
      apply Happly; exact Hclosed.
    + split; [exact Hv|exists body; split; [exact Heqv|]].
      intros U a Hclosed.
      assert (Hcons : forall i, i < S k ->
        nth_error (a :: eta1) i = nth_error (a :: eta2) i).
      { intros [|i] Hi; simpl; [reflexivity|apply Heq; lia]. }
      apply (proj2 (lift_equiv _ _ _
        (fun w => IHT (S k) (a :: eta1) (a :: eta2) rho w H1 Hcons))).
      apply Happly; exact Hclosed.
  - reflexivity.
Qed.

Fixpoint type_atoms (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow A B => type_atoms A ++ type_atoms B
  | Ty_All body => type_atoms body
  | Ty_Nat => []
  end.

Lemma relation_open_fvar : forall T k prefix rho X candidate v,
  lc_ty_at (S k) T -> ~ In X (type_atoms T) ->
  length prefix = k ->
  (value_relation prefix (relation_update rho X candidate)
    (open_ty_rec k (Ty_FVar X) T) v <->
   value_relation (prefix ++ [candidate]) rho T v).
Proof.
  induction T; intros k prefix rho X candidate v Hlc Hfresh Hlen;
    inversion Hlc; subst; simpl in *.
  - destruct (Nat.eqb (length prefix) n) eqn:Heq.
    + apply Nat.eqb_eq in Heq; subst.
      unfold relation_update; simpl; try rewrite Nat.eqb_refl.
      rewrite nth_error_app2 by lia;
        replace (length prefix - length prefix) with 0 by lia; simpl.
      reflexivity.
    + apply Nat.eqb_neq in Heq.
      assert (n < length prefix) by lia.
      rewrite nth_error_app1 by lia; reflexivity.
  - assert (X <> a) by (intro Heq; subst; apply Hfresh; auto).
    assert (Hneq : Nat.eqb X a = false) by (apply Nat.eqb_neq; assumption).
    unfold relation_update; rewrite Hneq; reflexivity.
  - assert (Hfresh1 : ~ In X (type_atoms T1)).
    { intro Hin; apply Hfresh; apply in_or_app; left; exact Hin. }
    assert (Hfresh2 : ~ In X (type_atoms T2)).
    { intro Hin; apply Hfresh; apply in_or_app; right; exact Hin. }
    split; intros [Hv [U [body [Heqv Happly]]]].
    + split; [exact Hv|exists U, body; split; [exact Heqv|]].
      intros arg Harg.
      apply (proj1 (lift_equiv _ _ _
        (fun w => IHT2 (length prefix) prefix rho X candidate w H3 Hfresh2 eq_refl))).
      apply Happly.
      apply (proj2 (IHT1 (length prefix) prefix rho X candidate arg H2 Hfresh1 eq_refl)); exact Harg.
    + split; [exact Hv|exists U, body; split; [exact Heqv|]].
      intros arg Harg.
      apply (proj2 (lift_equiv _ _ _
        (fun w => IHT2 (length prefix) prefix rho X candidate w H3 Hfresh2 eq_refl))).
      apply Happly.
      apply (proj1 (IHT1 (length prefix) prefix rho X candidate arg H2 Hfresh1 eq_refl)); exact Harg.
  - split; intros [Hv [body [Heqv Happly]]].
    + split; [exact Hv|exists body; split; [exact Heqv|]].
      intros U b HU.
      apply (proj1 (lift_equiv _ _ _
        (fun w => IHT (S (length prefix)) (b :: prefix) rho X candidate w H1 Hfresh eq_refl))).
      apply Happly; exact HU.
    + split; [exact Hv|exists body; split; [exact Heqv|]].
      intros U b HU.
      apply (proj2 (lift_equiv _ _ _
        (fun w => IHT (S (length prefix)) (b :: prefix) rho X candidate w H1 Hfresh eq_refl))).
      apply Happly; exact HU.
  - reflexivity.
Qed.

Definition type_candidate (eta : list value_candidate) (rho : relation_env)
    (T : ty) : value_candidate :=
  {| candidate_relation := value_relation eta rho T;
     candidate_values := value_relation_value eta rho T |}.

Lemma relation_open_type : forall T k prefix rho U candidate v,
  lc_ty_at (S k) T -> locally_closed_ty U ->
  length prefix = k ->
  (forall w, candidate_relation candidate w <-> value_relation prefix rho U w) ->
  (value_relation (prefix ++ [candidate]) rho T v <->
   value_relation prefix rho (open_ty_rec k U T) v).
Proof.
  induction T; intros k prefix rho U candidate v Hlc HU Hlen Hcandidate;
    inversion Hlc; subst; simpl in *.
  - destruct (Nat.eqb (length prefix) n) eqn:Heq.
    + apply Nat.eqb_eq in Heq; subst.
      rewrite nth_error_app2 by lia;
        replace (length prefix - length prefix) with 0 by lia; simpl.
      apply Hcandidate.
    + apply Nat.eqb_neq in Heq.
      assert (n < length prefix) by lia.
      rewrite nth_error_app1 by lia; reflexivity.
  - reflexivity.
  - split; intros [Hv [Annotation [body [Heqv Happly]]]].
    + split; [exact Hv|exists Annotation, body; split; [exact Heqv|]].
      intros arg Harg.
      apply (proj1 (lift_equiv _ _ _
        (fun w => IHT2 (length prefix) prefix rho U candidate w H3 HU eq_refl Hcandidate))).
      apply Happly.
      apply (proj2 (IHT1 (length prefix) prefix rho U candidate arg H2 HU eq_refl Hcandidate)); exact Harg.
    + split; [exact Hv|exists Annotation, body; split; [exact Heqv|]].
      intros arg Harg.
      apply (proj2 (lift_equiv _ _ _
        (fun w => IHT2 (length prefix) prefix rho U candidate w H3 HU eq_refl Hcandidate))).
      apply Happly.
      apply (proj1 (IHT1 (length prefix) prefix rho U candidate arg H2 HU eq_refl Hcandidate)); exact Harg.
  - split; intros [Hv [body [Heqv Happly]]].
    + split; [exact Hv|exists body; split; [exact Heqv|]].
      intros W b HW.
      assert (Hcandidate' : forall w,
        candidate_relation candidate w <-> value_relation (b :: prefix) rho U w).
      { intros w; transitivity (value_relation prefix rho U w).
        - apply Hcandidate.
        - apply value_relation_eta_ext with (k := 0); [exact HU|intros i Hi; lia]. }
      apply (proj1 (lift_equiv _ _ _
        (fun w => IHT (S (length prefix)) (b :: prefix) rho U candidate w
          H1 HU eq_refl Hcandidate'))).
      apply Happly; exact HW.
    + split; [exact Hv|exists body; split; [exact Heqv|]].
      intros W b HW.
      assert (Hcandidate' : forall w,
        candidate_relation candidate w <-> value_relation (b :: prefix) rho U w).
      { intros w; transitivity (value_relation prefix rho U w).
        - apply Hcandidate.
        - apply value_relation_eta_ext with (k := 0); [exact HU|intros i Hi; lia]. }
      apply (proj2 (lift_equiv _ _ _
        (fun w => IHT (S (length prefix)) (b :: prefix) rho U candidate w
          H1 HU eq_refl Hcandidate'))).
      apply Happly; exact HW.
  - reflexivity.
Qed.

Lemma tapp_related : forall eta rho T U t,
  lc_ty_at 1 T -> locally_closed_ty U ->
  expression_relation eta rho (Ty_All T) t ->
  expression_relation eta rho (open_ty T U) (tm_tapp t U).
Proof.
  intros eta rho T U t HclosedT HclosedU [Hlc [Hsn Hall]].
  induction Hsn as [t Hstep IH].
  apply lift_nonvalue.
  - constructor; assumption.
  - intro H; inversion H; subst;
      match goal with Hn : numeric_value (tm_tapp _ _) |- _ => inversion Hn end.
  - intros u Hred; inversion Hred; subst.
    + pose proof (Hall _ (multi_refl _) (v_tabs _ H1)) as Hrelation.
      destruct Hrelation as [_ [body [Heq Happly]]].
      inversion Heq; subst.
      apply (proj1 (lift_equiv _ _ _
        (fun v => value_relation_eta_ext (open_ty T U) 0 [] eta rho v
          (open_ty_lc 0 U T HclosedT HclosedU)
          (fun i Hi => False_rect _ (Nat.nlt_0_r i Hi))))).
      apply (proj1 (lift_equiv _ _ _
        (fun v => relation_open_type T 0 [] rho U
          (type_candidate [] rho U) v HclosedT HclosedU eq_refl
          (fun w => iff_refl _)))).
      assert (Heq_eta : forall i, i < 1 ->
        nth_error (type_candidate [] rho U :: eta) i =
        nth_error [type_candidate [] rho U] i).
      { intros [|i] Hi; simpl; [reflexivity|lia]. }
      apply (proj1 (lift_equiv _ _ _
        (fun v => value_relation_eta_ext T 1
          (type_candidate [] rho U :: eta) [type_candidate [] rho U] rho v
          HclosedT Heq_eta))).
      apply Happly; exact HclosedU.
    + apply IH.
      * exact H1.
      * exact (proj1 (lift_reduct _ _ _
          (conj Hlc (conj (SN_intro _ Hstep) Hall)) H1)).
      * exact (proj2 (proj2 (lift_reduct _ _ _
          (conj Hlc (conj (SN_intro _ Hstep) Hall)) H1))).
Qed.

Lemma open_ty_inert : forall K T, lc_ty_at K T ->
  forall k U, K <= k -> open_ty_rec k U T = T.
Proof.
  intros K T H; induction H; intros j U Hle; simpl; auto.
  - destruct (Nat.eqb j i) eqn:Heq; [apply Nat.eqb_eq in Heq; lia|reflexivity].
  - rewrite IHlc_ty_at1, IHlc_ty_at2 by lia; reflexivity.
  - rewrite IHlc_ty_at by lia; reflexivity.
Qed.

Lemma open_tm_inert : forall K k t, lc_tm_at K k t ->
  forall j u, k <= j -> open_tm_rec j u t = t.
Proof.
  intros K k t H; induction H; intros j u Hle; simpl; auto.
  - destruct (Nat.eqb j i) eqn:Heq; [apply Nat.eqb_eq in Heq; lia|reflexivity].
  - rewrite IHlc_tm_at by lia; reflexivity.
  - rewrite IHlc_tm_at1, IHlc_tm_at2 by lia; reflexivity.
  - rewrite IHlc_tm_at by lia; reflexivity.
  - rewrite IHlc_tm_at by lia; reflexivity.
  - rewrite IHlc_tm_at by lia; reflexivity.
  - rewrite IHlc_tm_at1, IHlc_tm_at2, IHlc_tm_at3 by lia; reflexivity.
  - rewrite IHlc_tm_at1, IHlc_tm_at2 by lia; reflexivity.
Qed.

Lemma open_tm_ty_inert : forall K k t, lc_tm_at K k t ->
  forall j U, K <= j -> open_tm_ty_rec j U t = t.
Proof.
  intros K k t H; induction H; intros j U Hle; simpl; auto.
  - rewrite (open_ty_inert K T H j U Hle).
    rewrite IHlc_tm_at by lia; reflexivity.
  - rewrite IHlc_tm_at1, IHlc_tm_at2 by lia; reflexivity.
  - rewrite IHlc_tm_at by lia; reflexivity.
  - rewrite IHlc_tm_at by lia;
      rewrite (open_ty_inert K T H0 j U Hle); reflexivity.
  - rewrite IHlc_tm_at by lia; reflexivity.
  - rewrite IHlc_tm_at1, IHlc_tm_at2, IHlc_tm_at3 by lia; reflexivity.
  - rewrite IHlc_tm_at1, IHlc_tm_at2 by lia; reflexivity.
Qed.

Fixpoint term_atoms (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs _ body => term_atoms body
  | tm_app t1 t2 | tm_choice t1 t2 => term_atoms t1 ++ term_atoms t2
  | tm_tabs body | tm_succ body => term_atoms body
  | tm_tapp body _ => term_atoms body
  | tm_zero => []
  | tm_natrec n b s => term_atoms n ++ term_atoms b ++ term_atoms s
  end.

Fixpoint type_atoms_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_fvar _ | tm_zero => []
  | tm_abs T body => type_atoms T ++ type_atoms_tm body
  | tm_app t1 t2 | tm_choice t1 t2 => type_atoms_tm t1 ++ type_atoms_tm t2
  | tm_tabs body | tm_succ body => type_atoms_tm body
  | tm_tapp body T => type_atoms_tm body ++ type_atoms T
  | tm_natrec n b s => type_atoms_tm n ++ type_atoms_tm b ++ type_atoms_tm s
  end.

Fixpoint context_type_atoms (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (_, T) :: rest => type_atoms T ++ context_type_atoms rest
  end.

Definition theta_update (theta : type_substitution) (X : atom) (U : ty) :
    type_substitution :=
  fun Y => if Nat.eqb X Y then U else theta Y.

Definition gamma_update (gamma : term_substitution) (x : atom) (v : tm) :
    term_substitution :=
  fun y => if Nat.eqb x y then v else gamma y.

Lemma theta_update_closed : forall theta X U,
  type_substitution_closed theta -> locally_closed_ty U ->
  type_substitution_closed (theta_update theta X U).
Proof.
  intros theta X U Htheta HU Y; unfold theta_update;
    destruct (Nat.eqb X Y); auto.
Qed.

Lemma gamma_update_closed : forall gamma x v,
  term_substitution_closed gamma -> locally_closed_tm v ->
  term_substitution_closed (gamma_update gamma x v).
Proof.
  intros gamma x v Hgamma Hv y; unfold gamma_update;
    destruct (Nat.eqb x y); auto.
Qed.

Lemma instantiate_ty_open_fvar : forall theta X U T k,
  type_substitution_closed theta -> ~ In X (type_atoms T) ->
  instantiate_ty (theta_update theta X U)
    (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k U (instantiate_ty theta T).
Proof.
  intros theta X U T; induction T; intros k Htheta Hfresh; simpl in *.
  - destruct (Nat.eqb k n) eqn:Heq; simpl.
    + unfold theta_update; rewrite Nat.eqb_refl; reflexivity.
    + reflexivity.
  - assert (X <> a) by (intro Heq; subst; apply Hfresh; auto).
    unfold theta_update;
      rewrite (proj2 (Nat.eqb_neq X a)) by assumption.
    symmetry; apply open_ty_inert with (K := 0); [apply Htheta|lia].
  - assert (Hfresh1 : ~ In X (type_atoms T1)).
    { intro Hin; apply Hfresh; apply in_or_app; left; exact Hin. }
    assert (Hfresh2 : ~ In X (type_atoms T2)).
    { intro Hin; apply Hfresh; apply in_or_app; right; exact Hin. }
    rewrite IHT1, IHT2 by assumption; reflexivity.
  - rewrite IHT by assumption; reflexivity.
  - reflexivity.
Qed.

Lemma not_in_app_parts : forall (x : atom) (L R : list atom),
  ~ In x (L ++ R) -> ~ In x L /\ ~ In x R.
Proof.
  intros x L R H; split; intro Hin; apply H; apply in_or_app;
    [left|right]; exact Hin.
Qed.

Lemma instantiate_open_fvar : forall theta gamma x v t k,
  term_substitution_closed gamma -> ~ In x (term_atoms t) ->
  instantiate theta (gamma_update gamma x v)
    (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k v (instantiate theta gamma t).
Proof.
  intros theta gamma x v t; induction t; intros k Hgamma Hfresh;
    simpl in *.
  - destruct (Nat.eqb k n); simpl.
    + unfold gamma_update; rewrite Nat.eqb_refl; reflexivity.
    + reflexivity.
  - assert (Hneq : x <> a) by (intro Heq; subst; apply Hfresh; auto).
    unfold gamma_update; rewrite (proj2 (Nat.eqb_neq x a)) by assumption.
    symmetry; apply open_tm_inert with (K := 0) (k := 0);
      [apply Hgamma|lia].
  - simpl; f_equal; apply IHt; assumption.
  - destruct (not_in_app_parts _ _ _ Hfresh) as [Hfresh1 Hfresh2].
    simpl; f_equal; [apply IHt1|apply IHt2]; assumption.
  - simpl; f_equal; apply IHt; assumption.
  - simpl; f_equal; apply IHt; assumption.
  - reflexivity.
  - simpl; f_equal; apply IHt; assumption.
  - destruct (not_in_app_parts _ _ _ Hfresh) as [HfreshN HfreshBS].
    destruct (not_in_app_parts _ _ _ HfreshBS) as [HfreshB HfreshS].
    simpl; f_equal; [apply IHt1|apply IHt2|apply IHt3]; assumption.
  - destruct (not_in_app_parts _ _ _ Hfresh) as [Hfresh1 Hfresh2].
    simpl; f_equal; [apply IHt1|apply IHt2]; assumption.
Qed.

Lemma instantiate_open_type_fvar : forall theta gamma X U t k,
  type_substitution_closed theta -> term_substitution_closed gamma ->
  ~ In X (type_atoms_tm t) ->
  instantiate (theta_update theta X U) gamma
    (open_tm_ty_rec k (Ty_FVar X) t) =
  open_tm_ty_rec k U (instantiate theta gamma t).
Proof.
  intros theta gamma X U t; induction t;
    intros k Htheta Hgamma Hfresh; simpl in *.
  - reflexivity.
  - symmetry; apply open_tm_ty_inert with (K := 0) (k := 0);
      [apply Hgamma|lia].
  - destruct (not_in_app_parts _ _ _ Hfresh) as [HfreshT HfreshBody].
    simpl; f_equal.
    + apply instantiate_ty_open_fvar; assumption.
    + apply IHt; assumption.
  - destruct (not_in_app_parts _ _ _ Hfresh) as [Hfresh1 Hfresh2].
    simpl; f_equal; [apply IHt1|apply IHt2]; assumption.
  - simpl; f_equal; apply IHt; assumption.
  - destruct (not_in_app_parts _ _ _ Hfresh) as [HfreshBody HfreshT].
    simpl; f_equal.
    + apply IHt; assumption.
    + apply instantiate_ty_open_fvar; assumption.
  - reflexivity.
  - simpl; f_equal; apply IHt; assumption.
  - destruct (not_in_app_parts _ _ _ Hfresh) as [HfreshN HfreshBS].
    destruct (not_in_app_parts _ _ _ HfreshBS) as [HfreshB HfreshS].
    simpl; f_equal; [apply IHt1|apply IHt2|apply IHt3]; assumption.
  - destruct (not_in_app_parts _ _ _ Hfresh) as [Hfresh1 Hfresh2].
    simpl; f_equal; [apply IHt1|apply IHt2]; assumption.
Qed.

Lemma has_type_result_closed : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_ty T.
Proof.
  intros Delta Gamma t T H; induction H;
    try solve [constructor; eauto using wf_ty_closed].
  - eapply wf_ty_closed; eassumption.
  - constructor.
    + exact (wf_ty_closed _ _ H).
    + exact (H1 (fresh L) (fresh_not_in L)).
  - inversion IHhas_type1; assumption.
  - apply lc_ty_all.
    pose proof (H0 (fresh L) (fresh_not_in L)) as Hbody.
    eapply open_ty_lc_reverse; exact Hbody.
  - inversion IHhas_type; subst.
    eapply open_ty_lc; [exact H3|exact (wf_ty_closed _ _ H0)].
  - exact IHhas_type2.
  - exact IHhas_type1.
Qed.

Lemma relation_fresh_update : forall T eta rho X candidate v,
  ~ In X (type_atoms T) ->
  (value_relation eta (relation_update rho X candidate) T v <->
   value_relation eta rho T v).
Proof.
  induction T; intros eta rho X candidate v Hfresh; simpl in *.
  - reflexivity.
  - assert (Hneq : Nat.eqb X a = false).
    { apply Nat.eqb_neq; intro Heq; subst; apply Hfresh; auto. }
    unfold relation_update; rewrite Hneq; reflexivity.
  - destruct (not_in_app_parts _ _ _ Hfresh) as [Hfresh1 Hfresh2].
    split; intros [Hv [U [body [Heq Happly]]]].
    + split; [exact Hv|exists U, body; split; [exact Heq|]].
      intros arg Harg.
      apply (proj1 (lift_equiv _ _ _
        (fun w => IHT2 eta rho X candidate w Hfresh2))).
      apply Happly; apply (proj2 (IHT1 eta rho X candidate arg Hfresh1)); exact Harg.
    + split; [exact Hv|exists U, body; split; [exact Heq|]].
      intros arg Harg.
      apply (proj2 (lift_equiv _ _ _
        (fun w => IHT2 eta rho X candidate w Hfresh2))).
      apply Happly; apply (proj1 (IHT1 eta rho X candidate arg Hfresh1)); exact Harg.
  - split; intros [Hv [body [Heq Happly]]].
    + split; [exact Hv|exists body; split; [exact Heq|]].
      intros U b HU.
      apply (proj1 (lift_equiv _ _ _
        (fun w => IHT (b :: eta) rho X candidate w Hfresh))).
      apply Happly; exact HU.
    + split; [exact Hv|exists body; split; [exact Heq|]].
      intros U b HU.
      apply (proj2 (lift_equiv _ _ _
        (fun w => IHT (b :: eta) rho X candidate w Hfresh))).
      apply Happly; exact HU.
  - reflexivity.
Qed.

Lemma context_type_atoms_lookup : forall Gamma x T X,
  lookup_context x Gamma = Some T ->
  In X (type_atoms T) -> In X (context_type_atoms Gamma).
Proof.
  induction Gamma as [|[y U] rest IH]; intros x T X Hlookup Hin;
    simpl in *; [discriminate|].
  destruct (Nat.eqb x y) eqn:Heq.
  - injection Hlookup as <-; apply in_or_app; left; exact Hin.
  - apply in_or_app; right; eapply IH; eassumption.
Qed.

Lemma related_rho_update : forall rho Gamma gamma X candidate,
  ~ In X (context_type_atoms Gamma) ->
  related_substitution rho Gamma gamma ->
  related_substitution (relation_update rho X candidate) Gamma gamma.
Proof.
  intros rho Gamma gamma X candidate Hfresh Hrelated x T Hlookup.
  assert (HfreshT : ~ In X (type_atoms T)).
  { intro Hin; apply Hfresh;
      eapply context_type_atoms_lookup; eassumption. }
  apply (proj2 (relation_fresh_update T [] rho X candidate (gamma x) HfreshT)).
  apply Hrelated with (x := x); assumption.
Qed.

Lemma related_gamma_update : forall rho Gamma gamma x T v,
  related_substitution rho Gamma gamma ->
  value_relation [] rho T v ->
  related_substitution rho (update Gamma x T) (gamma_update gamma x v).
Proof.
  intros rho Gamma gamma x T v Hrelated Hv y U Hlookup.
  unfold lookup_context in Hlookup; simpl in Hlookup.
  destruct (Nat.eqb y x) eqn:Heq.
  - apply Nat.eqb_eq in Heq; subst y.
    injection Hlookup as <-.
    unfold gamma_update; rewrite Nat.eqb_refl; exact Hv.
  - unfold gamma_update; rewrite Nat.eqb_sym; rewrite Heq.
    eapply Hrelated; exact Hlookup.
Qed.

Lemma tapp_candidate_related : forall eta rho T U candidate t,
  locally_closed_ty U ->
  expression_relation eta rho (Ty_All T) t ->
  expression_lifting (value_relation (candidate :: eta) rho T) (tm_tapp t U).
Proof.
  intros eta rho T U candidate t HU [Hlc [Hsn Hall]].
  induction Hsn as [t Hstep IH].
  apply lift_nonvalue.
  - constructor; assumption.
  - intro H; inversion H; subst;
      match goal with Hn : numeric_value (tm_tapp _ _) |- _ => inversion Hn end.
  - intros u Hred; inversion Hred; subst.
    + pose proof (Hall _ (multi_refl _) (v_tabs _ H1)) as Hrelation.
      destruct Hrelation as [_ [body [Heq Happly]]].
      inversion Heq; subst; apply Happly; exact HU.
    + apply IH.
      * exact H1.
      * exact (proj1 (lift_reduct _ _ _
          (conj Hlc (conj (SN_intro _ Hstep) Hall)) H1)).
      * exact (proj2 (proj2 (lift_reduct _ _ _
          (conj Hlc (conj (SN_intro _ Hstep) Hall)) H1))).
Qed.

Theorem fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall theta gamma rho,
    type_substitution_closed theta ->
    term_substitution_closed gamma ->
    related_substitution rho Gamma gamma ->
    expression_relation [] rho T (instantiate theta gamma t).
Proof.
  intros Delta Gamma t T Htyping; induction Htyping;
    intros theta gamma rho Htheta Hgamma Hrelated; simpl.
  - apply lift_value.
    + eapply value_relation_value; eapply Hrelated; eassumption.
    + eapply Hrelated; eassumption.
  - assert (Hlamclosed : locally_closed_tm
        (tm_abs (instantiate_ty theta T1) (instantiate theta gamma t2))).
    { change (locally_closed_tm (instantiate theta gamma (tm_abs T1 t2))).
      apply instantiate_at_closed; try assumption.
      eapply has_type_closed.
      exact (T_Abs L Delta Gamma T1 t2 T2 H H0). }
    apply lift_value.
    + apply v_abs; exact Hlamclosed.
    + simpl; split; [apply v_abs; exact Hlamclosed|].
      exists (instantiate_ty theta T1), (instantiate theta gamma t2).
      split; [reflexivity|].
      intros arg Harg.
      set (x := fresh (L ++ term_atoms t2)).
      assert (HfreshAll : ~ In x (L ++ term_atoms t2)).
      { unfold x; apply fresh_not_in. }
      destruct (not_in_app_parts _ _ _ HfreshAll) as [HnotL HnotBody].
      assert (Hargclosed : locally_closed_tm arg).
      { apply value_closed; eapply value_relation_value; exact Harg. }
      pose proof (H1 x HnotL theta (gamma_update gamma x arg) rho
        Htheta (gamma_update_closed _ _ _ Hgamma Hargclosed)
        (related_gamma_update _ _ _ _ _ _ Hrelated Harg)) as Hbody.
      change (expression_relation [] rho T2
        (instantiate theta (gamma_update gamma x arg)
          (open_tm_rec 0 (tm_fvar x) t2))) in Hbody.
      rewrite (instantiate_open_fvar theta gamma x arg t2 0 Hgamma HnotBody)
        in Hbody.
      exact Hbody.
  - eapply app_related.
    + apply IHHtyping1; assumption.
    + apply IHHtyping2; assumption.
  - assert (Htabclosed : locally_closed_tm (tm_tabs (instantiate theta gamma t))).
    { change (locally_closed_tm (instantiate theta gamma (tm_tabs t))).
      apply instantiate_at_closed; try assumption.
      eapply has_type_closed; exact (T_TAbs L Delta Gamma t T H). }
    assert (HlcT : lc_ty_at 1 T).
    { pose proof (has_type_result_closed _ _ _ _
        (T_TAbs L Delta Gamma t T H)) as HlcAll.
      inversion HlcAll; assumption. }
    apply lift_value.
    + apply v_tabs; exact Htabclosed.
    + simpl; split; [apply v_tabs; exact Htabclosed|].
      exists (instantiate theta gamma t); split; [reflexivity|].
      intros U candidate HU.
      set (X := fresh (((L ++ type_atoms_tm t) ++ type_atoms T)
        ++ context_type_atoms Gamma)).
      assert (HfreshAll : ~ In X (((L ++ type_atoms_tm t) ++ type_atoms T)
        ++ context_type_atoms Gamma)).
      { unfold X; apply fresh_not_in. }
      destruct (not_in_app_parts _ _ _ HfreshAll) as [HfreshLT HfreshGamma].
      destruct (not_in_app_parts _ _ _ HfreshLT) as [HfreshL HfreshT].
      destruct (not_in_app_parts _ _ _ HfreshL) as [HfreshBind HfreshBody].
      pose proof (H0 X HfreshBind (theta_update theta X U) gamma
        (relation_update rho X candidate)
        (theta_update_closed _ _ _ Htheta HU) Hgamma
        (related_rho_update _ _ _ _ _ HfreshGamma Hrelated)) as Hbody.
      change (expression_relation [] (relation_update rho X candidate)
        (open_ty T (Ty_FVar X))
        (instantiate (theta_update theta X U) gamma
          (open_tm_ty_rec 0 (Ty_FVar X) t))) in Hbody.
      rewrite (instantiate_open_type_fvar theta gamma X U t 0
        Htheta Hgamma HfreshBody) in Hbody.
      apply (proj1 (lift_equiv _ _ _
        (fun w => relation_open_fvar T 0 [] rho X candidate w
          HlcT HfreshT eq_refl))) in Hbody.
      exact Hbody.
  - assert (HlcT : lc_ty_at 1 T).
    { pose proof (has_type_result_closed _ _ _ _ Htyping) as HlcAll.
      inversion HlcAll; assumption. }
    assert (HU : locally_closed_ty U) by (eapply wf_ty_closed; eassumption).
    apply (proj1 (lift_equiv _ _ _
      (fun w => relation_open_type T 0 [] rho U
        (type_candidate [] rho U) w HlcT HU eq_refl
        (fun v => iff_refl _)))).
    eapply tapp_candidate_related.
    + apply instantiate_ty_at_closed; assumption.
    + apply IHHtyping; assumption.
  - apply zero_related.
  - apply succ_related; apply IHHtyping; assumption.
  - eapply rec_related.
    + apply IHHtyping1; assumption.
    + apply IHHtyping2; assumption.
    + apply IHHtyping3; assumption.
  - apply choice_related.
    + apply IHHtyping1; assumption.
    + apply IHHtyping2; assumption.
Qed.

Lemma instantiate_ty_identity : forall T,
  instantiate_ty (fun X => Ty_FVar X) T = T.
Proof.
  induction T; simpl; try rewrite IHT1, IHT2;
    try rewrite IHT; reflexivity.
Qed.

Lemma instantiate_identity : forall t,
  instantiate (fun X => Ty_FVar X) (fun x => tm_fvar x) t = t.
Proof.
  induction t; simpl; try rewrite instantiate_ty_identity;
    try rewrite IHt; try rewrite IHt1; try rewrite IHt2;
    try rewrite IHt3; reflexivity.
Qed.

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  intros t T Htyping.
  pose proof (fundamental [] empty t T Htyping
    (fun X => Ty_FVar X) (fun x => tm_fvar x) (fun _ => None)) as Hfund.
  assert (Htheta : type_substitution_closed (fun X => Ty_FVar X)).
  { intro X; constructor. }
  assert (Hgamma : term_substitution_closed (fun x => tm_fvar x)).
  { intro x; constructor. }
  specialize (Hfund Htheta Hgamma).
  assert (Hrelated : related_substitution (fun _ => None) empty
      (fun x => tm_fvar x)).
  { intros x U Hlookup; inversion Hlookup. }
  specialize (Hfund Hrelated).
  rewrite instantiate_identity in Hfund.
  exact (proj1 (proj2 Hfund)).
Qed.

End SystemFNormalizationNondeterminismRecursionMediumTask.
