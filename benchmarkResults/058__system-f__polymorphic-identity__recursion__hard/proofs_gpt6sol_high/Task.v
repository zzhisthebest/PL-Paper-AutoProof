(** System F parametricity benchmark, Hard variant.
    Features: recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFParametricityRecursionHardTask.

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

(** A relation on values is lifted to terms by allowing a finite reduction
    on each side.  The two components of a type-variable environment may be
    instantiated at different closed types. *)
Record relation_assignment := {
  assignment_left : ty;
  assignment_right : ty;
  assignment_rel : tm -> tm -> Prop
}.

Definition relation_environment := atom -> relation_assignment.

Fixpoint related_value
    (T : ty) (bound : list relation_assignment)
    (free : relation_environment) (v1 v2 : tm) {struct T} : Prop :=
  match T with
  | Ty_BVar i =>
      match nth_error bound i with
      | Some a => assignment_rel a v1 v2
      | None => False
      end
  | Ty_FVar X => assignment_rel (free X) v1 v2
  | Ty_Arrow A B =>
      value v1 /\ value v2 /\
      forall w1 w2, related_value A bound free w1 w2 ->
        exists z1 z2,
          tm_app v1 w1 -->* z1 /\ tm_app v2 w2 -->* z2 /\
          related_value B bound free z1 z2
  | Ty_All A =>
      value v1 /\ value v2 /\
      forall U (R : tm -> tm -> Prop),
        locally_closed_ty U ->
        (forall w1 w2, R w1 w2 -> value w1 /\ value w2) ->
        exists z1 z2,
          tm_tapp v1 U -->* z1 /\ tm_tapp v2 U -->* z2 /\
          related_value A
            ({| assignment_left := U; assignment_right := U;
                assignment_rel := R |} :: bound) free z1 z2
  | Ty_Nat =>
      exists n, v1 = numeral n /\ v2 = numeral n
  end.

Definition related_term
    (T : ty) (bound : list relation_assignment)
    (free : relation_environment) (t1 t2 : tm) : Prop :=
  locally_closed_tm t1 /\ locally_closed_tm t2 /\
  exists v1 v2, t1 -->* v1 /\ t2 -->* v2 /\
                related_value T bound free v1 v2.

Definition admissible (a : relation_assignment) : Prop :=
  locally_closed_ty (assignment_left a) /\
  locally_closed_ty (assignment_right a) /\
  forall v1 v2, assignment_rel a v1 v2 -> value v1 /\ value v2.

Lemma numeral_numeric : forall n, numeric_value (numeral n).
Proof. induction n; simpl; constructor; assumption. Qed.

Lemma numeric_is_numeral : forall v, numeric_value v ->
  exists n, v = numeral n.
Proof.
  intros v H; induction H.
  - exists 0; reflexivity.
  - destruct IHnumeric_value as [k ->]. exists (S k); reflexivity.
Qed.

Lemma numeric_closed : forall n, numeric_value n -> locally_closed_tm n.
Proof. intros n H; induction H; unfold locally_closed_tm in *; eauto. Qed.

Lemma value_closed : forall v, value v -> locally_closed_tm v.
Proof.
  intros v H; inversion H; subst; eauto using numeric_closed.
Qed.

Lemma multi_trans : forall a b c, a -->* b -> b -->* c -> a -->* c.
Proof.
  intros a b c Hab; induction Hab; intros Hbc; eauto using multi.
Qed.

Lemma multi_app_left : forall a a' b,
  a -->* a' -> locally_closed_tm b ->
  tm_app a b -->* tm_app a' b.
Proof.
  intros a a' b H; induction H; intros Hb.
  - constructor.
  - eapply multi_step; eauto using step.
Qed.

Lemma multi_app_right : forall a b b',
  value a -> b -->* b' -> tm_app a b -->* tm_app a b'.
Proof.
  intros a b b' Ha H; induction H.
  - constructor.
  - eapply multi_step; eauto using step.
Qed.

Lemma multi_tapp : forall a a' U,
  a -->* a' -> locally_closed_ty U ->
  tm_tapp a U -->* tm_tapp a' U.
Proof.
  intros a a' U H; induction H; intros HU.
  - constructor.
  - eapply multi_step; eauto using step.
Qed.

Lemma multi_succ : forall a a',
  a -->* a' -> tm_succ a -->* tm_succ a'.
Proof.
  intros a a' H; induction H.
  - constructor.
  - eapply multi_step; eauto using step.
Qed.

Lemma multi_rec_arg : forall a a' b s,
  a -->* a' -> locally_closed_tm b -> locally_closed_tm s ->
  tm_natrec a b s -->* tm_natrec a' b s.
Proof.
  intros a a' b s H; induction H; intros Hb Hs.
  - constructor.
  - eapply multi_step; eauto using step.
Qed.

Lemma multi_rec_base : forall n b b' s,
  numeric_value n -> b -->* b' -> locally_closed_tm s ->
  tm_natrec n b s -->* tm_natrec n b' s.
Proof.
  intros n b b' s Hn H; induction H; intros Hs.
  - constructor.
  - eapply multi_step; eauto using step.
Qed.

Lemma multi_rec_step : forall n b s s',
  numeric_value n -> value b -> s -->* s' ->
  tm_natrec n b s -->* tm_natrec n b s'.
Proof.
  intros n b s s' Hn Hb H; induction H.
  - constructor.
  - eapply multi_step; eauto using step.
Qed.

Definition fresh_atom (xs : list atom) : atom :=
  S (fold_right Nat.max 0 xs).

Lemma fresh_atom_not_in : forall xs, ~ In (fresh_atom xs) xs.
Proof.
  assert (Hbound : forall xs x, In x xs -> x <= fold_right Nat.max 0 xs).
  { induction xs as [|y ys IH]; intros x Hin; simpl in *.
    - contradiction.
    - destruct Hin as [-> | Hin]; [lia | specialize (IH x Hin); lia]. }
  unfold fresh_atom; intros xs Hin.
  specialize (Hbound xs (S (fold_right Nat.max 0 xs)) Hin). lia.
Qed.

Lemma lc_ty_open_reverse : forall T k X,
  lc_ty_at k (open_ty_rec k (Ty_FVar X) T) ->
  lc_ty_at (S k) T.
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

Lemma wf_ty_closed : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H; induction H.
  - constructor.
  - constructor; assumption.
  - unfold locally_closed_ty in *.
    specialize (H (fresh_atom L) (fresh_atom_not_in L)).
    specialize (H0 (fresh_atom L) (fresh_atom_not_in L)).
    constructor. eapply lc_ty_open_reverse; exact H0.
  - constructor.
Qed.

Lemma lc_tm_open_reverse : forall t K k x,
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) ->
  lc_tm_at K (S k) t.
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
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
Qed.

Lemma lc_tm_ty_open_reverse : forall t K k X,
  lc_tm_at K k (open_tm_ty_rec K (Ty_FVar X) t) ->
  lc_tm_at (S K) k t.
Proof.
  induction t; intros K k X H; simpl in H.
  - inversion H; subst; constructor; assumption.
  - constructor.
  - inversion H; subst; constructor.
    + eapply lc_ty_open_reverse; eauto.
    + eauto.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto using lc_ty_open_reverse.
  - constructor.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
Qed.

Lemma has_type_closed : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T H; induction H; unfold locally_closed_tm in *.
  - constructor.
  - constructor.
    + apply wf_ty_closed in H. exact H.
    + specialize (H0 (fresh_atom L) (fresh_atom_not_in L)).
      specialize (H1 (fresh_atom L) (fresh_atom_not_in L)).
      eapply lc_tm_open_reverse; exact H1.
  - constructor; assumption.
  - constructor.
    specialize (H (fresh_atom L) (fresh_atom_not_in L)).
    specialize (H0 (fresh_atom L) (fresh_atom_not_in L)).
    eapply lc_tm_ty_open_reverse; exact H0.
  - constructor; [assumption | exact (wf_ty_closed _ _ H0)].
  - constructor.
  - constructor; assumption.
  - constructor; assumption.
Qed.

Fixpoint instantiate_ty (rho : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => rho X
  | Ty_Arrow A B => Ty_Arrow (instantiate_ty rho A) (instantiate_ty rho B)
  | Ty_All A => Ty_All (instantiate_ty rho A)
  | Ty_Nat => Ty_Nat
  end.

Fixpoint instantiate_tm
    (rho : atom -> ty) (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_abs A b => tm_abs (instantiate_ty rho A) (instantiate_tm rho sigma b)
  | tm_app a b => tm_app (instantiate_tm rho sigma a) (instantiate_tm rho sigma b)
  | tm_tabs b => tm_tabs (instantiate_tm rho sigma b)
  | tm_tapp a A => tm_tapp (instantiate_tm rho sigma a) (instantiate_ty rho A)
  | tm_zero => tm_zero
  | tm_succ a => tm_succ (instantiate_tm rho sigma a)
  | tm_natrec n b s =>
      tm_natrec (instantiate_tm rho sigma n)
                (instantiate_tm rho sigma b)
                (instantiate_tm rho sigma s)
  end.

Fixpoint free_ty_atoms (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow A B => free_ty_atoms A ++ free_ty_atoms B
  | Ty_All A => free_ty_atoms A
  | Ty_Nat => []
  end.

Fixpoint free_tm_atoms (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs _ b => free_tm_atoms b
  | tm_app a b => free_tm_atoms a ++ free_tm_atoms b
  | tm_tabs b => free_tm_atoms b
  | tm_tapp a _ => free_tm_atoms a
  | tm_zero => []
  | tm_succ a => free_tm_atoms a
  | tm_natrec n b s => free_tm_atoms n ++ free_tm_atoms b ++ free_tm_atoms s
  end.

Fixpoint free_tm_ty_atoms (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_fvar _ | tm_zero => []
  | tm_abs A b => free_ty_atoms A ++ free_tm_ty_atoms b
  | tm_app a b => free_tm_ty_atoms a ++ free_tm_ty_atoms b
  | tm_tabs b => free_tm_ty_atoms b
  | tm_tapp a A => free_tm_ty_atoms a ++ free_ty_atoms A
  | tm_succ a => free_tm_ty_atoms a
  | tm_natrec n b s =>
      free_tm_ty_atoms n ++ free_tm_ty_atoms b ++ free_tm_ty_atoms s
  end.

Definition update_ty_map (rho : atom -> ty) (X : atom) (U : ty) :=
  fun Y => if Nat.eqb X Y then U else rho Y.

Definition update_tm_map (sigma : atom -> tm) (x : atom) (v : tm) :=
  fun y => if Nat.eqb x y then v else sigma y.

Definition left_types (theta : relation_environment) : atom -> ty :=
  fun X => assignment_left (theta X).
Definition right_types (theta : relation_environment) : atom -> ty :=
  fun X => assignment_right (theta X).

Definition related_substitutions
    (Gamma : context) (theta : relation_environment)
    (sigma1 sigma2 : atom -> tm) : Prop :=
  (forall x, value (sigma1 x) /\ value (sigma2 x)) /\
  (forall x A, lookup_context x Gamma = Some A ->
      related_value A [] theta (sigma1 x) (sigma2 x)).

Definition admissible_environment (theta : relation_environment) : Prop :=
  forall X, admissible (theta X).

Lemma lc_ty_weaken : forall T k k',
  lc_ty_at k T -> k <= k' -> lc_ty_at k' T.
Proof.
  intros T k k' H; revert k' ; induction H; intros k' Hle.
  - constructor; lia.
  - constructor.
  - constructor; eauto.
  - apply lc_ty_all. apply IHlc_ty_at. lia.
  - constructor.
Qed.

Lemma lc_tm_weaken : forall t K k K' k',
  lc_tm_at K k t -> K <= K' -> k <= k' -> lc_tm_at K' k' t.
Proof.
  intros t K k K' k' H; revert K' k'; induction H;
    intros K' k' HK Hk.
  - constructor; lia.
  - constructor.
  - apply lc_tm_abs.
    + eapply lc_ty_weaken; eauto.
    + apply IHlc_tm_at; lia.
  - constructor; eauto.
  - apply lc_tm_tabs. apply IHlc_tm_at; lia.
  - constructor; eauto using lc_ty_weaken.
  - constructor.
  - constructor; eauto.
  - constructor; eauto.
Qed.

Lemma instantiate_ty_lc : forall rho T k,
  (forall X, locally_closed_ty (rho X)) ->
  lc_ty_at k T -> lc_ty_at k (instantiate_ty rho T).
Proof.
  intros rho T k Hr H; induction H; simpl.
  - constructor; assumption.
  - apply lc_ty_weaken with (k := 0); [exact (Hr X) | lia].
  - constructor; assumption.
  - constructor; assumption.
  - constructor.
Qed.

Lemma instantiate_tm_lc : forall rho sigma t K k,
  (forall X, locally_closed_ty (rho X)) ->
  (forall x, locally_closed_tm (sigma x)) ->
  lc_tm_at K k t ->
  lc_tm_at K k (instantiate_tm rho sigma t).
Proof.
  intros rho sigma t K k Hr Hs H; induction H; simpl;
    try (constructor; eauto using instantiate_ty_lc).
  apply lc_tm_weaken with (K := 0) (k := 0);
    [exact (Hs x) | lia | lia].
Qed.

Lemma open_ty_closed : forall T k U,
  lc_ty_at k T -> open_ty_rec k U T = T.
Proof.
  intros T k U H; induction H; simpl; try (f_equal; assumption); auto.
  destruct (Nat.eqb k i) eqn:E; [apply Nat.eqb_eq in E; lia | reflexivity].
Qed.

Lemma open_tm_closed : forall t K k u,
  lc_tm_at K k t -> open_tm_rec k u t = t.
Proof.
  intros t K k u H; induction H; simpl; try (f_equal; assumption); auto.
  destruct (Nat.eqb k i) eqn:E; [apply Nat.eqb_eq in E; lia | reflexivity].
Qed.

Lemma open_tm_ty_closed : forall t K k U,
  lc_tm_at K k t -> open_tm_ty_rec K U t = t.
Proof.
  intros t K k U H; induction H; simpl;
    try (f_equal; eauto using open_ty_closed); auto.
Qed.

Lemma related_value_bound_ext : forall T k b1 b2 theta v1 v2,
  lc_ty_at k T ->
  (forall i, i < k -> nth_error b1 i = nth_error b2 i) ->
  (related_value T b1 theta v1 v2 <->
   related_value T b2 theta v1 v2).
Proof.
  intros T k b1 b2 theta v1 v2 Hlc.
  revert b1 b2 theta v1 v2; induction Hlc;
    intros b1 b2 theta v1 v2 Heq; simpl.
  - rewrite Heq by assumption. reflexivity.
  - reflexivity.
  - split; intros [Hv1 [Hv2 Hfun]]; repeat split; try assumption;
      intros w1 w2 Hw.
    + apply (proj2 (IHHlc1 b1 b2 theta w1 w2 Heq)) in Hw.
      specialize (Hfun w1 w2 Hw) as [z1 [z2 [H1 [H2 Hz]]]].
      exists z1, z2; repeat split; try assumption.
      apply (proj1 (IHHlc2 b1 b2 theta z1 z2 Heq)); assumption.
    + apply (proj1 (IHHlc1 b1 b2 theta w1 w2 Heq)) in Hw.
      specialize (Hfun w1 w2 Hw) as [z1 [z2 [H1 [H2 Hz]]]].
      exists z1, z2; repeat split; try assumption.
      apply (proj2 (IHHlc2 b1 b2 theta z1 z2 Heq)); assumption.
  - assert (Hcons : forall a i, i < S k ->
        nth_error (a :: b1) i = nth_error (a :: b2) i).
    { intros a [|i] Hi; simpl; [reflexivity | apply Heq; lia]. }
    split; intros [Hv1 [Hv2 Hfun]]; repeat split; try assumption;
      intros U R HU HR.
    + specialize (Hfun U R HU HR)
        as [z1 [z2 [H1 [H2 Hz]]]].
      exists z1, z2; repeat split; try assumption.
      apply (proj1 (IHHlc ( _ :: b1) (_ :: b2) theta z1 z2
        (Hcons _))); exact Hz.
    + specialize (Hfun U R HU HR)
        as [z1 [z2 [H1 [H2 Hz]]]].
      exists z1, z2; repeat split; try assumption.
      apply (proj2 (IHHlc ( _ :: b1) (_ :: b2) theta z1 z2
        (Hcons _))); exact Hz.
  - reflexivity.
Qed.

Definition diagonal_assignment (U : ty) (theta : relation_environment) :
    relation_assignment :=
  {| assignment_left := U; assignment_right := U;
     assignment_rel := related_value U [] theta |}.

Lemma related_value_open_ty : forall T k U b theta a v1 v2,
  lc_ty_at (S k) T -> locally_closed_ty U -> length b = k ->
  assignment_rel a = related_value U [] theta ->
  (related_value (open_ty_rec k U T) b theta v1 v2 <->
   related_value T (b ++ [a]) theta v1 v2).
Proof.
  induction T; intros k U b theta relA v1 v2 Hlc HU Hlen Hrel;
    simpl in *.
  - inversion Hlc; clear Hlc.
    destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. rewrite <- E.
      rewrite nth_error_app2 by lia.
      rewrite Hlen, Nat.sub_diag. simpl.
      rewrite Hrel.
      apply related_value_bound_ext with (k := 0); auto.
      intros j Hi; lia.
    + apply Nat.eqb_neq in E.
      assert (n < k) by lia.
      rewrite nth_error_app1 by lia. reflexivity.
  - reflexivity.
  - inversion Hlc; clear Hlc.
    split; intros [Hv1 [Hv2 Hfun]]; repeat split; try assumption;
      intros w1 w2 Hw.
    + apply (proj2 (IHT1 k U b theta relA w1 w2 H2 HU Hlen Hrel)) in Hw.
      specialize (Hfun w1 w2 Hw) as [z1 [z2 [Hr1 [Hr2 Hz]]]].
      exists z1, z2; repeat split; try assumption.
      apply (proj1 (IHT2 k U b theta relA z1 z2 H3 HU Hlen Hrel)); assumption.
    + apply (proj1 (IHT1 k U b theta relA w1 w2 H2 HU Hlen Hrel)) in Hw.
      specialize (Hfun w1 w2 Hw) as [z1 [z2 [Hr1 [Hr2 Hz]]]].
      exists z1, z2; repeat split; try assumption.
      apply (proj2 (IHT2 k U b theta relA z1 z2 H3 HU Hlen Hrel)); assumption.
  - inversion Hlc; clear Hlc.
    split; intros [Hv1 [Hv2 Hfun]]; repeat split; try assumption;
      intros U0 R HU0 HR.
    + specialize (Hfun U0 R HU0 HR)
        as [z1 [z2 [Hr1 [Hr2 Hz]]]].
      exists z1, z2; repeat split; try assumption.
      apply (proj1 (IHT (S k) U
        ({| assignment_left := U0; assignment_right := U0;
            assignment_rel := R |} :: b) theta relA z1 z2 H1 HU
        (f_equal S Hlen) Hrel)); exact Hz.
    + specialize (Hfun U0 R HU0 HR)
        as [z1 [z2 [Hr1 [Hr2 Hz]]]].
      exists z1, z2; repeat split; try assumption.
      apply (proj2 (IHT (S k) U
        ({| assignment_left := U0; assignment_right := U0;
            assignment_rel := R |} :: b) theta relA z1 z2 H1 HU
        (f_equal S Hlen) Hrel)); exact Hz.
  - reflexivity.
Qed.

Definition update_relation_environment
    (theta : relation_environment) (X : atom)
    (a : relation_assignment) : relation_environment :=
  fun Y => if Nat.eqb X Y then a else theta Y.

Lemma related_value_open_fvar : forall T k X b theta relA v1 v2,
  lc_ty_at (S k) T -> length b = k ->
  ~ In X (free_ty_atoms T) ->
  (related_value (open_ty_rec k (Ty_FVar X) T) b
       (update_relation_environment theta X relA) v1 v2 <->
   related_value T (b ++ [relA]) theta v1 v2).
Proof.
  induction T; intros k X b theta relA v1 v2 Hlc Hlen Hfresh;
    simpl in *.
  - inversion Hlc; clear Hlc.
    destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. rewrite <- E.
      rewrite nth_error_app2 by lia.
      rewrite Hlen, Nat.sub_diag. simpl.
      unfold update_relation_environment. rewrite Nat.eqb_refl.
      reflexivity.
    + apply Nat.eqb_neq in E. assert (n < k) by lia.
      rewrite nth_error_app1 by lia. reflexivity.
  - unfold update_relation_environment.
    assert (X <> a) by (intro Heq; subst; apply Hfresh; left; reflexivity).
    destruct (Nat.eqb X a) eqn:E;
      [apply Nat.eqb_eq in E; contradiction | reflexivity].
  - inversion Hlc; clear Hlc.
    assert (Hfresh1 : ~ In X (free_ty_atoms T1)).
    { intro Hin; apply Hfresh; apply in_or_app; left; exact Hin. }
    assert (Hfresh2 : ~ In X (free_ty_atoms T2)).
    { intro Hin; apply Hfresh; apply in_or_app; right; exact Hin. }
    split; intros [Hv1 [Hv2 Hfun]]; repeat split; try assumption;
      intros w1 w2 Hw.
    + apply (proj2 (IHT1 k X b theta relA w1 w2 H2 Hlen Hfresh1)) in Hw.
      specialize (Hfun w1 w2 Hw) as [z1 [z2 [Hr1 [Hr2 Hz]]]].
      exists z1, z2; repeat split; try assumption.
      apply (proj1 (IHT2 k X b theta relA z1 z2 H3 Hlen Hfresh2)); assumption.
    + apply (proj1 (IHT1 k X b theta relA w1 w2 H2 Hlen Hfresh1)) in Hw.
      specialize (Hfun w1 w2 Hw) as [z1 [z2 [Hr1 [Hr2 Hz]]]].
      exists z1, z2; repeat split; try assumption.
      apply (proj2 (IHT2 k X b theta relA z1 z2 H3 Hlen Hfresh2)); assumption.
  - inversion Hlc; clear Hlc.
    split; intros [Hv1 [Hv2 Hfun]]; repeat split; try assumption;
      intros U R HU HR.
    + specialize (Hfun U R HU HR) as [z1 [z2 [Hr1 [Hr2 Hz]]]].
      exists z1, z2; repeat split; try assumption.
      apply (proj1 (IHT (S k) X
        ({| assignment_left := U; assignment_right := U;
            assignment_rel := R |} :: b) theta relA z1 z2 H1
        (f_equal S Hlen) Hfresh)); exact Hz.
    + specialize (Hfun U R HU HR) as [z1 [z2 [Hr1 [Hr2 Hz]]]].
      exists z1, z2; repeat split; try assumption.
      apply (proj2 (IHT (S k) X
        ({| assignment_left := U; assignment_right := U;
            assignment_rel := R |} :: b) theta relA z1 z2 H1
        (f_equal S Hlen) Hfresh)); exact Hz.
  - reflexivity.
Qed.

Lemma instantiate_ty_open : forall T k X rho U,
  ~ In X (free_ty_atoms T) ->
  (forall Y, locally_closed_ty (rho Y)) ->
  instantiate_ty (update_ty_map rho X U)
    (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k U (instantiate_ty rho T).
Proof.
  induction T; intros k X rho U Hfresh Hr; simpl in *.
  - destruct (Nat.eqb k n); simpl;
      [unfold update_ty_map; rewrite Nat.eqb_refl |]; reflexivity.
  - unfold update_ty_map.
    assert (X <> a) by (intro Heq; subst; apply Hfresh; left; reflexivity).
    destruct (Nat.eqb X a) eqn:E;
      [apply Nat.eqb_eq in E; contradiction |].
    symmetry. apply open_ty_closed.
    apply lc_ty_weaken with (k := 0); [apply Hr | lia].
  - assert (H1 : ~ In X (free_ty_atoms T1)).
    { intro Hin; apply Hfresh; apply in_or_app; left; exact Hin. }
    assert (H2 : ~ In X (free_ty_atoms T2)).
    { intro Hin; apply Hfresh; apply in_or_app; right; exact Hin. }
    f_equal; eauto.
  - f_equal. apply IHT; auto.
  - reflexivity.
Qed.

Lemma instantiate_ty_open_general : forall T k rho U,
  (forall Y, locally_closed_ty (rho Y)) ->
  instantiate_ty rho (open_ty_rec k U T) =
  open_ty_rec k (instantiate_ty rho U) (instantiate_ty rho T).
Proof.
  induction T; intros k rho U Hr; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. apply open_ty_closed.
    apply lc_ty_weaken with (k := 0); [apply Hr | lia].
  - f_equal; eauto.
  - f_equal; eauto.
  - reflexivity.
Qed.

Lemma instantiate_tm_ty_open_general : forall t k rho sigma U,
  (forall Y, locally_closed_ty (rho Y)) ->
  (forall y, locally_closed_tm (sigma y)) ->
  instantiate_tm rho sigma (open_tm_ty_rec k U t) =
  open_tm_ty_rec k (instantiate_ty rho U) (instantiate_tm rho sigma t).
Proof.
  induction t; intros k rho sigma U Hr Hs; simpl.
  - reflexivity.
  - symmetry. apply (open_tm_ty_closed (sigma a) k 0
      (instantiate_ty rho U)).
    apply lc_tm_weaken with (K := 0) (k := 0);
      [apply Hs | lia | lia].
  - f_equal; [apply instantiate_ty_open_general | apply IHt]; auto.
  - f_equal; eauto.
  - f_equal. apply IHt; auto.
  - f_equal; [apply IHt | apply instantiate_ty_open_general]; auto.
  - reflexivity.
  - f_equal. apply IHt; auto.
  - f_equal; eauto.
Qed.

Lemma instantiate_tm_ty_open : forall t k X rho sigma U,
  ~ In X (free_tm_ty_atoms t) ->
  (forall Y, locally_closed_ty (rho Y)) ->
  (forall y, locally_closed_tm (sigma y)) ->
  instantiate_tm (update_ty_map rho X U) sigma
    (open_tm_ty_rec k (Ty_FVar X) t) =
  open_tm_ty_rec k U (instantiate_tm rho sigma t).
Proof.
  induction t; intros k X rho sigma U Hfresh Hr Hs; simpl in *.
  - reflexivity.
  - symmetry. apply (open_tm_ty_closed (sigma a) k 0 U).
    apply lc_tm_weaken with (K := 0) (k := 0);
      [apply Hs | lia | lia].
  - assert (H1 : ~ In X (free_ty_atoms t)).
    { intro Hin; apply Hfresh; apply in_or_app; left; exact Hin. }
    assert (H2 : ~ In X (free_tm_ty_atoms t0)).
    { intro Hin; apply Hfresh; apply in_or_app; right; exact Hin. }
    f_equal; [apply instantiate_ty_open | apply IHt]; auto.
  - assert (H1 : ~ In X (free_tm_ty_atoms t1)).
    { intro Hin; apply Hfresh; apply in_or_app; left; exact Hin. }
    assert (H2 : ~ In X (free_tm_ty_atoms t2)).
    { intro Hin; apply Hfresh; apply in_or_app; right; exact Hin. }
    f_equal; eauto.
  - f_equal. apply IHt; auto.
  - assert (H1 : ~ In X (free_tm_ty_atoms t)).
    { intro Hin; apply Hfresh; apply in_or_app; left; exact Hin. }
    assert (H2 : ~ In X (free_ty_atoms t0)).
    { intro Hin; apply Hfresh; apply in_or_app; right; exact Hin. }
    f_equal; [apply IHt | apply instantiate_ty_open]; auto.
  - reflexivity.
  - f_equal. apply IHt; auto.
  - assert (Hn : ~ In X (free_tm_ty_atoms t1)).
    { intro Hin; apply Hfresh; apply in_or_app; left; exact Hin. }
    assert (Hb : ~ In X (free_tm_ty_atoms t2)).
    { intro Hin; apply Hfresh; apply in_or_app; right.
      apply in_or_app; left; exact Hin. }
    assert (Hs' : ~ In X (free_tm_ty_atoms t3)).
    { intro Hin; apply Hfresh; apply in_or_app; right.
      apply in_or_app; right; exact Hin. }
    f_equal; eauto.
Qed.

Lemma instantiate_tm_open : forall t k x rho sigma v,
  ~ In x (free_tm_atoms t) ->
  (forall y, locally_closed_tm (sigma y)) ->
  instantiate_tm rho (update_tm_map sigma x v)
    (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k v (instantiate_tm rho sigma t).
Proof.
  induction t; intros k x rho sigma v Hfresh Hs; simpl in *.
  - destruct (Nat.eqb k n) eqn:E; simpl.
    + unfold update_tm_map; rewrite Nat.eqb_refl; reflexivity.
    + reflexivity.
  - unfold update_tm_map.
    assert (x <> a) by (intro Heq; subst; apply Hfresh; left; reflexivity).
    destruct (Nat.eqb x a) eqn:E;
      [apply Nat.eqb_eq in E; contradiction |].
    symmetry. apply (open_tm_closed (sigma a) 0 k v).
    apply lc_tm_weaken with (K := 0) (k := 0);
      [apply Hs | lia | lia].
  - f_equal. apply IHt; auto.
  - assert (H1 : ~ In x (free_tm_atoms t1)).
    { intro Hin; apply Hfresh; apply in_or_app; left; exact Hin. }
    assert (H2 : ~ In x (free_tm_atoms t2)).
    { intro Hin; apply Hfresh; apply in_or_app; right; exact Hin. }
    f_equal; eauto.
  - f_equal. apply IHt; auto.
  - f_equal. apply IHt; auto.
  - reflexivity.
  - f_equal. apply IHt; auto.
  - assert (Hn : ~ In x (free_tm_atoms t1)).
    { intro Hin; apply Hfresh; apply in_or_app; left; exact Hin. }
    assert (Hb : ~ In x (free_tm_atoms t2)).
    { intro Hin; apply Hfresh; apply in_or_app; right.
      apply in_or_app; left; exact Hin. }
    assert (Hs' : ~ In x (free_tm_atoms t3)).
    { intro Hin; apply Hfresh; apply in_or_app; right.
      apply in_or_app; right; exact Hin. }
    f_equal; eauto.
Qed.

Lemma related_value_free_ext : forall T b theta X a v1 v2,
  ~ In X (free_ty_atoms T) ->
  (related_value T b (update_relation_environment theta X a) v1 v2 <->
   related_value T b theta v1 v2).
Proof.
  induction T; intros b theta X relA v1 v2 Hfresh; simpl in *.
  - reflexivity.
  - unfold update_relation_environment.
    assert (X <> a) by (intro Heq; subst; apply Hfresh; left; reflexivity).
    destruct (Nat.eqb X a) eqn:E;
      [apply Nat.eqb_eq in E; contradiction | reflexivity].
  - assert (H1 : ~ In X (free_ty_atoms T1)).
    { intro Hin; apply Hfresh; apply in_or_app; left; exact Hin. }
    assert (H2 : ~ In X (free_ty_atoms T2)).
    { intro Hin; apply Hfresh; apply in_or_app; right; exact Hin. }
    split; intros [Hv1 [Hv2 Hfun]]; repeat split; try assumption;
      intros w1 w2 Hw.
    + apply (proj2 (IHT1 b theta X relA w1 w2 H1)) in Hw.
      specialize (Hfun w1 w2 Hw) as [z1 [z2 [Hr1 [Hr2 Hz]]]].
      exists z1, z2; repeat split; try assumption.
      apply (proj1 (IHT2 b theta X relA z1 z2 H2)); assumption.
    + apply (proj1 (IHT1 b theta X relA w1 w2 H1)) in Hw.
      specialize (Hfun w1 w2 Hw) as [z1 [z2 [Hr1 [Hr2 Hz]]]].
      exists z1, z2; repeat split; try assumption.
      apply (proj2 (IHT2 b theta X relA z1 z2 H2)); assumption.
  - split; intros [Hv1 [Hv2 Hfun]]; repeat split; try assumption;
      intros U R HU HR.
    + specialize (Hfun U R HU HR) as [z1 [z2 [Hr1 [Hr2 Hz]]]].
      exists z1, z2; repeat split; try assumption.
      apply (proj1 (IHT
        ({| assignment_left := U; assignment_right := U;
            assignment_rel := R |} :: b) theta X relA z1 z2 Hfresh)); assumption.
    + specialize (Hfun U R HU HR) as [z1 [z2 [Hr1 [Hr2 Hz]]]].
      exists z1, z2; repeat split; try assumption.
      apply (proj2 (IHT
        ({| assignment_left := U; assignment_right := U;
            assignment_rel := R |} :: b) theta X relA z1 z2 Hfresh)); assumption.
  - reflexivity.
Qed.

Lemma related_value_is_value : forall T b theta v1 v2,
  Forall admissible b -> admissible_environment theta ->
  related_value T b theta v1 v2 -> value v1 /\ value v2.
Proof.
  induction T; intros b theta v1 v2 Hb Htheta Hrel; simpl in Hrel.
  - destruct (nth_error b n) as [a|] eqn:E; [|contradiction].
    apply nth_error_In in E.
    apply Forall_forall with (x := a) in Hb; [|assumption].
    destruct Hb as [_ [_ Hgood]]. apply Hgood; exact Hrel.
  - specialize (Htheta a). destruct Htheta as [_ [_ Hgood]].
    apply Hgood; exact Hrel.
  - tauto.
  - tauto.
  - destruct Hrel as [n [-> ->]]. split; constructor; apply numeral_numeric.
Qed.

Lemma instantiate_closed : forall Delta Gamma t T theta sigma,
  has_type Delta Gamma t T ->
  admissible_environment theta ->
  (forall x, value (sigma x)) ->
  locally_closed_tm (instantiate_tm (left_types theta) sigma t).
Proof.
  intros Delta Gamma t T theta sigma Hty Htheta Hsigma.
  apply instantiate_tm_lc.
  - intro X. destruct (Htheta X) as [H _]. exact H.
  - intro x. apply value_closed, Hsigma.
  - apply has_type_closed in Hty. exact Hty.
Qed.

Fixpoint context_keys (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (x, _) :: Gamma' => x :: context_keys Gamma'
  end.

Fixpoint context_type_atoms (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (_, A) :: Gamma' => free_ty_atoms A ++ context_type_atoms Gamma'
  end.

Lemma lookup_fresh_type : forall Gamma x A X,
  lookup_context x Gamma = Some A ->
  ~ In X (context_type_atoms Gamma) ->
  ~ In X (free_ty_atoms A).
Proof.
  induction Gamma as [|[y B] Gamma IH]; intros x A X Hlook Hfresh;
    simpl in *; [discriminate |].
  destruct (Nat.eqb x y) eqn:E.
  - inversion Hlook; subst. intro Hin. apply Hfresh.
    apply in_or_app; left; exact Hin.
  - eapply IH; [exact Hlook |].
    intro Hin; apply Hfresh; apply in_or_app; right; exact Hin.
Qed.

Lemma related_substitutions_type_extend : forall Gamma theta sigma1 sigma2 X a,
  related_substitutions Gamma theta sigma1 sigma2 ->
  ~ In X (context_type_atoms Gamma) ->
  related_substitutions Gamma (update_relation_environment theta X a)
    sigma1 sigma2.
Proof.
  intros Gamma theta sigma1 sigma2 X a [Hvalues Hlookup] Hfresh.
  split; [exact Hvalues |].
  intros x A Hlook.
  apply (proj2 (related_value_free_ext A [] theta X a
    (sigma1 x) (sigma2 x) (lookup_fresh_type Gamma x A X Hlook Hfresh))).
  apply Hlookup; exact Hlook.
Qed.

Lemma related_substitutions_term_extend : forall Gamma theta sigma1 sigma2 x A w1 w2,
  related_substitutions Gamma theta sigma1 sigma2 ->
  ~ In x (context_keys Gamma) ->
  related_value A [] theta w1 w2 ->
  admissible_environment theta ->
  related_substitutions ((x,A)::Gamma) theta
    (update_tm_map sigma1 x w1) (update_tm_map sigma2 x w2).
Proof.
  intros Gamma theta sigma1 sigma2 x A w1 w2 [Hvalues Hlookup]
    Hfresh Hrel Htheta.
  assert (Hw : value w1 /\ value w2).
  { eapply related_value_is_value; eauto. }
  split.
  - intro y. unfold update_tm_map.
    destruct (Nat.eqb x y); [exact Hw | apply Hvalues].
  - intros y B Hlook. simpl in Hlook.
    destruct (Nat.eqb y x) eqn:E.
    + apply Nat.eqb_eq in E; subst. inversion Hlook; subst.
      unfold update_tm_map. rewrite Nat.eqb_refl. exact Hrel.
    + apply Nat.eqb_neq in E.
      unfold update_tm_map.
      assert (Nat.eqb x y = false) by (apply Nat.eqb_neq; lia).
      rewrite H. apply Hlookup; exact Hlook.
Qed.

Lemma related_natrec_values : forall T theta n b1 b2 s1 s2,
  admissible_environment theta ->
  related_value T [] theta b1 b2 ->
  related_value (Ty_Arrow Ty_Nat (Ty_Arrow T T)) [] theta s1 s2 ->
  exists z1 z2,
    tm_natrec (numeral n) b1 s1 -->* z1 /\
    tm_natrec (numeral n) b2 s2 -->* z2 /\
    related_value T [] theta z1 z2.
Proof.
  intros T theta n; induction n as [|n IH]; intros b1 b2 s1 s2
    Htheta Hb Hs.
  - destruct (related_value_is_value T [] theta b1 b2
      (Forall_nil _) Htheta Hb) as [Hbv1 Hbv2].
    destruct Hs as [Hsv1 [Hsv2 _]].
    exists b1, b2; repeat split; try assumption.
    + apply multi_step with (y := b1);
        [apply ST_RecZero; assumption | constructor].
    + apply multi_step with (y := b2);
        [apply ST_RecZero; assumption | constructor].
  - destruct (related_value_is_value T [] theta b1 b2
      (Forall_nil _) Htheta Hb) as [Hbv1 Hbv2].
    pose proof Hs as Hs_original.
    destruct Hs as [Hsv1 [Hsv2 Hfun]].
    assert (Hnum : related_value Ty_Nat [] theta
        (numeral n) (numeral n)).
    { simpl. exists n; auto. }
    specialize (Hfun (numeral n) (numeral n) Hnum)
      as [f1 [f2 [Hf1 [Hf2 Hf]]]].
    destruct (related_value_is_value (Ty_Arrow T T) [] theta f1 f2
      (Forall_nil _) Htheta Hf) as [Hfv1 Hfv2].
    specialize (IH b1 b2 s1 s2 Htheta Hb Hs_original)
      as [r1 [r2 [Hr1 [Hr2 Hr]]]].
    destruct Hf as [_ [_ Happly]].
    specialize (Happly r1 r2 Hr) as [z1 [z2 [Hz1 [Hz2 Hz]]]].
    exists z1, z2; repeat split; try assumption.
    + eapply multi_step.
      * apply ST_RecSucc; try assumption.
        apply numeral_numeric.
      * eapply multi_trans.
        -- apply multi_app_left.
           ++ exact Hf1.
           ++ unfold locally_closed_tm. constructor.
              ** exact (numeric_closed _ (numeral_numeric n)).
              ** exact (value_closed _ Hbv1).
              ** exact (value_closed _ Hsv1).
        -- eapply multi_trans.
           ++ apply multi_app_right; [exact Hfv1 | exact Hr1].
           ++ exact Hz1.
    + eapply multi_step.
      * apply ST_RecSucc; try assumption.
        apply numeral_numeric.
      * eapply multi_trans.
        -- apply multi_app_left.
           ++ exact Hf2.
           ++ unfold locally_closed_tm. constructor.
              ** exact (numeric_closed _ (numeral_numeric n)).
              ** exact (value_closed _ Hbv2).
              ** exact (value_closed _ Hsv2).
        -- eapply multi_trans.
           ++ apply multi_app_right; [exact Hfv2 | exact Hr2].
           ++ exact Hz2.
Qed.

Lemma lc_ty_open : forall T k U,
  lc_ty_at (S k) T -> locally_closed_ty U ->
  lc_ty_at k (open_ty_rec k U T).
Proof.
  induction T; intros k U Hlc HU; simpl in *.
  - inversion Hlc; clear Hlc.
    destruct (Nat.eqb k n) eqn:E.
    + apply lc_ty_weaken with (k := 0); [exact HU | lia].
    + apply Nat.eqb_neq in E. constructor; lia.
  - constructor.
  - inversion Hlc; clear Hlc. constructor; eauto.
  - inversion Hlc; clear Hlc. constructor; eauto.
  - constructor.
Qed.

Lemma has_type_result_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_ty T.
Proof.
  intros Delta Gamma t T Hty; induction Hty;
    unfold locally_closed_ty in *.
  - exact (wf_ty_closed _ _ H0).
  - constructor; [exact (wf_ty_closed _ _ H) |].
    specialize (H0 (fresh_atom L) (fresh_atom_not_in L)).
    specialize (H1 (fresh_atom L) (fresh_atom_not_in L)).
    exact H1.
  - inversion IHHty1; assumption.
  - constructor.
    specialize (H (fresh_atom L) (fresh_atom_not_in L)).
    specialize (H0 (fresh_atom L) (fresh_atom_not_in L)).
    eapply lc_ty_open_reverse; exact H0.
  - inversion IHHty; subst.
    eapply lc_ty_open; eauto using wf_ty_closed.
  - constructor.
  - constructor.
  - exact IHHty2.
Qed.

Lemma admissible_environment_update : forall theta X a,
  admissible_environment theta -> admissible a ->
  admissible_environment (update_relation_environment theta X a).
Proof.
  intros theta X a Htheta Ha Y.
  unfold update_relation_environment.
  destruct (Nat.eqb X Y); [exact Ha | apply Htheta].
Qed.

Lemma instantiate_ty_map_ext : forall T rho1 rho2,
  (forall X, rho1 X = rho2 X) ->
  instantiate_ty rho1 T = instantiate_ty rho2 T.
Proof.
  induction T; intros rho1 rho2 Heq; simpl; f_equal; eauto.
Qed.

Lemma instantiate_tm_map_ext : forall t rho1 rho2 sigma,
  (forall X, rho1 X = rho2 X) ->
  instantiate_tm rho1 sigma t = instantiate_tm rho2 sigma t.
Proof.
  induction t; intros rho1 rho2 sigma Heq; simpl; f_equal;
    eauto using instantiate_ty_map_ext.
Qed.

Theorem fundamental_relation : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall theta sigma1 sigma2,
    admissible_environment theta ->
    related_substitutions Gamma theta sigma1 sigma2 ->
    related_term T [] theta
      (instantiate_tm (left_types theta) sigma1 t)
      (instantiate_tm (left_types theta) sigma2 t).
Proof.
  intros Delta Gamma t T Hty.
  induction Hty; intros theta sigma1 sigma2 Htheta Hsub;
    simpl.
  - destruct Hsub as [Hvalues Hlookup].
    specialize (Hlookup x T H).
    destruct (Hvalues x) as [Hv1 Hv2].
    repeat split; eauto using value_closed.
    exists (sigma1 x), (sigma2 x); repeat split;
      try constructor; auto.
  - assert (Htyped : has_type Delta Gamma (tm_abs T1 t2)
        (Ty_Arrow T1 T2)).
    { eapply T_Abs with (L := L); eauto. }
    destruct Hsub as [Hvalues Hlookup].
    assert (Hlc1 : locally_closed_tm
        (tm_abs (instantiate_ty (left_types theta) T1)
          (instantiate_tm (left_types theta) sigma1 t2))).
    { change (locally_closed_tm
        (instantiate_tm (left_types theta) sigma1 (tm_abs T1 t2))).
      eapply instantiate_closed; [exact Htyped | exact Htheta |].
      intro y; exact (proj1 (Hvalues y)). }
    assert (Hlc2 : locally_closed_tm
        (tm_abs (instantiate_ty (left_types theta) T1)
          (instantiate_tm (left_types theta) sigma2 t2))).
    { change (locally_closed_tm
        (instantiate_tm (left_types theta) sigma2 (tm_abs T1 t2))).
      eapply instantiate_closed; [exact Htyped | exact Htheta |].
      intro y; exact (proj2 (Hvalues y)). }
    split; [exact Hlc1 |]. split; [exact Hlc2 |].
    eexists _, _. split; [constructor |]. split; [constructor |].
    simpl. split; [apply v_abs; exact Hlc1 |].
    split; [apply v_abs; exact Hlc2 |].
    intros w1 w2 Hw.
    set (x := fresh_atom (L ++ free_tm_atoms t2 ++ context_keys Gamma)).
    assert (HxL : ~ In x L).
    { unfold x; intro Hin; apply fresh_atom_not_in with
        (xs := L ++ free_tm_atoms t2 ++ context_keys Gamma).
      apply in_or_app; left; exact Hin. }
    assert (Hxt : ~ In x (free_tm_atoms t2)).
    { unfold x; intro Hin; apply fresh_atom_not_in with
        (xs := L ++ free_tm_atoms t2 ++ context_keys Gamma).
      apply in_or_app; right; apply in_or_app; left; exact Hin. }
    assert (HxG : ~ In x (context_keys Gamma)).
    { unfold x; intro Hin; apply fresh_atom_not_in with
        (xs := L ++ free_tm_atoms t2 ++ context_keys Gamma).
      apply in_or_app; right; apply in_or_app; right; exact Hin. }
    destruct (H1 x HxL theta
      (update_tm_map sigma1 x w1) (update_tm_map sigma2 x w2)
      Htheta
      (related_substitutions_term_extend Gamma theta sigma1 sigma2
        x T1 w1 w2 (conj Hvalues Hlookup) HxG Hw Htheta))
      as [_ [_ [z1 [z2 [Hz1 [Hz2 Hz]]]]]].
    assert (Hmaps : forall y, locally_closed_tm (sigma1 y) /\
                                    locally_closed_tm (sigma2 y)).
    { intro y; destruct (Hvalues y) as [Hy1 Hy2];
      split; apply value_closed; assumption. }
    unfold open_tm in Hz1, Hz2.
    rewrite (instantiate_tm_open t2 0 x (left_types theta)
      sigma1 w1 Hxt (fun y => proj1 (Hmaps y))) in Hz1.
    rewrite (instantiate_tm_open t2 0 x (left_types theta)
      sigma2 w2 Hxt (fun y => proj2 (Hmaps y))) in Hz2.
    destruct (related_value_is_value T1 [] theta w1 w2
      (Forall_nil _) Htheta Hw) as [Hwv1 Hwv2].
    exists z1, z2; repeat split; try assumption.
    + eapply multi_step; [apply ST_AppAbs; eauto | exact Hz1].
    + eapply multi_step; [apply ST_AppAbs; eauto | exact Hz2].
  - destruct (IHHty1 theta sigma1 sigma2 Htheta Hsub)
      as [Hlc1 [Hlc1' [f1 [f2 [Hf1 [Hf2 Hf]]]]]].
    destruct (IHHty2 theta sigma1 sigma2 Htheta Hsub)
      as [Hlc2 [Hlc2' [w1 [w2 [Hw1 [Hw2 Hw]]]]]].
    destruct Hf as [Hfv1 [Hfv2 Hfun]].
    specialize (Hfun w1 w2 Hw) as [z1 [z2 [Hz1 [Hz2 Hz]]]].
    split; [constructor; assumption |].
    split; [constructor; assumption |].
    exists z1, z2; repeat split; try assumption.
    + eapply multi_trans.
      * apply multi_app_left; eauto.
      * eapply multi_trans.
        -- apply multi_app_right; eauto.
        -- exact Hz1.
    + eapply multi_trans.
      * apply multi_app_left; eauto.
      * eapply multi_trans.
        -- apply multi_app_right; eauto.
        -- exact Hz2.
  - assert (Htyped : has_type Delta Gamma (tm_tabs t) (Ty_All T)).
    { eapply T_TAbs with (L := L); eauto. }
    destruct Hsub as [Hvalues Hlookup].
    assert (Hlc1 : locally_closed_tm
      (tm_tabs (instantiate_tm (left_types theta) sigma1 t))).
    { change (locally_closed_tm
        (instantiate_tm (left_types theta) sigma1 (tm_tabs t))).
      eapply instantiate_closed; [exact Htyped | exact Htheta |].
      intro y; exact (proj1 (Hvalues y)). }
    assert (Hlc2 : locally_closed_tm
      (tm_tabs (instantiate_tm (left_types theta) sigma2 t))).
    { change (locally_closed_tm
        (instantiate_tm (left_types theta) sigma2 (tm_tabs t))).
      eapply instantiate_closed; [exact Htyped | exact Htheta |].
      intro y; exact (proj2 (Hvalues y)). }
    split; [exact Hlc1 |]. split; [exact Hlc2 |].
    eexists _, _. split; [constructor |]. split; [constructor |].
    simpl. split; [apply v_tabs; exact Hlc1 |].
    split; [apply v_tabs; exact Hlc2 |].
    intros U R HU HR.
    set (X := fresh_atom
      (L ++ free_tm_ty_atoms t ++ free_ty_atoms T ++
       context_type_atoms Gamma)).
    assert (HXL : ~ In X L).
    { unfold X; intro Hin; apply fresh_atom_not_in with
        (xs := L ++ free_tm_ty_atoms t ++ free_ty_atoms T ++
               context_type_atoms Gamma).
      apply in_or_app; left; exact Hin. }
    assert (HXt : ~ In X (free_tm_ty_atoms t)).
    { unfold X; intro Hin; apply fresh_atom_not_in with
        (xs := L ++ free_tm_ty_atoms t ++ free_ty_atoms T ++
               context_type_atoms Gamma).
      apply in_or_app; right; apply in_or_app; left; exact Hin. }
    assert (HXT : ~ In X (free_ty_atoms T)).
    { unfold X; intro Hin; apply fresh_atom_not_in with
        (xs := L ++ free_tm_ty_atoms t ++ free_ty_atoms T ++
               context_type_atoms Gamma).
      apply in_or_app; right; apply in_or_app; right.
      apply in_or_app; left; exact Hin. }
    assert (HXG : ~ In X (context_type_atoms Gamma)).
    { unfold X; intro Hin; apply fresh_atom_not_in with
        (xs := L ++ free_tm_ty_atoms t ++ free_ty_atoms T ++
               context_type_atoms Gamma).
      apply in_or_app; right; apply in_or_app; right.
      apply in_or_app; right; exact Hin. }
    set (a := {| assignment_left := U; assignment_right := U;
                 assignment_rel := R |}).
    assert (Ha : admissible a).
    { unfold a, admissible; simpl.
      split; [exact HU | split; [exact HU | exact HR]]. }
    set (theta' := update_relation_environment theta X a).
    assert (Htheta' : admissible_environment theta').
    { unfold theta'; eapply admissible_environment_update; eauto. }
    destruct (H0 X HXL theta' sigma1 sigma2 Htheta'
      (related_substitutions_type_extend Gamma theta sigma1 sigma2
        X a (conj Hvalues Hlookup) HXG))
      as [_ [_ [z1 [z2 [Hz1 [Hz2 Hz]]]]]].
    assert (Hr : forall Y, locally_closed_ty (left_types theta Y)).
    { intro Y; destruct (Htheta Y) as [Hy _]; exact Hy. }
    assert (Hs1 : forall y, locally_closed_tm (sigma1 y)).
    { intro y; apply value_closed, (proj1 (Hvalues y)). }
    assert (Hs2 : forall y, locally_closed_tm (sigma2 y)).
    { intro y; apply value_closed, (proj2 (Hvalues y)). }
    unfold theta' in Hz1, Hz2.
    assert (Hmap : forall Y,
      left_types (update_relation_environment theta X a) Y =
      update_ty_map (left_types theta) X U Y).
    { intro Y; unfold left_types, update_relation_environment,
        update_ty_map; destruct (Nat.eqb X Y); unfold a; reflexivity. }
    rewrite (instantiate_tm_map_ext
      (open_tm_ty t (Ty_FVar X))
      (left_types (update_relation_environment theta X a))
      (update_ty_map (left_types theta) X U) sigma1 Hmap) in Hz1.
    rewrite (instantiate_tm_map_ext
      (open_tm_ty t (Ty_FVar X))
      (left_types (update_relation_environment theta X a))
      (update_ty_map (left_types theta) X U) sigma2 Hmap) in Hz2.
    unfold open_tm_ty in Hz1, Hz2.
    rewrite (instantiate_tm_ty_open t 0 X (left_types theta)
      sigma1 U HXt Hr Hs1) in Hz1.
    rewrite (instantiate_tm_ty_open t 0 X (left_types theta)
      sigma2 U HXt Hr Hs2) in Hz2.
    assert (HTlc : lc_ty_at 1 T).
    { pose proof (has_type_result_lc _ _ _ _ Htyped) as Hres.
      inversion Hres; assumption. }
    assert (Hz' : related_value T [a] theta z1 z2).
    { apply (proj1 (related_value_open_fvar T 0 X [] theta a
        z1 z2 HTlc eq_refl HXT)); exact Hz. }
    exists z1, z2; repeat split; try assumption.
    + eapply multi_step; [apply ST_TAppTabs; eauto | exact Hz1].
    + eapply multi_step; [apply ST_TAppTabs; eauto | exact Hz2].
  - destruct (IHHty theta sigma1 sigma2 Htheta Hsub)
      as [Hlc1 [Hlc2 [f1 [f2 [Hf1 [Hf2 Hf]]]]]].
    assert (Hr : forall Y, locally_closed_ty (left_types theta Y)).
    { intro Y; destruct (Htheta Y) as [Hy _]; exact Hy. }
    assert (HUlc : locally_closed_ty (instantiate_ty (left_types theta) U)).
    { apply instantiate_ty_lc; [exact Hr | exact (wf_ty_closed _ _ H)]. }
    destruct Hf as [Hfv1 [Hfv2 Hfun]].
    set (R := related_value U [] theta).
    assert (HR : forall w1 w2, R w1 w2 -> value w1 /\ value w2).
    { intros w1 w2 Hw; eapply related_value_is_value; eauto. }
    specialize (Hfun (instantiate_ty (left_types theta) U) R HUlc HR)
      as [z1 [z2 [Hz1 [Hz2 Hz]]]].
    set (a := {| assignment_left := instantiate_ty (left_types theta) U;
                 assignment_right := instantiate_ty (left_types theta) U;
                 assignment_rel := R |}).
    assert (HTlc : lc_ty_at 1 T).
    { pose proof (has_type_result_lc _ _ _ _ Hty) as Hres.
      inversion Hres; assumption. }
    assert (Hz' : related_value (open_ty T U) [] theta z1 z2).
    { apply (proj2 (related_value_open_ty T 0 U [] theta a z1 z2
        HTlc (wf_ty_closed _ _ H) eq_refl eq_refl)); exact Hz. }
    split; [constructor; eauto |]. split; [constructor; eauto |].
    exists z1, z2; repeat split; try assumption.
    + eapply multi_trans.
      * apply multi_tapp; eauto.
      * exact Hz1.
    + eapply multi_trans.
      * apply multi_tapp; eauto.
      * exact Hz2.
  - split; [constructor |]. split; [constructor |].
    exists tm_zero, tm_zero; repeat split; try constructor.
    simpl. exists 0; auto.
  - destruct (IHHty theta sigma1 sigma2 Htheta Hsub)
      as [Hlc1 [Hlc2 [v1 [v2 [H1 [H2 Hv]]]]]].
    destruct Hv as [m [-> ->]].
    split; [constructor; exact Hlc1 |].
    split; [constructor; exact Hlc2 |].
    exists (numeral (S m)), (numeral (S m)); repeat split.
    + apply multi_succ; exact H1.
    + apply multi_succ; exact H2.
    + simpl. exists (S m); auto.
  - destruct (IHHty1 theta sigma1 sigma2 Htheta Hsub)
      as [HlcN1 [HlcN2 [n1 [n2 [Hn1 [Hn2 Hn]]]]]].
    destruct (IHHty2 theta sigma1 sigma2 Htheta Hsub)
      as [HlcB1 [HlcB2 [b1 [b2 [Hb1 [Hb2 Hb]]]]]].
    destruct (IHHty3 theta sigma1 sigma2 Htheta Hsub)
      as [HlcS1 [HlcS2 [s1 [s2 [Hs1 [Hs2 Hs]]]]]].
    destruct Hn as [m [-> ->]].
    destruct (related_value_is_value T [] theta b1 b2
      (Forall_nil _) Htheta Hb) as [Hbv1 Hbv2].
    destruct (related_value_is_value
      (Ty_Arrow Ty_Nat (Ty_Arrow T T)) [] theta s1 s2
      (Forall_nil _) Htheta Hs) as [Hsv1 Hsv2].
    destruct (related_natrec_values T theta m b1 b2 s1 s2
      Htheta Hb Hs) as [z1 [z2 [Hz1 [Hz2 Hz]]]].
    split; [constructor; assumption |].
    split; [constructor; assumption |].
    exists z1, z2; repeat split; try assumption.
    + eapply multi_trans.
      * apply multi_rec_arg; eauto.
      * eapply multi_trans.
        -- apply multi_rec_base; eauto using numeral_numeric.
        -- eapply multi_trans.
           ++ apply multi_rec_step; eauto using numeral_numeric.
           ++ exact Hz1.
    + eapply multi_trans.
      * apply multi_rec_arg; eauto.
      * eapply multi_trans.
        -- apply multi_rec_base; eauto using numeral_numeric.
        -- eapply multi_trans.
           ++ apply multi_rec_step; eauto using numeral_numeric.
           ++ exact Hz2.
Qed.

Lemma free_ty_open_preserves : forall T k U X,
  In X (free_ty_atoms T) ->
  In X (free_ty_atoms (open_ty_rec k U T)).
Proof.
  induction T; intros k U X Hin; simpl in *; try contradiction.
  - exact Hin.
  - repeat rewrite in_app_iff in *; destruct Hin;
      [left; eauto | right; eauto].
  - eauto.
Qed.

Lemma free_tm_open_preserves : forall t k u x,
  In x (free_tm_atoms t) ->
  In x (free_tm_atoms (open_tm_rec k u t)).
Proof.
  induction t; intros k u x Hin; simpl in *; try contradiction;
    try (exact Hin); try (eauto).
  - repeat rewrite in_app_iff in *; destruct Hin;
      [left; eauto | right; eauto].
  - repeat rewrite in_app_iff in *; intuition eauto.
Qed.

Lemma free_tm_ty_open_preserves : forall t k U X,
  In X (free_tm_ty_atoms t) ->
  In X (free_tm_ty_atoms (open_tm_ty_rec k U t)).
Proof.
  induction t; intros k U X Hin; simpl in *; try contradiction;
    try (eauto).
  - repeat rewrite in_app_iff in *; destruct Hin.
    + left; eapply free_ty_open_preserves; eauto.
    + right; eauto.
  - repeat rewrite in_app_iff in *; intuition eauto.
  - repeat rewrite in_app_iff in *; destruct Hin.
    + left; eauto.
    + right; eapply free_ty_open_preserves; eauto.
  - repeat rewrite in_app_iff in *; intuition eauto.
Qed.

Lemma free_tm_atoms_open_ty : forall t k U,
  free_tm_atoms (open_tm_ty_rec k U t) = free_tm_atoms t.
Proof.
  induction t; intros k U; simpl; try reflexivity.
  - apply IHt.
  - rewrite IHt1, IHt2; reflexivity.
  - apply IHt.
  - apply IHt.
  - apply IHt.
  - rewrite IHt1, IHt2, IHt3; reflexivity.
Qed.

Lemma free_tm_ty_atoms_open_tm : forall t k x,
  free_tm_ty_atoms (open_tm_rec k (tm_fvar x) t) = free_tm_ty_atoms t.
Proof.
  induction t; intros k x; simpl; try reflexivity.
  - destruct (Nat.eqb k n); reflexivity.
  - rewrite (IHt (S k) x); reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
  - apply IHt.
  - rewrite IHt; reflexivity.
  - apply IHt.
  - rewrite IHt1, IHt2, IHt3; reflexivity.
Qed.

Lemma wf_ty_support : forall Delta T X,
  wf_ty Delta T -> In X (free_ty_atoms T) -> In X Delta.
Proof.
  intros Delta T X Hwf; induction Hwf; simpl; intros Hin.
  - destruct Hin as [-> | []]; assumption.
  - apply in_app_iff in Hin as [Hin | Hin]; eauto.
  - set (Y := fresh_atom (L ++ free_ty_atoms T ++ [X])).
    assert (HYL : ~ In Y L).
    { unfold Y; intro HYin; apply fresh_atom_not_in with
        (xs := L ++ free_ty_atoms T ++ [X]);
      apply in_or_app; left; exact HYin. }
    assert (HYX : Y <> X).
    { unfold Y; intro Heq; apply fresh_atom_not_in with
        (xs := L ++ free_ty_atoms T ++ [X]); subst;
      apply in_or_app; right; apply in_or_app; right;
      simpl; auto. }
    specialize (H0 Y HYL (free_ty_open_preserves T 0 (Ty_FVar Y) X Hin)).
    simpl in H0. destruct H0 as [Heq | HIn]; [contradiction | exact HIn].
  - contradiction.
Qed.

Lemma has_type_support : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  (forall x, In x (free_tm_atoms t) ->
    exists A, lookup_context x Gamma = Some A) /\
  (forall X, In X (free_tm_ty_atoms t) -> In X Delta).
Proof.
  intros Delta Gamma t T Hty; induction Hty; simpl.
  - split.
    + intros y [-> | []]. exists T; exact H.
    + intros X Hin; contradiction.
  - split.
    + intros y Hin.
      set (x := fresh_atom (L ++ free_tm_atoms t2)).
      assert (HxL : ~ In x L).
      { unfold x; intro HIn; apply fresh_atom_not_in with
          (xs := L ++ free_tm_atoms t2);
        apply in_or_app; left; exact HIn. }
      assert (Hxy : x <> y).
      { intro Heq; unfold x in Heq. apply fresh_atom_not_in with
          (xs := L ++ free_tm_atoms t2);
        apply in_or_app; right; rewrite Heq; exact Hin. }
      specialize (H1 x HxL) as [Hterm _].
      specialize (Hterm y (free_tm_open_preserves t2 0
        (tm_fvar x) y Hin)) as [A HA].
      simpl in HA.
      assert (Heqb : Nat.eqb y x = false) by (apply Nat.eqb_neq; lia).
      rewrite Heqb in HA. exists A; exact HA.
    + intros X Hin. apply in_app_iff in Hin as [Hin | Hin].
      * eapply wf_ty_support; eauto.
      * set (x := fresh_atom L).
        assert (HxL : ~ In x L) by (apply fresh_atom_not_in).
        specialize (H1 x HxL) as [_ Htypes].
        apply Htypes. unfold open_tm.
        rewrite free_tm_ty_atoms_open_tm. exact Hin.
  - destruct IHHty1 as [Hterm1 Htypes1].
    destruct IHHty2 as [Hterm2 Htypes2].
    split; intros y Hin; apply in_app_iff in Hin as [Hin | Hin];
      eauto.
  - split.
    + intros y Hin.
      set (X := fresh_atom L).
      assert (HXL : ~ In X L) by (apply fresh_atom_not_in).
      specialize (H0 X HXL) as [Hterm _].
      apply Hterm. unfold open_tm_ty.
      rewrite free_tm_atoms_open_ty. exact Hin.
    + intros Y Hin.
      set (X := fresh_atom (L ++ free_tm_ty_atoms t)).
      assert (HXL : ~ In X L).
      { unfold X; intro HIn; apply fresh_atom_not_in with
          (xs := L ++ free_tm_ty_atoms t);
        apply in_or_app; left; exact HIn. }
      assert (HXY : X <> Y).
      { intro Heq; unfold X in Heq. apply fresh_atom_not_in with
          (xs := L ++ free_tm_ty_atoms t);
        apply in_or_app; right; rewrite Heq; exact Hin. }
      specialize (H0 X HXL) as [_ Htypes].
      specialize (Htypes Y (free_tm_ty_open_preserves t 0
        (Ty_FVar X) Y Hin)).
      simpl in Htypes. destruct Htypes as [Heq | HIn];
        [contradiction | exact HIn].
  - destruct IHHty as [Hterm Htypes].
    split.
    + exact Hterm.
    + intros X Hin. apply in_app_iff in Hin as [Hin | Hin].
      * apply Htypes; exact Hin.
      * eapply wf_ty_support; eauto.
  - split; intros x Hin; contradiction.
  - exact IHHty.
  - destruct IHHty1 as [Hterm1 Htypes1].
    destruct IHHty2 as [Hterm2 Htypes2].
    destruct IHHty3 as [Hterm3 Htypes3].
    split; intros y Hin; repeat rewrite in_app_iff in Hin;
      intuition eauto.
Qed.

Lemma instantiate_ty_identity : forall T rho,
  (forall X, ~ In X (free_ty_atoms T)) ->
  instantiate_ty rho T = T.
Proof.
  induction T; intros rho Hnone; simpl; try reflexivity.
  - exfalso; apply (Hnone a); simpl; auto.
  - f_equal; [apply IHT1 | apply IHT2]; intros X Hin;
      apply (Hnone X); simpl; apply in_or_app;
      [left | right]; exact Hin.
  - f_equal. apply IHT. exact Hnone.
Qed.

Lemma instantiate_tm_identity : forall t rho sigma,
  (forall x, ~ In x (free_tm_atoms t)) ->
  (forall X, ~ In X (free_tm_ty_atoms t)) ->
  instantiate_tm rho sigma t = t.
Proof.
  induction t; intros rho sigma Hterm Htype; simpl; try reflexivity.
  - exfalso; apply (Hterm a); simpl; auto.
  - f_equal.
    + apply instantiate_ty_identity. intros X Hin.
      apply (Htype X); simpl; apply in_or_app; left; exact Hin.
    + apply IHt.
      * exact Hterm.
      * intros X Hin; apply (Htype X); simpl;
          apply in_or_app; right; exact Hin.
  - f_equal.
    + apply IHt1.
      * intros x Hin; apply (Hterm x); simpl;
          apply in_or_app; left; exact Hin.
      * intros X Hin; apply (Htype X); simpl;
          apply in_or_app; left; exact Hin.
    + apply IHt2.
      * intros x Hin; apply (Hterm x); simpl;
          apply in_or_app; right; exact Hin.
      * intros X Hin; apply (Htype X); simpl;
          apply in_or_app; right; exact Hin.
  - f_equal; apply IHt; assumption.
  - f_equal.
    + apply IHt.
      * exact Hterm.
      * intros X Hin; apply (Htype X); simpl;
          apply in_or_app; left; exact Hin.
    + apply instantiate_ty_identity. intros X Hin.
      apply (Htype X); simpl; apply in_or_app; right; exact Hin.
  - f_equal; apply IHt; assumption.
  - f_equal.
    + apply IHt1.
      * intros x Hin; apply (Hterm x); simpl;
          repeat rewrite in_app_iff; tauto.
      * intros X Hin; apply (Htype X); simpl;
          repeat rewrite in_app_iff; tauto.
    + apply IHt2.
      * intros x Hin; apply (Hterm x); simpl;
          repeat rewrite in_app_iff; tauto.
      * intros X Hin; apply (Htype X); simpl;
          repeat rewrite in_app_iff; tauto.
    + apply IHt3.
      * intros x Hin; apply (Hterm x); simpl;
          repeat rewrite in_app_iff; tauto.
      * intros X Hin; apply (Htype X); simpl;
          repeat rewrite in_app_iff; tauto.
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
  intros t Hty U v Hwf Hv Hvt.
  set (theta0 := (fun _ =>
    {| assignment_left := Ty_Nat;
                assignment_right := Ty_Nat;
                assignment_rel := fun _ _ => False |}) : relation_environment).
  set (sigma0 := (fun _ => tm_zero) : atom -> tm).
  assert (Htheta0 : admissible_environment theta0).
  { intro X; unfold theta0, admissible; simpl.
    split; [constructor | split; [constructor |]].
    intros a b H; contradiction. }
  assert (Hsub0 : related_substitutions empty theta0 sigma0 sigma0).
  { split.
    - intro x; unfold sigma0; split; constructor; constructor.
    - intros x A Hlook; discriminate. }
  pose proof (fundamental_relation [] empty t
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0)))
    Hty theta0 sigma0 sigma0 Htheta0 Hsub0) as Hfund.
  assert (Hident : instantiate_tm (left_types theta0) sigma0 t = t).
  { apply instantiate_tm_identity.
    - intros x Hin.
      destruct (has_type_support _ _ _ _ Hty) as [Hterm _].
      destruct (Hterm x Hin) as [A HA]. discriminate.
    - intros X Hin.
      destruct (has_type_support _ _ _ _ Hty) as [_ Htype].
      apply (Htype X Hin). }
  rewrite Hident in Hfund.
  destruct Hfund as [_ [_ [p1 [p2 [Hp1 [Hp2 Hp]]]]]].
  destruct Hp as [_ [_ Hpoly]].
  set (R := fun w1 w2 : tm => w1 = v /\ w2 = v).
  assert (HR : forall w1 w2, R w1 w2 -> value w1 /\ value w2).
  { intros w1 w2 [-> ->]; split; exact Hv. }
  specialize (Hpoly U R (wf_ty_closed _ _ Hwf) HR)
    as [f1 [f2 [Hf1 [Hf2 Hf]]]].
  destruct Hf as [_ [_ Hfun]].
  assert (Hvv : related_value (Ty_BVar 0)
      [{| assignment_left := U; assignment_right := U;
          assignment_rel := R |}] theta0 v v).
  { simpl. unfold R; auto. }
  specialize (Hfun v v Hvv) as [z1 [z2 [Hz1 [Hz2 Hz]]]].
  simpl in Hz. destruct Hz as [Heq _]. subst z1.
  eapply multi_trans.
  - apply multi_app_left.
    + apply multi_tapp; [exact Hp1 | exact (wf_ty_closed _ _ Hwf)].
    + exact (value_closed _ Hv).
  - eapply multi_trans.
    + apply multi_app_left; [exact Hf1 | exact (value_closed _ Hv)].
    + exact Hz1.
Qed.

End SystemFParametricityRecursionHardTask.
