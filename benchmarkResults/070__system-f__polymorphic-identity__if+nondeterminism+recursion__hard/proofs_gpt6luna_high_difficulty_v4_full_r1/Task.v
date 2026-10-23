(** System F parametricity benchmark, Hard variant.
    Features: if-nondeterminism-recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFParametricityIfNondeterminismRecursionHardTask.

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
  | v_true : value tm_true
  | v_false : value tm_false
  | v_nat : forall n, numeric_value n -> value n.

Lemma numeric_value_lc : forall n, numeric_value n -> locally_closed_tm n.
Proof. intros n H; induction H; simpl; constructor; assumption. Qed.
Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof.
  intros v H; inversion H; subst; try assumption; try constructor;
    eauto using numeric_value_lc.
Qed.
Lemma numeral_numeric : forall n, numeric_value (numeral n).
Proof. induction n; simpl; constructor; assumption. Qed.
Lemma numeral_value : forall n, value (numeral n).
Proof. intro n; apply v_nat; apply numeral_numeric. Qed.

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
      has_type Delta Gamma (tm_natrec n b s) T
  | T_Choice : forall Delta Gamma t1 t2 T,
      has_type Delta Gamma t1 T -> has_type Delta Gamma t2 T ->
      has_type Delta Gamma (tm_choice t1 t2) T.

Lemma lc_ty_open_inv : forall k T X,
  lc_ty_at k (open_ty_rec k (Ty_FVar X) T) -> lc_ty_at (S k) T.
Proof.
  intros k T; revert k; induction T; intros k X H; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst; constructor; lia.
    + inversion H; subst; constructor; lia.
  - constructor.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor. eapply IHT; eauto.
  - constructor.
  - constructor.
Qed.

Lemma lc_ty_weaken : forall K1 K2 T,
  K1 <= K2 -> lc_ty_at K1 T -> lc_ty_at K2 T.
Proof.
  intros K1 K2 T Hle Hlc; revert K2 Hle.
  induction Hlc; intros K2 Hle.
  - constructor; lia.
  - constructor.
  - constructor; [eapply IHHlc1|eapply IHHlc2]; assumption.
  - constructor. apply IHHlc. lia.
  - constructor.
  - constructor.
Qed.

Lemma lc_tm_type_weaken : forall K1 K2 k t,
  K1 <= K2 -> lc_tm_at K1 k t -> lc_tm_at K2 k t.
Proof.
  intros K1 K2 k t Hle Hlc; revert K2 Hle.
  induction Hlc; intros K2 Hle.
  - constructor; assumption.
  - constructor.
  - constructor.
    + eapply lc_ty_weaken; eauto.
    + eapply IHHlc; eauto.
  - constructor.
    + eapply IHHlc1; eauto.
    + eapply IHHlc2; eauto.
  - constructor. eapply IHHlc; lia.
  - constructor.
    + eapply IHHlc; eauto.
    + eapply lc_ty_weaken; eauto.
  - constructor.
  - constructor.
  - constructor.
    + eapply IHHlc1; eauto.
    + eapply IHHlc2; eauto.
    + eapply IHHlc3; eauto.
  - constructor.
  - constructor. eapply IHHlc; eauto.
  - constructor.
    + eapply IHHlc1; eauto.
    + eapply IHHlc2; eauto.
    + eapply IHHlc3; eauto.
  - constructor.
    + eapply IHHlc1; eauto.
    + eapply IHHlc2; eauto.
Qed.

Inductive multi : tm -> tm -> Prop :=
  | multi_refl : forall x, multi x x
  | multi_step : forall x y z, x --> y -> multi y z -> multi x z.
Notation "t '-->*' u" := (multi t u) (at level 40).


Hint Constructors lc_ty_at lc_tm_at value : core.

(* The operational part of the logical relation records a successful
   call-by-value path.  This is the appropriate notion for tm_choice. *)
Definition may_rel (R : tm -> tm -> Prop) (t u : tm) : Prop :=
  exists v w, multi t v /\ multi u w /\ value v /\ value w /\ R v w.

Lemma multi_trans : forall t u v, multi t u -> multi u v -> multi t v.
Proof.
  intros t u v H; induction H; intros Huv; eauto using multi.
Qed.

Lemma multi_app_left : forall f f' a,
  multi f f' -> locally_closed_tm a -> multi (tm_app f a) (tm_app f' a).
Proof.
  intros f f' a H; induction H; intros Ha.
  - constructor.
  - eapply multi_step; [eapply ST_App1; eauto|apply IHmulti; exact Ha].
Qed.
Lemma multi_app_right : forall v a a',
  value v -> multi a a' -> multi (tm_app v a) (tm_app v a').
Proof.
  intros v a a' Hv H; induction H.
  - constructor.
  - eapply multi_step; [eapply ST_App2; eauto|exact IHmulti].
Qed.
Lemma multi_tapp_ctx : forall f f' A,
  multi f f' -> locally_closed_ty A ->
  multi (tm_tapp f A) (tm_tapp f' A).
Proof.
  intros f f' A H; induction H; intros HA.
  - constructor.
  - eapply multi_step; [eapply ST_TApp; eauto|apply IHmulti; exact HA].
Qed.
Lemma multi_succ_ctx : forall n n',
  multi n n' -> multi (tm_succ n) (tm_succ n').
Proof.
  intros n n' H; induction H.
  - constructor.
  - eapply multi_step; [eapply ST_Succ; eauto|exact IHmulti].
Qed.
Lemma multi_if_ctx : forall c c' a b,
  multi c c' -> locally_closed_tm a -> locally_closed_tm b ->
  multi (tm_if c a b) (tm_if c' a b).
Proof.
  intros c c' a b H; induction H; intros Ha Hb.
  - constructor.
  - eapply multi_step; [eapply ST_If; eauto|]. apply IHmulti; assumption.
Qed.
Lemma multi_rec_arg_ctx : forall n n' b s,
  multi n n' -> locally_closed_tm b -> locally_closed_tm s ->
  multi (tm_natrec n b s) (tm_natrec n' b s).
Proof.
  intros n n' b s H; induction H; intros Hb Hs.
  - constructor.
  - eapply multi_step; [eapply ST_RecArg; eauto|]. apply IHmulti; assumption.
Qed.
Lemma multi_rec_base_ctx : forall n b b' s,
  numeric_value n -> multi b b' -> locally_closed_tm s ->
  multi (tm_natrec n b s) (tm_natrec n b' s).
Proof.
  intros n b b' s Hn H; induction H; intros Hs.
  - constructor.
  - eapply multi_step; [eapply ST_RecBase; eauto|]. apply IHmulti; exact Hs.
Qed.
Lemma multi_rec_step_ctx : forall n b s s',
  numeric_value n -> value b -> multi s s' ->
  multi (tm_natrec n b s) (tm_natrec n b s').
Proof.
  intros n b s s' Hn Hb H; induction H.
  - constructor.
  - eapply multi_step; [eapply ST_RecStep; eauto|exact IHmulti].
Qed.

Definition val_rel := tm -> tm -> Prop.
Definition ty_env := atom -> ty.
Definition rel_env := atom -> val_rel.
Definition bound_env := nat -> val_rel.
Definition bound_update (b : bound_env) (k : nat) (R : val_rel) : bound_env :=
  fun i => if Nat.eqb i k then R else b i.
Definition bound_push (R : val_rel) (b : bound_env) : bound_env :=
  fun i => match i with O => R | S j => b j end.

Fixpoint close_ty (theta : ty_env) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => theta X
  | Ty_Arrow A B => Ty_Arrow (close_ty theta A) (close_ty theta B)
  | Ty_All A => Ty_All (close_ty theta A)
  | Ty_Bool => Ty_Bool
  | Ty_Nat => Ty_Nat
  end.

Fixpoint close_tm (theta : ty_env) (xi : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => xi x
  | tm_abs T b => tm_abs (close_ty theta T) (close_tm theta xi b)
  | tm_app f a => tm_app (close_tm theta xi f) (close_tm theta xi a)
  | tm_tabs b => tm_tabs (close_tm theta xi b)
  | tm_tapp f T => tm_tapp (close_tm theta xi f) (close_ty theta T)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if c a b => tm_if (close_tm theta xi c) (close_tm theta xi a) (close_tm theta xi b)
  | tm_zero => tm_zero
  | tm_succ n => tm_succ (close_tm theta xi n)
  | tm_natrec n b s => tm_natrec (close_tm theta xi n) (close_tm theta xi b) (close_tm theta xi s)
  | tm_choice a b => tm_choice (close_tm theta xi a) (close_tm theta xi b)
  end.

Fixpoint max_atom (xs : list atom) : nat :=
  match xs with [] => 0 | x :: xs' => Nat.max x (max_atom xs') end.
Lemma in_max_atom : forall xs x, In x xs -> x <= max_atom xs.
Proof.
  induction xs as [|a xs IH]; intros x Hin; simpl in *; [contradiction|].
  destruct Hin as [->|Hin].
  - apply Nat.le_max_l.
  - eapply Nat.le_trans; [eapply IH; eauto|apply Nat.le_max_r].
Qed.
Lemma fresh_atom : forall (xs : list atom), exists x : atom, ~ In x xs.
Proof.
  intro xs. exists (S (max_atom xs)). intro Hin.
  pose proof (in_max_atom xs (S (max_atom xs)) Hin); lia.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H; induction H.
  - constructor.
  - constructor; assumption.
  - constructor. destruct (fresh_atom L) as [X HX].
    apply lc_ty_open_inv with (X := X). apply H0; exact HX.
  - constructor.
  - constructor.
Qed.

Fixpoint ty_fv (T : ty) : list atom :=
  match T with
  | Ty_BVar _ | Ty_Bool | Ty_Nat => []
  | Ty_FVar X => [X]
  | Ty_Arrow A B => ty_fv A ++ ty_fv B
  | Ty_All A => ty_fv A
  end.
Fixpoint tm_fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_true | tm_false | tm_zero => []
  | tm_fvar x => [x]
  | tm_abs _ b | tm_tabs b | tm_succ b => tm_fv b
  | tm_app a b | tm_choice a b => tm_fv a ++ tm_fv b
  | tm_tapp a _ => tm_fv a
  | tm_if c a b | tm_natrec c a b => tm_fv c ++ tm_fv a ++ tm_fv b
  end.
Fixpoint tm_tfv (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_fvar _ | tm_true | tm_false | tm_zero => []
  | tm_abs T b => ty_fv T ++ tm_tfv b
  | tm_app a b | tm_choice a b => tm_tfv a ++ tm_tfv b
  | tm_tabs b | tm_succ b => tm_tfv b
  | tm_tapp a T => tm_tfv a ++ ty_fv T
  | tm_if c a b | tm_natrec c a b => tm_tfv c ++ tm_tfv a ++ tm_tfv b
  end.
Fixpoint ctx_tfv (G : context) : list atom :=
  match G with [] => [] | (_,T)::G' => ty_fv T ++ ctx_tfv G' end.
Fixpoint ctx_vars (G : context) : list atom :=
  match G with [] => [] | (x,_)::G' => x :: ctx_vars G' end.

Lemma notin_app_l : forall (A : Type) (x : A) l r,
  ~ In x (l ++ r) -> ~ In x l.
Proof. intros A x l r H Hin; apply H; apply in_app_iff; left; exact Hin. Qed.
Lemma notin_app_r : forall (A : Type) (x : A) l r,
  ~ In x (l ++ r) -> ~ In x r.
Proof. intros A x l r H Hin; apply H; apply in_app_iff; right; exact Hin. Qed.

Lemma lc_tm_open_inv : forall K k t x,
  ~ In x (tm_fv t) ->
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) ->
  lc_tm_at K (S k) t.
Proof.
  intros K k t; revert K k; induction t; intros K k x Hfresh Hlc;
    simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst. inversion Hlc; subst. constructor; lia.
    + inversion Hlc; subst. constructor; lia.
  - constructor.
  - inversion Hlc; subst. constructor; [assumption|].
    eapply IHt; eauto.
  - inversion Hlc; subst. constructor.
    + eapply IHt1; eauto using in_or_app.
    + eapply IHt2; eauto using in_or_app.
  - inversion Hlc; subst. constructor. eapply IHt; eauto.
  - inversion Hlc; subst. constructor; [eapply IHt; eauto|assumption].
  - constructor.
  - constructor.
  - inversion Hlc; subst. constructor.
    + eapply IHt1; [exact (notin_app_l atom x (tm_fv t1) (tm_fv t2 ++ tm_fv t3) Hfresh)|assumption].
    + eapply IHt2; [exact (notin_app_l atom x (tm_fv t2) (tm_fv t3) (notin_app_r atom x (tm_fv t1) (tm_fv t2 ++ tm_fv t3) Hfresh))|assumption].
    + eapply IHt3; [exact (notin_app_r atom x (tm_fv t2) (tm_fv t3) (notin_app_r atom x (tm_fv t1) (tm_fv t2 ++ tm_fv t3) Hfresh))|assumption].
  - constructor.
  - inversion Hlc; subst. constructor. eapply IHt; eauto.
  - inversion Hlc; subst. constructor.
    + eapply IHt1; [exact (notin_app_l atom x (tm_fv t1) (tm_fv t2 ++ tm_fv t3) Hfresh)|assumption].
    + eapply IHt2; [exact (notin_app_l atom x (tm_fv t2) (tm_fv t3) (notin_app_r atom x (tm_fv t1) (tm_fv t2 ++ tm_fv t3) Hfresh))|assumption].
    + eapply IHt3; [exact (notin_app_r atom x (tm_fv t2) (tm_fv t3) (notin_app_r atom x (tm_fv t1) (tm_fv t2 ++ tm_fv t3) Hfresh))|assumption].
  - inversion Hlc; subst. constructor.
    + eapply IHt1; [eapply notin_app_l; exact Hfresh|assumption].
    + eapply IHt2; [eapply notin_app_r; exact Hfresh|assumption].
Qed.

Lemma lc_tm_ty_open_inv : forall K k t X,
  lc_tm_at K k (open_tm_ty_rec K (Ty_FVar X) t) ->
  lc_tm_at (S K) k t.
Proof.
  intros K k t; revert K k; induction t; intros K k X Hlc; simpl in *.
  - inversion Hlc; subst; constructor; assumption.
  - constructor.
  - inversion Hlc; subst. constructor.
    + eapply lc_ty_open_inv; eauto.
    + eapply IHt; eauto.
  - inversion Hlc; subst. constructor; [eapply IHt1|eapply IHt2]; eauto.
  - inversion Hlc; subst. constructor. eapply IHt; eauto.
  - inversion Hlc; subst. constructor; [eapply IHt; eauto|eapply lc_ty_open_inv; eauto].
  - constructor.
  - constructor.
  - inversion Hlc; subst. constructor; [eapply IHt1|eapply IHt2|eapply IHt3]; eauto.
  - constructor.
  - inversion Hlc; subst. constructor. eapply IHt; eauto.
  - inversion Hlc; subst. constructor; [eapply IHt1|eapply IHt2|eapply IHt3]; eauto.
  - inversion Hlc; subst. constructor; [eapply IHt1|eapply IHt2]; eauto.
Qed.

Definition xi_update (xi : atom -> tm) (x : atom) (v : tm) : atom -> tm :=
  fun y => if Nat.eqb y x then v else xi y.
Definition ty_update (theta : ty_env) (X : atom) (U : ty) : ty_env :=
  fun Y => if Nat.eqb Y X then U else theta Y.
Definition rel_update (rho : rel_env) (X : atom) (R : val_rel) : rel_env :=
  fun Y => if Nat.eqb Y X then R else rho Y.

Lemma lookup_update_eq : forall G x A y,
  lookup_context y (update G x A) =
    if Nat.eqb y x then Some A else lookup_context y G.
Proof. reflexivity. Qed.

Lemma lookup_none_fresh : forall G x,
  ~ In x (ctx_vars G) -> lookup_context x G = None.
Proof.
  induction G as [|[y T] G IH]; intros x Hfresh; simpl in *; [reflexivity|].
  apply not_in_cons in Hfresh as [Hneq Htail].
  destruct (Nat.eqb x y) eqn:E; [apply Nat.eqb_eq in E; contradiction|].
  apply IH; exact Htail.
Qed.

Lemma lookup_tfv_in_ctx : forall G x T,
  lookup_context x G = Some T ->
  forall X, In X (ty_fv T) -> In X (ctx_tfv G).
Proof.
  induction G as [|[y A] G IH]; intros x T Hlook X HX; simpl in *; try discriminate.
  destruct (Nat.eqb x y) eqn:E.
  - inversion Hlook; subst. apply in_or_app; left; exact HX.
  - apply in_or_app; right. eapply IH; eauto.
Qed.

Definition ty_env_ok (theta : ty_env) : Prop :=
  forall X, locally_closed_ty (theta X).
Definition term_env_ok (xi : atom -> tm) : Prop := forall x, value (xi x).
Definition rel_ok (R : val_rel) : Prop :=
  forall v w, R v w -> value v /\ value w.
Definition rel_env_ok (rho : rel_env) : Prop := forall X, rel_ok (rho X).
Definition empty_bound : bound_env := fun _ _ _ => False.
Definition bound_env_ok (b : bound_env) : Prop := forall i, rel_ok (b i).
Lemma empty_bound_ok : bound_env_ok empty_bound.
Proof. intros i v w H; contradiction. Qed.

Lemma lc_tm_weaken : forall K k1 k2 t,
  k1 <= k2 -> lc_tm_at K k1 t -> lc_tm_at K k2 t.
Proof.
  intros K k1 k2 t Hle Hlc; revert k2 Hle.
  induction Hlc; intros k2 Hle; try solve [constructor; eauto].
  - constructor; lia.
  - constructor; [assumption|]. apply IHHlc. lia.
Qed.

Lemma open_ty_rec_lc : forall d k U T,
  d <= k -> lc_ty_at d T -> open_ty_rec k U T = T.
Proof.
  intros d k U T Hdk Hlc; revert d k Hdk Hlc.
  induction T; intros d k Hdk Hlc; simpl.
  - inversion Hlc; subst. destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; lia.
    + reflexivity.
  - reflexivity.
  - inversion Hlc; subst. f_equal.
    + eapply IHT1; eauto.
    + eapply IHT2; eauto.
  - inversion Hlc; subst. f_equal.
    eapply IHT with (d := S d) (k := S k); [lia|assumption].
  - reflexivity.
  - reflexivity.
Qed.

Lemma open_tm_ty_rec_lc : forall K k U t,
  lc_tm_at K k t -> open_tm_ty_rec K U t = t.
Proof.
  intros K k U t Hlc; revert K k Hlc.
  induction t; intros K k Hlc; simpl.
  - reflexivity.
  - reflexivity.
  - inversion Hlc; subst. f_equal.
    + eapply open_ty_rec_lc with (d := K) (k := K); [lia|eassumption].
    + eapply IHt; eassumption.
  - inversion Hlc; subst. f_equal; [eapply IHt1|eapply IHt2]; eassumption.
  - inversion Hlc; subst. f_equal. eapply IHt with (K := S K); eassumption.
  - inversion Hlc; subst. f_equal.
    + eapply IHt; eassumption.
    + eapply open_ty_rec_lc with (d := K) (k := K); [lia|eassumption].
  - reflexivity.
  - reflexivity.
  - inversion Hlc; subst. f_equal; [eapply IHt1|eapply IHt2|eapply IHt3]; eassumption.
  - reflexivity.
  - inversion Hlc; subst. f_equal. eapply IHt; eassumption.
  - inversion Hlc; subst. f_equal; [eapply IHt1|eapply IHt2|eapply IHt3]; eassumption.
  - inversion Hlc; subst. f_equal; [eapply IHt1|eapply IHt2]; eassumption.
Qed.

Lemma close_ty_open_fvar : forall T k theta X U,
  ty_env_ok theta -> ~ In X (ty_fv T) ->
  close_ty (ty_update theta X U) (open_ty_rec k (Ty_FVar X) T) =
    open_ty_rec k U (close_ty theta T).
Proof.
  induction T; intros k theta X U Hok Hfresh; simpl in *.
  - destruct (Nat.eqb k n) eqn:E; simpl.
    + unfold close_ty, ty_update; simpl; rewrite Nat.eqb_refl; reflexivity.
    + reflexivity.
  - assert (Hneq : a <> X) by (intro E; subst; apply Hfresh; simpl; auto).
    unfold close_ty, ty_update; simpl. destruct (Nat.eqb a X) eqn:E.
    + apply Nat.eqb_eq in E; contradiction.
    + symmetry. apply open_ty_rec_lc with (d := 0) (k := k); [lia|apply Hok].
  - assert (Hf1 : ~ In X (ty_fv T1)) by (intro Hin; apply Hfresh; apply in_app_iff; left; exact Hin).
    assert (Hf2 : ~ In X (ty_fv T2)) by (intro Hin; apply Hfresh; apply in_app_iff; right; exact Hin).
    f_equal; [eapply IHT1|eapply IHT2]; eauto.
  - f_equal. eapply IHT; eauto.
  - reflexivity.
  - reflexivity.
Qed.

Lemma close_tm_ty_open_fvar : forall t k theta xi X U,
  ty_env_ok theta -> term_env_ok xi -> ~ In X (tm_tfv t) ->
  close_tm (ty_update theta X U) xi (open_tm_ty_rec k (Ty_FVar X) t) =
    open_tm_ty_rec k U (close_tm theta xi t).
Proof.
  induction t; intros k theta xi X U Hok Hxi Hfresh; simpl in *.
  - reflexivity.
  - symmetry. apply open_tm_ty_rec_lc with (K := k) (k := 0).
    eapply lc_tm_type_weaken with (K1 := 0); [lia|apply value_lc, Hxi].
  - assert (Hann : ~ In X (ty_fv t)) by (eapply notin_app_l; exact Hfresh).
    assert (Hbody : ~ In X (tm_tfv t0)) by (eapply notin_app_r; exact Hfresh).
    f_equal.
    + eapply close_ty_open_fvar; eauto.
    + eapply IHt; eauto.
  - assert (Hf1 : ~ In X (tm_tfv t1)) by (eapply notin_app_l; exact Hfresh).
    assert (Hf2 : ~ In X (tm_tfv t2)) by (eapply notin_app_r; exact Hfresh).
    f_equal; [eapply IHt1|eapply IHt2]; eauto.
  - f_equal. eapply IHt; eauto.
  - assert (Hft : ~ In X (tm_tfv t)) by (eapply notin_app_l; exact Hfresh).
    assert (Hf : ~ In X (ty_fv t0)) by (eapply notin_app_r; exact Hfresh).
    f_equal.
    + eapply IHt; [assumption|assumption|exact Hft].
    + eapply close_ty_open_fvar; eauto.
  - reflexivity.
  - reflexivity.
  - assert (Hf1 : ~ In X (tm_tfv t1)) by (eapply notin_app_l; exact Hfresh).
    assert (Hf2 : ~ In X (tm_tfv t2)) by (eapply notin_app_l; eapply notin_app_r; exact Hfresh).
    assert (Hf3 : ~ In X (tm_tfv t3)) by (eapply notin_app_r; eapply notin_app_r; exact Hfresh).
    f_equal; [eapply IHt1|eapply IHt2|eapply IHt3]; eauto.
  - reflexivity.
  - f_equal. eapply IHt; eauto.
  - assert (Hf1 : ~ In X (tm_tfv t1)) by (eapply notin_app_l; exact Hfresh).
    assert (Hf2 : ~ In X (tm_tfv t2)) by (eapply notin_app_l; eapply notin_app_r; exact Hfresh).
    assert (Hf3 : ~ In X (tm_tfv t3)) by (eapply notin_app_r; eapply notin_app_r; exact Hfresh).
    f_equal; [eapply IHt1|eapply IHt2|eapply IHt3]; eauto.
  - assert (Hf1 : ~ In X (tm_tfv t1)) by (intro Hin; apply Hfresh; simpl; apply in_app_iff; left; exact Hin).
    assert (Hf2 : ~ In X (tm_tfv t2)) by (intro Hin; apply Hfresh; simpl; apply in_app_iff; right; exact Hin).
    f_equal; [eapply IHt1|eapply IHt2]; eauto.
Qed.

Lemma has_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T Hty; induction Hty.
  - constructor.
  - apply lc_tm_abs.
    + eapply wf_ty_lc; eassumption.
    + destruct (fresh_atom (L ++ tm_fv t2)) as [x Hx].
      apply lc_tm_open_inv with (x := x).
      * eapply notin_app_r; exact Hx.
      * match goal with
        | Hih : forall x, ~ In x L -> locally_closed_tm (open_tm t2 (tm_fvar x)) |- _ =>
            apply (Hih x); eapply notin_app_l; exact Hx
        end.
  - constructor; assumption.
  - apply lc_tm_tabs.
    destruct (fresh_atom (L ++ tm_tfv t)) as [X HX].
    apply lc_tm_ty_open_inv with (X := X).
    apply (H0 X); eapply notin_app_l; exact HX.
  - constructor; [assumption|eapply wf_ty_lc; eassumption].
  - constructor.
  - constructor.
  - constructor; assumption.
  - constructor.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
Qed.

(* A type-variable environment is interpreted by arbitrary relations on
   values.  Bound variables are handled by the stack argument. *)
Fixpoint ty_rel (rho : rel_env) (bound : bound_env) (T : ty) : val_rel :=
  match T with
  | Ty_BVar i => bound i
  | Ty_FVar X => rho X
  | Ty_Arrow A B => fun v w =>
      value v /\ value w /\
      forall a b, ty_rel rho bound A a b ->
        may_rel (ty_rel rho bound B) (tm_app v a) (tm_app w b)
  | Ty_All A => fun v w =>
      value v /\ value w /\
      forall a b (R : val_rel), locally_closed_ty a -> locally_closed_ty b ->
        rel_ok R ->
        may_rel (ty_rel rho (bound_push R bound) A)
          (tm_tapp v a) (tm_tapp w b)
  | Ty_Bool => fun v w => v = tm_true /\ w = tm_true \/ v = tm_false /\ w = tm_false
  | Ty_Nat => fun v w => exists n, v = numeral n /\ w = numeral n
  end.

Lemma may_rel_ext : forall R S t u,
  (forall v w, R v w <-> S v w) ->
  (may_rel R t u <-> may_rel S t u).
Proof.
  intros R S t u H; split; intros (v & w & H1 & H2 & Hv & Hw & HR);
    exists v, w; repeat split; try assumption; apply H; assumption.
Qed.

Lemma bound_push_update : forall b k R Q,
  forall i, bound_push Q (bound_update b k R) i =
    bound_update (bound_push Q b) (S k) R i.
Proof.
  intros b k R Q i; destruct i; simpl; auto.
Qed.

Lemma ty_rel_bound_ext : forall rho b b' T,
  (forall i v w, b i v w <-> b' i v w) ->
  forall v w, ty_rel rho b T v w <-> ty_rel rho b' T v w.
Proof.
  intros rho b b' T; revert b b'; induction T; intros b b' Hext v w; simpl.
  - apply Hext.
  - tauto.
  - split.
    + intros (Hv & Hw & Hfun); repeat split; try assumption.
      intros a c Hac. apply (proj1 (may_rel_ext _ _ _ _ (fun p q => IHT2 b b' Hext p q))).
      apply Hfun. apply (proj2 (IHT1 b b' Hext a c)); exact Hac.
    + intros (Hv & Hw & Hfun); repeat split; try assumption.
      intros a c Hac. apply (proj2 (may_rel_ext _ _ _ _ (fun p q => IHT2 b b' Hext p q))).
      apply Hfun. apply (proj1 (IHT1 b b' Hext a c)); exact Hac.
  - split.
    + intros (Hv & Hw & Hfun); repeat split; try assumption.
      intros a c Q Ha Hc HQ.
      apply (proj1 (may_rel_ext _ _ _ _ (fun p q => IHT (bound_push Q b) (bound_push Q b') (fun i x y => match i with O => iff_refl (Q x y) | S j => Hext j x y end) p q))).
      apply Hfun; assumption.
    + intros (Hv & Hw & Hfun); repeat split; try assumption.
      intros a c Q Ha Hc HQ.
      apply (proj2 (may_rel_ext _ _ _ _ (fun p q => IHT (bound_push Q b) (bound_push Q b') (fun i x y => match i with O => iff_refl (Q x y) | S j => Hext j x y end) p q))).
      apply Hfun; assumption.
  - tauto.
  - tauto.
Qed.

Lemma ty_rel_bound_lc : forall K T,
  lc_ty_at K T -> forall rho b b',
  (forall i, i < K -> forall v w, b i v w <-> b' i v w) ->
  forall v w, ty_rel rho b T v w <-> ty_rel rho b' T v w.
Proof.
  intros K T Hlc; induction Hlc; intros rho b b' Hprefix v w; simpl.
  - apply Hprefix; assumption.
  - tauto.
  - split.
    + intros (Hv & Hw & Hfun); repeat split; try assumption.
      intros a c Hac.
      apply (proj1 (may_rel_ext _ _ _ _ (fun p q => IHHlc2 rho b b' Hprefix p q))).
      apply Hfun. apply (proj2 (IHHlc1 rho b b' Hprefix a c)); exact Hac.
    + intros (Hv & Hw & Hfun); repeat split; try assumption.
      intros a c Hac.
      apply (proj2 (may_rel_ext _ _ _ _ (fun p q => IHHlc2 rho b b' Hprefix p q))).
      apply Hfun. apply (proj1 (IHHlc1 rho b b' Hprefix a c)); exact Hac.
  - split.
    + intros (Hv & Hw & Hfun); repeat split; try assumption.
      intros a c Q Ha Hc HQ.
      assert (Hp : forall i, i < S k -> forall p q,
        bound_push Q b i p q <-> bound_push Q b' i p q).
      { intros i Hi p q; destruct i; simpl; [tauto|apply Hprefix; lia]. }
      apply (proj1 (may_rel_ext _ _ _ _ (fun p q =>
        IHHlc rho (bound_push Q b) (bound_push Q b') Hp p q))).
      apply Hfun; assumption.
    + intros (Hv & Hw & Hfun); repeat split; try assumption.
      intros a c Q Ha Hc HQ.
      assert (Hp : forall i, i < S k -> forall p q,
        bound_push Q b i p q <-> bound_push Q b' i p q).
      { intros i Hi p q; destruct i; simpl; [tauto|apply Hprefix; lia]. }
      apply (proj2 (may_rel_ext _ _ _ _ (fun p q =>
        IHHlc rho (bound_push Q b) (bound_push Q b') Hp p q))).
      apply Hfun; assumption.
  - tauto.
  - tauto.
Qed.

Lemma ty_rel_open_fvar : forall T k rho bound X R,
  ~ In X (ty_fv T) -> forall v w,
  ty_rel (rel_update rho X R) bound (open_ty_rec k (Ty_FVar X) T) v w <->
  ty_rel rho (bound_update bound k R) T v w.
Proof.
  induction T; intros k rho bound X R Hfresh v w; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst. unfold rel_update, bound_update; simpl.
      destruct (Nat.eqb X X) eqn:EX; [|apply Nat.eqb_neq in EX; contradiction].
      destruct (Nat.eqb n n) eqn:En; [reflexivity|apply Nat.eqb_neq in En; contradiction].
    + unfold bound_update. rewrite Nat.eqb_sym, E. tauto.
  - assert (Hneq : a <> X) by (intro E; subst; apply Hfresh; simpl; auto).
    unfold rel_update. destruct (Nat.eqb a X) eqn:E.
    + apply Nat.eqb_eq in E; contradiction.
    + tauto.
  - assert (Hf1 : ~ In X (ty_fv T1)) by (intro Hin; apply Hfresh; apply in_app_iff; left; exact Hin).
    assert (Hf2 : ~ In X (ty_fv T2)) by (intro Hin; apply Hfresh; apply in_app_iff; right; exact Hin).
    specialize (IHT1 k rho bound X R Hf1).
    specialize (IHT2 k rho bound X R Hf2).
    simpl. split.
    + intros (Hv & Hw & Hfun); repeat split; try assumption.
      intros a b Hab.
      apply (proj1 (may_rel_ext _ _ _ _ (fun p q => IHT2 p q))).
      apply Hfun. apply (proj2 (IHT1 a b)); exact Hab.
    + intros (Hv & Hw & Hfun); repeat split; try assumption.
      intros a b Hab.
      apply (proj2 (may_rel_ext _ _ _ _ (fun p q => IHT2 p q))).
      apply Hfun. apply (proj1 (IHT1 a b)); exact Hab.
  - simpl. split.
    + intros (Hv & Hw & Hfun); repeat split; try assumption.
      intros a b Q Ha Hb Hvalid.
      assert (Hcomm : forall i x y,
        bound_update (bound_push Q bound) (S k) R i x y <->
        bound_push Q (bound_update bound k R) i x y).
      { intros i x y; rewrite <- (bound_push_update bound k R Q i); tauto. }
      apply (proj1 (may_rel_ext _ _ _ _ (fun p q =>
        iff_trans (IHT (S k) rho (bound_push Q bound) X R Hfresh p q)
          (ty_rel_bound_ext rho
            (bound_update (bound_push Q bound) (S k) R)
            (bound_push Q (bound_update bound k R)) T
            Hcomm p q)))).
      apply Hfun; assumption.
    + intros (Hv & Hw & Hfun); repeat split; try assumption.
      intros a b Q Ha Hb Hvalid.
      assert (Hcomm : forall i x y,
        bound_update (bound_push Q bound) (S k) R i x y <->
        bound_push Q (bound_update bound k R) i x y).
      { intros i x y; rewrite <- (bound_push_update bound k R Q i); tauto. }
      apply (proj2 (may_rel_ext _ _ _ _ (fun p q =>
        iff_trans (IHT (S k) rho (bound_push Q bound) X R Hfresh p q)
          (ty_rel_bound_ext rho
            (bound_update (bound_push Q bound) (S k) R)
            (bound_push Q (bound_update bound k R)) T
            Hcomm p q)))).
      apply Hfun; assumption.
  - tauto.
  - tauto.
Qed.

Lemma ty_rel_open_subst : forall T k rho bound U,
  lc_ty_at 0 U ->
  forall v w,
  ty_rel rho bound (open_ty_rec k U T) v w <->
  ty_rel rho (bound_update bound k (ty_rel rho bound U)) T v w.
Proof.
  induction T; intros k rho bound U HU v w; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst. unfold bound_update; rewrite Nat.eqb_refl. tauto.
    + unfold bound_update. rewrite Nat.eqb_sym, E. tauto.
  - tauto.
  - assert (IHA : forall a b, ty_rel rho bound (open_ty_rec k U T1) a b <->
       ty_rel rho (bound_update bound k (ty_rel rho bound U)) T1 a b)
      by (intros; apply IHT1; exact HU).
    assert (IHB : forall a b, ty_rel rho bound (open_ty_rec k U T2) a b <->
       ty_rel rho (bound_update bound k (ty_rel rho bound U)) T2 a b)
      by (intros; apply IHT2; exact HU).
    simpl. split.
    + intros (Hv & Hw & Hfun); repeat split; try assumption.
      intros a b Hab.
      apply (proj1 (may_rel_ext _ _ _ _ (fun p q => IHB p q))).
      apply Hfun. apply (proj2 (IHA a b)); exact Hab.
    + intros (Hv & Hw & Hfun); repeat split; try assumption.
      intros a b Hab.
      apply (proj2 (may_rel_ext _ _ _ _ (fun p q => IHB p q))).
      apply Hfun. apply (proj1 (IHA a b)); exact Hab.
  - simpl. split.
    + intros (Hv & Hw & Hfun); repeat split; try assumption.
      intros a b Q Ha Hb HQ.
      assert (HUQ : forall p q,
        ty_rel rho bound U p q <-> ty_rel rho (bound_push Q bound) U p q).
      { eapply ty_rel_bound_lc; [exact HU|]. intros i Hi; lia. }
      assert (Hcomm : forall i p q,
        bound_update (bound_push Q bound) (S k)
          (ty_rel rho (bound_push Q bound) U) i p q <->
        bound_push Q (bound_update bound k (ty_rel rho bound U)) i p q).
      { intros i p q. destruct i as [|j]; simpl.
        - tauto.
        - destruct (Nat.eqb j k) eqn:E; simpl.
          + apply Nat.eqb_eq in E; subst.
            unfold bound_update, bound_push; simpl.
            rewrite Nat.eqb_refl. apply iff_sym; apply HUQ.
          + unfold bound_update, bound_push.
            assert (Hs : Nat.eqb (S j) (S k) = Nat.eqb j k) by reflexivity.
            rewrite Hs, E. tauto. }
      apply (proj1 (may_rel_ext _ _ _ _
        (fun p q => iff_trans
          (IHT (S k) rho (bound_push Q bound) U HU p q)
          (ty_rel_bound_ext rho
            (bound_update (bound_push Q bound) (S k)
              (ty_rel rho (bound_push Q bound) U))
            (bound_push Q (bound_update bound k (ty_rel rho bound U))) T
            Hcomm p q)))).
      apply Hfun; assumption.
    + intros (Hv & Hw & Hfun); repeat split; try assumption.
      intros a b Q Ha Hb HQ.
      assert (HUQ : forall p q,
        ty_rel rho bound U p q <-> ty_rel rho (bound_push Q bound) U p q).
      { eapply ty_rel_bound_lc; [exact HU|]. intros i Hi; lia. }
      assert (Hcomm : forall i p q,
        bound_update (bound_push Q bound) (S k)
          (ty_rel rho (bound_push Q bound) U) i p q <->
        bound_push Q (bound_update bound k (ty_rel rho bound U)) i p q).
      { intros i p q. destruct i as [|j]; simpl.
        - tauto.
        - destruct (Nat.eqb j k) eqn:E; simpl.
          + apply Nat.eqb_eq in E; subst.
            unfold bound_update, bound_push.
            assert (Hs : Nat.eqb (S k) (S k) = Nat.eqb k k) by reflexivity.
            rewrite Hs, !Nat.eqb_refl; simpl. apply iff_sym; apply HUQ.
          + unfold bound_update, bound_push.
            assert (Hs : Nat.eqb (S j) (S k) = Nat.eqb j k) by reflexivity.
            rewrite Hs, E. tauto. }
      apply (proj2 (may_rel_ext _ _ _ _
        (fun p q => iff_trans
          (IHT (S k) rho (bound_push Q bound) U HU p q)
          (ty_rel_bound_ext rho
            (bound_update (bound_push Q bound) (S k)
              (ty_rel rho (bound_push Q bound) U))
            (bound_push Q (bound_update bound k (ty_rel rho bound U))) T
            Hcomm p q)))).
      apply Hfun; assumption.
  - tauto.
  - tauto.
Qed.

Lemma ty_rel_update_fresh : forall T rho bound X R,
  ~ In X (ty_fv T) -> forall v w,
  ty_rel (rel_update rho X R) bound T v w <-> ty_rel rho bound T v w.
Proof.
  induction T; intros rho bound X R Hfresh v w; simpl in *.
  - tauto.
  - assert (Hneq : a <> X) by (intro E; subst; apply Hfresh; simpl; auto).
    unfold rel_update. destruct (Nat.eqb a X) eqn:E.
    + apply Nat.eqb_eq in E; contradiction.
    + tauto.
  - assert (Hf1 : ~ In X (ty_fv T1)) by (intro Hin; apply Hfresh; apply in_app_iff; left; exact Hin).
    assert (Hf2 : ~ In X (ty_fv T2)) by (intro Hin; apply Hfresh; apply in_app_iff; right; exact Hin).
    specialize (IHT1 rho bound X R Hf1).
    specialize (IHT2 rho bound X R Hf2).
    split.
    + intros (Hv & Hw & Hfun); repeat split; try assumption.
      intros a b Hab.
      apply (proj1 (may_rel_ext _ _ _ _ (fun p q => IHT2 p q))).
      apply Hfun. apply (proj2 (IHT1 a b)); exact Hab.
    + intros (Hv & Hw & Hfun); repeat split; try assumption.
      intros a b Hab.
      apply (proj2 (may_rel_ext _ _ _ _ (fun p q => IHT2 p q))).
      apply Hfun. apply (proj1 (IHT1 a b)); exact Hab.
  - simpl. split.
    + intros (Hv & Hw & Hfun); repeat split; try assumption.
      intros a b Q Ha Hb HQ.
      apply (proj1 (may_rel_ext _ _ _ _ (fun p q =>
        IHT rho (bound_push Q bound) X R Hfresh p q))).
      apply Hfun; assumption.
    + intros (Hv & Hw & Hfun); repeat split; try assumption.
      intros a b Q Ha Hb HQ.
      apply (proj2 (may_rel_ext _ _ _ _ (fun p q =>
        IHT rho (bound_push Q bound) X R Hfresh p q))).
      apply Hfun; assumption.
  - tauto.
  - tauto.
Qed.

Lemma may_rel_app : forall rho bound A B f f' a a',
  may_rel (ty_rel rho bound (Ty_Arrow A B)) f f' ->
  may_rel (ty_rel rho bound A) a a' ->
  locally_closed_tm a -> locally_closed_tm a' ->
  may_rel (ty_rel rho bound B) (tm_app f a) (tm_app f' a').
Proof.
  intros rho bound A B f f' a a' Hf Ha Hla Hla'.
  destruct Hf as (fv & fw & Hf1 & Hf2 & Hfv & Hfw & Hfun).
  destruct Ha as (av & aw & Ha1 & Ha2 & Hav & Haw & Hab).
  destruct Hfun as (Hfv' & Hfw' & Happly).
  assert (Hout := Happly av aw Hab).
  destruct Hout as (rv & rw & Hr1 & Hr2 & Hrv & Hrw & Hrel).
  exists rv, rw; repeat split; try assumption.
  - eapply multi_trans with (u := tm_app fv a).
    + apply multi_app_left; [exact Hf1|exact Hla].
    + eapply multi_trans with (u := tm_app fv av).
      * apply multi_app_right; [exact Hfv|exact Ha1].
      * exact Hr1.
  - eapply multi_trans with (u := tm_app fw a').
    + apply multi_app_left; [exact Hf2|exact Hla'].
    + eapply multi_trans with (u := tm_app fw aw).
      * apply multi_app_right; [exact Hfw|exact Ha2].
      * exact Hr2.
Qed.

Lemma may_rel_tapp : forall rho bound T f f' A B R,
  may_rel (ty_rel rho bound (Ty_All T)) f f' ->
  locally_closed_ty A -> locally_closed_ty B -> rel_ok R ->
  may_rel (ty_rel rho (bound_push R bound) T)
    (tm_tapp f A) (tm_tapp f' B).
Proof.
  intros rho bound T f f' A B R Hf HA HB HR.
  destruct Hf as (fv & fw & Hf1 & Hf2 & Hfv & Hfw & Hfun).
  destruct Hfun as (Hfv' & Hfw' & Happly).
  assert (Hout := Happly A B R HA HB HR).
  destruct Hout as (rv & rw & Hr1 & Hr2 & Hrv & Hrw & Hrel).
  exists rv, rw; repeat split; try assumption.
  - eapply multi_trans.
    + apply multi_tapp_ctx with (A := A); [exact Hf1|exact HA].
    + exact Hr1.
  - eapply multi_trans.
    + apply multi_tapp_ctx with (A := B); [exact Hf2|exact HB].
    + exact Hr2.
Qed.

Lemma may_rel_recrec : forall rho bound T n b b' s s',
  ty_rel rho bound T b b' ->
  ty_rel rho bound (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s s' ->
  value b -> value b' -> value s -> value s' ->
  may_rel (ty_rel rho bound T)
    (tm_natrec (numeral n) b s) (tm_natrec (numeral n) b' s').
Proof.
  intros rho bound T n; induction n; intros b b' s s' Hb Hs Hvb Hvb' Hvs Hvs'.
  - exists b, b'; repeat split; try assumption.
    + eapply multi_step; [apply ST_RecZero; assumption|constructor].
    + eapply multi_step; [apply ST_RecZero; assumption|constructor].
  - assert (Hsm : may_rel
      (ty_rel rho bound (Ty_Arrow Ty_Nat (Ty_Arrow T T))) s s').
    { exists s, s'; split; [constructor|]. split; [constructor|].
      split; [exact Hvs|]. split; [exact Hvs'|exact Hs]. }
    assert (Hnm : may_rel (ty_rel rho bound Ty_Nat) (numeral n) (numeral n)).
    { exists (numeral n), (numeral n); split; [constructor|]. split; [constructor|].
      split; [apply numeral_value|]. split; [apply numeral_value|].
      exists n; split; reflexivity. }
    assert (Hinner : may_rel
      (ty_rel rho bound (Ty_Arrow T T))
      (tm_app s (numeral n)) (tm_app s' (numeral n))).
    { eapply may_rel_app with (rho := rho) (bound := bound)
        (A := Ty_Nat) (B := Ty_Arrow T T) (f := s) (f' := s')
        (a := numeral n) (a' := numeral n).
      - exact Hsm.
      - exact Hnm.
      - apply value_lc, numeral_value.
      - apply value_lc, numeral_value. }
    assert (Hrec : may_rel (ty_rel rho bound T)
       (tm_natrec (numeral n) b s) (tm_natrec (numeral n) b' s')).
    { apply IHn; assumption. }
    assert (Hlc : locally_closed_tm (tm_natrec (numeral n) b s)).
    { constructor; [apply value_lc, numeral_value|apply value_lc; assumption|apply value_lc; assumption]. }
    assert (Hlc' : locally_closed_tm (tm_natrec (numeral n) b' s')).
    { constructor; [apply value_lc, numeral_value|apply value_lc; assumption|apply value_lc; assumption]. }
    assert (Happs := may_rel_app rho bound T T
      (tm_app s (numeral n)) (tm_app s' (numeral n))
      (tm_natrec (numeral n) b s) (tm_natrec (numeral n) b' s')
      Hinner Hrec Hlc Hlc').
    destruct Happs as (rv & rw & Hr1 & Hr2 & Hrv & Hrw & Hrel).
    exists rv, rw; repeat split; try assumption.
    + eapply multi_trans.
      * eapply multi_step; [apply ST_RecSucc; try apply numeral_numeric; assumption|constructor].
      * exact Hr1.
    + eapply multi_trans.
      * eapply multi_step; [apply ST_RecSucc; try apply numeral_numeric; assumption|constructor].
      * exact Hr2.
Qed.

Lemma may_rel_natrec : forall rho bound T n n' b b' s s',
  may_rel (ty_rel rho bound Ty_Nat) n n' ->
  may_rel (ty_rel rho bound T) b b' ->
  may_rel (ty_rel rho bound
    (Ty_Arrow Ty_Nat (Ty_Arrow T T))) s s' ->
  locally_closed_tm n -> locally_closed_tm n' ->
  locally_closed_tm b -> locally_closed_tm b' ->
  locally_closed_tm s -> locally_closed_tm s' ->
  may_rel (ty_rel rho bound T)
    (tm_natrec n b s) (tm_natrec n' b' s').
Proof.
  intros rho bound T n n' b b' s s' Hn Hb Hs Hln Hln' Hlb Hlb' Hls Hls'.
  destruct Hn as (nv & nw & Hn1 & Hn2 & Hnv & Hnw & Hnr).
  destruct Hnr as [m [-> ->]].
  destruct Hb as (bv & bw & Hb1 & Hb2 & Hbv & Hbw & Hbr).
  destruct Hs as (sv & sw & Hs1 & Hs2 & Hsv & Hsw & Hsr).
  assert (HL : multi (tm_natrec n b s) (tm_natrec (numeral m) bv sv)).
  { eapply multi_trans.
    - eapply multi_rec_arg_ctx; [exact Hn1|exact Hlb|exact Hls].
    - eapply multi_trans.
      + apply multi_rec_base_ctx; [apply numeral_numeric|exact Hb1|exact Hls].
      + apply multi_rec_step_ctx; [apply numeral_numeric|exact Hbv|exact Hs1]. }
  assert (HR : multi (tm_natrec n' b' s') (tm_natrec (numeral m) bw sw)).
  { eapply multi_trans.
    - eapply multi_rec_arg_ctx; [exact Hn2|exact Hlb'|exact Hls'].
    - eapply multi_trans.
      + apply multi_rec_base_ctx; [apply numeral_numeric|exact Hb2|exact Hls'].
      + apply multi_rec_step_ctx; [apply numeral_numeric|exact Hbw|exact Hs2]. }
  assert (Hfin := may_rel_recrec rho bound T m bv bw sv sw Hbr Hsr Hbv Hbw Hsv Hsw).
  destruct Hfin as (rv & rw & Hfin1 & Hfin2 & Hrv & Hrw & Hrel).
  exists rv, rw; repeat split; try assumption.
  - eapply multi_trans; [exact HL|exact Hfin1].
  - eapply multi_trans; [exact HR|exact Hfin2].
Qed.

Definition env_rel (Delta : ty_context) (Gamma : context)
  (theta1 theta2 : ty_env) (rho : rel_env) (xi1 xi2 : atom -> tm) : Prop :=
  (forall X, In X Delta -> locally_closed_ty (theta1 X)) /\
  (forall X, In X Delta -> locally_closed_ty (theta2 X)) /\
  (forall x T, lookup_context x Gamma = Some T ->
      ty_rel rho (fun _ => fun _ _ => False) T (xi1 x) (xi2 x)).

Lemma lc_ty_close : forall K T,
  lc_ty_at K T -> forall theta, ty_env_ok theta ->
  lc_ty_at K (close_ty theta T).
Proof.
  intros K T Hlc; induction Hlc; intros theta Hok; simpl.
  - constructor; assumption.
  - eapply lc_ty_weaken with (K1 := 0); [lia|apply Hok].
  - constructor; [eapply IHHlc1|eapply IHHlc2]; assumption.
  - constructor. eapply IHHlc; assumption.
  - constructor.
  - constructor.
Qed.

Lemma lc_tm_close : forall K k t,
  lc_tm_at K k t -> forall theta xi,
  ty_env_ok theta -> term_env_ok xi ->
  lc_tm_at K k (close_tm theta xi t).
Proof.
  intros K k t Hlc; induction Hlc; intros theta xi Htheta Hxi; simpl.
  - constructor; assumption.
  - eapply lc_tm_type_weaken with (K1 := 0); [lia|].
    eapply lc_tm_weaken with (k1 := 0); [lia|apply value_lc, Hxi].
  - constructor.
    + eapply lc_ty_close; eauto.
    + eapply IHHlc; eauto.
  - constructor; [eapply IHHlc1|eapply IHHlc2]; eauto.
  - constructor. eapply IHHlc; eauto.
  - constructor.
    + eapply IHHlc; eauto.
    + eapply lc_ty_close; eauto.
  - constructor.
  - constructor.
  - constructor; [eapply IHHlc1|eapply IHHlc2|eapply IHHlc3]; eauto.
  - constructor.
  - constructor. eapply IHHlc; eauto.
  - constructor; [eapply IHHlc1|eapply IHHlc2|eapply IHHlc3]; eauto.
  - constructor; [eapply IHHlc1|eapply IHHlc2]; eauto.
Qed.

Lemma close_typed_lc : forall Delta Gamma t T theta xi,
  has_type Delta Gamma t T -> ty_env_ok theta -> term_env_ok xi ->
  locally_closed_tm (close_tm theta xi t).
Proof.
  intros Delta Gamma t T theta xi Hty Htheta Hxi.
  eapply lc_tm_close with (K := 0) (k := 0);
    [exact (has_type_lc Delta Gamma t T Hty)|exact Htheta|exact Hxi].
Qed.

Lemma env_rel_update_term : forall Delta G theta1 theta2 rho xi1 xi2 x A a b,
  env_rel Delta G theta1 theta2 rho xi1 xi2 ->
  ~ In x (ctx_vars G) ->
  ty_rel rho (fun _ => fun _ _ => False) A a b ->
  env_rel Delta (update G x A) theta1 theta2 rho
    (xi_update xi1 x a) (xi_update xi2 x b).
Proof.
  intros Delta G theta1 theta2 rho xi1 xi2 x A a b [Htheta1 [Htheta2 Hctx]] Hfresh Hab.
  split; [exact Htheta1|]. split; [exact Htheta2|].
  intros y T Hlook.
  rewrite lookup_update_eq in Hlook.
  destruct (Nat.eqb y x) eqn:E.
  - inversion Hlook; subst T. unfold xi_update. rewrite E. exact Hab.
  - specialize (Hctx y T Hlook). unfold xi_update.
    rewrite E. exact Hctx.
Qed.

Lemma env_rel_update_type : forall Delta G theta1 theta2 rho xi1 xi2 X A B R,
  env_rel Delta G theta1 theta2 rho xi1 xi2 ->
  ~ In X Delta ->
  (forall x T, lookup_context x G = Some T -> ~ In X (ty_fv T)) ->
  locally_closed_ty A -> locally_closed_ty B ->
  env_rel (X :: Delta) G (ty_update theta1 X A) (ty_update theta2 X B)
    (rel_update rho X R) xi1 xi2.
Proof.
  intros Delta G theta1 theta2 rho xi1 xi2 X A B R
    [Hth1 [Hth2 Hctx]] HfreshD HfreshG HA HB.
  split.
  - intros Y HY. simpl in HY. destruct HY as [<-|HY].
    + unfold ty_update; rewrite Nat.eqb_refl; exact HA.
    + unfold ty_update. destruct (Nat.eqb Y X) eqn:E.
      * apply Nat.eqb_eq in E; subst; contradiction.
      * apply Hth1; exact HY.
  - split.
    + intros Y HY. simpl in HY. destruct HY as [<-|HY].
      * unfold ty_update; rewrite Nat.eqb_refl; exact HB.
      * unfold ty_update. destruct (Nat.eqb Y X) eqn:E.
        -- apply Nat.eqb_eq in E; subst; contradiction.
        -- apply Hth2; exact HY.
    + intros x T Hlook.
      assert (HX : ~ In X (ty_fv T)) by (apply HfreshG with (x := x) (T := T); exact Hlook).
      apply (proj2 (ty_rel_update_fresh T rho
        (fun _ => fun _ _ => False) X R HX (xi1 x) (xi2 x))).
      apply Hctx with (x := x) (T := T); exact Hlook.
Qed.

Lemma ty_env_ok_update : forall theta X U,
  ty_env_ok theta -> locally_closed_ty U ->
  ty_env_ok (ty_update theta X U).
Proof.
  intros theta X U Hok HU Y; unfold ty_update.
  destruct (Nat.eqb Y X); [exact HU|apply Hok].
Qed.

Lemma ty_rel_ok : forall rho bound T,
  rel_env_ok rho -> bound_env_ok bound ->
  forall v w, ty_rel rho bound T v w -> value v /\ value w.
Proof.
  intros rho bound T; induction T; intros Hrho Hbound v w Hrel; simpl in *.
  - apply Hbound with (i := n); exact Hrel.
  - apply Hrho with (X := a); exact Hrel.
  - tauto.
  - tauto.
  - destruct Hrel as [[-> ->]|[-> ->]]; split; constructor.
  - destruct Hrel as [n [-> ->]]; split; apply v_nat; induction n; simpl; constructor; assumption.
Qed.

Lemma rel_env_ok_update : forall rho X R,
  rel_env_ok rho -> rel_ok R -> rel_env_ok (rel_update rho X R).
Proof.
  intros rho X R Hok HR Y; unfold rel_update.
  destruct (Nat.eqb Y X); auto.
Qed.
Lemma term_env_ok_update : forall xi x v,
  term_env_ok xi -> value v -> term_env_ok (xi_update xi x v).
Proof.
  intros xi x v Hxi Hv y; unfold xi_update.
  destruct (Nat.eqb y x); auto.
Qed.
Lemma ty_rel_bound_zero_push : forall rho T R,
  forall v w,
  ty_rel rho (bound_update empty_bound 0 R) T v w <->
  ty_rel rho (bound_push R empty_bound) T v w.
Proof.
  intros rho T R v w.
  apply ty_rel_bound_ext.
  intros i a b; unfold bound_update, bound_push, empty_bound.
  destruct i; simpl; tauto.
Qed.

Lemma open_tm_rec_lc : forall K k t u,
  lc_tm_at K k t -> open_tm_rec k u t = t.
Proof.
  intros K k t; revert K k; induction t; intros K k u Hlc; simpl.
  - inversion Hlc; subst. destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; lia.
    + reflexivity.
  - reflexivity.
  - inversion Hlc; subst. f_equal. eapply IHt; eauto.
  - inversion Hlc; subst. f_equal; [eapply IHt1|eapply IHt2]; eauto.
  - inversion Hlc; subst. f_equal. eapply IHt; eauto.
  - inversion Hlc; subst. f_equal. eapply IHt; eauto.
  - reflexivity.
  - reflexivity.
  - inversion Hlc; subst. f_equal; [eapply IHt1|eapply IHt2|eapply IHt3]; eauto.
  - reflexivity.
  - inversion Hlc; subst. f_equal. eapply IHt; eauto.
  - inversion Hlc; subst. f_equal; [eapply IHt1|eapply IHt2|eapply IHt3]; eauto.
  - inversion Hlc; subst. f_equal; [eapply IHt1|eapply IHt2]; eauto.
Qed.

Lemma close_open_tm_rec : forall t k theta xi x v,
  ~ In x (tm_fv t) -> term_env_ok xi -> value v ->
  close_tm theta (xi_update xi x v) (open_tm_rec k (tm_fvar x) t) =
    open_tm_rec k v (close_tm theta xi t).
Proof.
  induction t; intros k theta xi x v Hfresh Hxi Hv; simpl in *.
  - destruct (Nat.eqb k n) eqn:E; simpl.
    + unfold xi_update; rewrite Nat.eqb_refl; reflexivity.
    + reflexivity.
  - simpl in Hfresh. assert (Hneq : x <> a) by (intro E; subst; apply Hfresh; simpl; auto).
    unfold xi_update. destruct (Nat.eqb a x) eqn:E.
    + apply Nat.eqb_eq in E; subst; exfalso; apply Hneq; reflexivity.
    +
    simpl. symmetry. eapply open_tm_rec_lc with (K := 0).
    eapply lc_tm_weaken with (k1 := 0) (k2 := k).
    * apply Nat.le_0_l.
    * apply value_lc, Hxi.
  - f_equal. eapply IHt; eauto.
  - f_equal.
    + eapply IHt1; eauto using notin_app_l.
    + eapply IHt2; eauto using notin_app_r.
  - f_equal. eapply IHt; eauto.
  - f_equal. eapply IHt; eauto.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + eapply IHt1; [exact (notin_app_l atom x (tm_fv t1) (tm_fv t2 ++ tm_fv t3) Hfresh)|exact Hxi|exact Hv].
    + eapply IHt2; [exact (notin_app_l atom x (tm_fv t2) (tm_fv t3) (notin_app_r atom x (tm_fv t1) (tm_fv t2 ++ tm_fv t3) Hfresh))|exact Hxi|exact Hv].
    + eapply IHt3; [exact (notin_app_r atom x (tm_fv t2) (tm_fv t3) (notin_app_r atom x (tm_fv t1) (tm_fv t2 ++ tm_fv t3) Hfresh))|exact Hxi|exact Hv].
  - reflexivity.
  - f_equal. eapply IHt; eauto.
  - f_equal.
    + eapply IHt1; [exact (notin_app_l atom x (tm_fv t1) (tm_fv t2 ++ tm_fv t3) Hfresh)|exact Hxi|exact Hv].
    + eapply IHt2; [exact (notin_app_l atom x (tm_fv t2) (tm_fv t3) (notin_app_r atom x (tm_fv t1) (tm_fv t2 ++ tm_fv t3) Hfresh))|exact Hxi|exact Hv].
    + eapply IHt3; [exact (notin_app_r atom x (tm_fv t2) (tm_fv t3) (notin_app_r atom x (tm_fv t1) (tm_fv t2 ++ tm_fv t3) Hfresh))|exact Hxi|exact Hv].
  - f_equal.
    + eapply IHt1; eauto using notin_app_l.
    + eapply IHt2; eauto using notin_app_r.
Qed.


Lemma fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall theta1 theta2 rho xi1 xi2,
    ty_env_ok theta1 -> ty_env_ok theta2 ->
    rel_env_ok rho -> term_env_ok xi1 -> term_env_ok xi2 ->
    env_rel Delta Gamma theta1 theta2 rho xi1 xi2 ->
    may_rel (ty_rel rho empty_bound T)
      (close_tm theta1 xi1 t) (close_tm theta2 xi2 t).
Proof.
  intros Delta Gamma t T Hty; induction Hty;
    intros theta1 theta2 rho xi1 xi2 Htheta1 Htheta2 Hrho Hxi1 Hxi2 Henv.
  - destruct Henv as [_ [_ Hctx]].
    pose proof (Hctx x T H) as Hrel.
    pose proof (ty_rel_ok rho empty_bound T Hrho empty_bound_ok
      (xi1 x) (xi2 x) Hrel) as [Hv Hw].
    exists (xi1 x), (xi2 x); repeat split; try assumption; constructor.
  - destruct Henv as [Hctx1 [Hctx2 Hctx]].
    assert (Hlc1 : locally_closed_tm (close_tm theta1 xi1 (tm_abs T1 t2))).
    { eapply close_typed_lc; [eapply T_Abs; eauto|exact Htheta1|exact Hxi1]. }
    assert (Hlc2 : locally_closed_tm (close_tm theta2 xi2 (tm_abs T1 t2))).
    { eapply close_typed_lc; [eapply T_Abs; eauto|exact Htheta2|exact Hxi2]. }
    exists (tm_abs (close_ty theta1 T1) (close_tm theta1 xi1 t2)),
      (tm_abs (close_ty theta2 T1) (close_tm theta2 xi2 t2)).
    split; [constructor|]. split; [constructor|].
    split; [apply v_abs; exact Hlc1|]. split; [apply v_abs; exact Hlc2|].
    simpl. split; [apply v_abs; exact Hlc1|]. split; [apply v_abs; exact Hlc2|].
    intros a b Hab.
    pose proof (ty_rel_ok rho empty_bound T1 Hrho empty_bound_ok a b Hab) as [Hva Hvb].
    destruct (fresh_atom (L ++ (ctx_vars Gamma ++ tm_fv t2))) as [x Hx].
    assert (HnotL : ~ In x L) by (eapply notin_app_l; exact Hx).
    assert (HnotGamma : ~ In x (ctx_vars Gamma))
      by (eapply notin_app_l; eapply notin_app_r; exact Hx).
    assert (HnotBody : ~ In x (tm_fv t2))
      by (eapply notin_app_r; eapply notin_app_r; exact Hx).
    assert (Henv0 : env_rel Delta Gamma theta1 theta2 rho xi1 xi2)
      by (repeat split; assumption).
    assert (Henv' := env_rel_update_term Delta Gamma theta1 theta2 rho xi1 xi2 x T1 a b Henv0 HnotGamma Hab).
    assert (Hxi1' := term_env_ok_update xi1 x a Hxi1 Hva).
    assert (Hxi2' := term_env_ok_update xi2 x b Hxi2 Hvb).
    assert (Hbody : may_rel (ty_rel rho empty_bound T2)
      (close_tm theta1 (xi_update xi1 x a) (open_tm t2 (tm_fvar x)))
      (close_tm theta2 (xi_update xi2 x b) (open_tm t2 (tm_fvar x)))).
    { match goal with
      | Hih : forall y, ~ In y L -> _ |- _ =>
          eapply Hih; eauto
      end. }
    unfold open_tm in Hbody.
    rewrite (close_open_tm_rec t2 0 theta1 xi1 x a HnotBody Hxi1 Hva) in Hbody.
    rewrite (close_open_tm_rec t2 0 theta2 xi2 x b HnotBody Hxi2 Hvb) in Hbody.
    destruct Hbody as (rv & rw & Hr1 & Hr2 & Hrv & Hrw & Hrel).
    exists rv, rw; repeat split; try assumption.
    + eapply multi_trans.
      * eapply multi_step; [apply ST_AppAbs; [exact Hlc1|exact Hva]|constructor].
      * exact Hr1.
    + eapply multi_trans.
      * eapply multi_step; [apply ST_AppAbs; [exact Hlc2|exact Hvb]|constructor].
      * exact Hr2.
  - destruct Henv as [Hctx1 [Hctx2 Hctx]].
    assert (Henv0 : env_rel Delta Gamma theta1 theta2 rho xi1 xi2)
      by (repeat split; assumption).
    assert (Harglc1 : locally_closed_tm (close_tm theta1 xi1 t2)).
    { eapply close_typed_lc; eauto. }
    assert (Harglc2 : locally_closed_tm (close_tm theta2 xi2 t2)).
    { eapply close_typed_lc; eauto. }
    eapply may_rel_app.
    + eapply IHHty1; eauto.
    + eapply IHHty2; eauto.
    + exact Harglc1.
    + exact Harglc2.
  - destruct Henv as [Hctx1 [Hctx2 Hctx]].
    assert (Hlc1 : locally_closed_tm (close_tm theta1 xi1 (tm_tabs t))).
    { eapply close_typed_lc; [eapply T_TAbs; eauto|exact Htheta1|exact Hxi1]. }
    assert (Hlc2 : locally_closed_tm (close_tm theta2 xi2 (tm_tabs t))).
    { eapply close_typed_lc; [eapply T_TAbs; eauto|exact Htheta2|exact Hxi2]. }
    exists (tm_tabs (close_tm theta1 xi1 t)), (tm_tabs (close_tm theta2 xi2 t)).
    split; [constructor|]. split; [constructor|].
    split; [apply v_tabs; exact Hlc1|]. split; [apply v_tabs; exact Hlc2|].
    simpl. split; [apply v_tabs; exact Hlc1|]. split; [apply v_tabs; exact Hlc2|].
    intros A B R HA HB HR.
    destruct (fresh_atom (L ++ (Delta ++ (ctx_tfv Gamma ++
      (tm_tfv t ++ (ty_fv T ++ ctx_tfv Gamma)))))) as [X HX].
    assert (HX_L : ~ In X L) by (eapply notin_app_l; exact HX).
    assert (HX_D : ~ In X Delta)
      by (eapply notin_app_l; eapply notin_app_r; exact HX).
    assert (HX_G : ~ In X (ctx_tfv Gamma))
      by (eapply notin_app_l; eapply notin_app_r; eapply notin_app_r; exact HX).
    assert (HX_tm : ~ In X (tm_tfv t))
      by (eapply notin_app_l; eapply notin_app_r; eapply notin_app_r; eapply notin_app_r; exact HX).
    assert (HX_T : ~ In X (ty_fv T))
      by (eapply notin_app_l; eapply notin_app_r; eapply notin_app_r; eapply notin_app_r; eapply notin_app_r; exact HX).
    assert (Henv' : env_rel (X :: Delta) Gamma
      (ty_update theta1 X A) (ty_update theta2 X B)
      (rel_update rho X R) xi1 xi2).
    { assert (Henv0 : env_rel Delta Gamma theta1 theta2 rho xi1 xi2)
        by (repeat split; assumption).
      eapply env_rel_update_type.
      - exact Henv0.
      - exact HX_D.
      - intros x U Hlook Hin.
        apply HX_G. eapply lookup_tfv_in_ctx; eauto.
      - exact HA.
      - exact HB. }
    assert (Htheta1' := ty_env_ok_update theta1 X A Htheta1 HA).
    assert (Htheta2' := ty_env_ok_update theta2 X B Htheta2 HB).
    assert (Hrho' := rel_env_ok_update rho X R Hrho HR).
    assert (Hbody : may_rel
      (ty_rel (rel_update rho X R) empty_bound (open_ty T (Ty_FVar X)))
      (close_tm (ty_update theta1 X A) xi1 (open_tm_ty t (Ty_FVar X)))
      (close_tm (ty_update theta2 X B) xi2 (open_tm_ty t (Ty_FVar X)))).
    { match goal with
      | Hih : forall Y, ~ In Y L -> _ |- _ =>
          eapply Hih; eauto
      end. }
    assert (Hrelconv : forall p q,
      ty_rel (rel_update rho X R) empty_bound (open_ty T (Ty_FVar X)) p q <->
      ty_rel rho (bound_push R empty_bound) T p q).
    { intros p q.
      eapply iff_trans.
      - apply ty_rel_open_fvar; exact HX_T.
      - apply ty_rel_bound_zero_push. }
    assert (Hbody' : may_rel (ty_rel rho (bound_push R empty_bound) T)
      (open_tm_ty (close_tm theta1 xi1 t) A)
      (open_tm_ty (close_tm theta2 xi2 t) B)).
    { unfold open_tm_ty in Hbody |- *.
      rewrite (close_tm_ty_open_fvar t 0 theta1 xi1 X A Htheta1 Hxi1 HX_tm) in Hbody.
      rewrite (close_tm_ty_open_fvar t 0 theta2 xi2 X B Htheta2 Hxi2 HX_tm) in Hbody.
      apply (proj1 (may_rel_ext _ _ _ _ Hrelconv)); exact Hbody. }
    destruct Hbody' as (rv & rw & Hr1 & Hr2 & Hrv & Hrw & Hrel).
    exists rv, rw; repeat split; try assumption.
    + eapply multi_trans.
      * eapply multi_step; [apply ST_TAppTabs; [exact Hlc1|exact HA]|constructor].
      * exact Hr1.
    + eapply multi_trans.
      * eapply multi_step; [apply ST_TAppTabs; [exact Hlc2|exact HB]|constructor].
      * exact Hr2.
  - destruct Henv as [Hctx1 [Hctx2 Hctx]].
    assert (Henv0 : env_rel Delta Gamma theta1 theta2 rho xi1 xi2)
      by (repeat split; assumption).
    pose proof (IHHty theta1 theta2 rho xi1 xi2 Htheta1 Htheta2 Hrho Hxi1 Hxi2 Henv0) as Hfun.
    assert (HUlc : locally_closed_ty U).
    { match goal with Hwf : wf_ty Delta U |- _ => exact (wf_ty_lc Delta U Hwf) end. }
    assert (HU1 : locally_closed_ty (close_ty theta1 U)).
    { apply lc_ty_close; assumption. }
    assert (HU2 : locally_closed_ty (close_ty theta2 U)).
    { apply lc_ty_close; assumption. }
    assert (HRU : rel_ok (ty_rel rho empty_bound U)).
    { intros p q Hp. exact (ty_rel_ok rho empty_bound U Hrho empty_bound_ok p q Hp). }
    pose proof (may_rel_tapp rho empty_bound T
      (close_tm theta1 xi1 t) (close_tm theta2 xi2 t)
      (close_ty theta1 U) (close_ty theta2 U)
      (ty_rel rho empty_bound U) Hfun HU1 HU2 HRU) as Hres.
    assert (Hconv : forall p q,
      ty_rel rho empty_bound (open_ty T U) p q <->
      ty_rel rho (bound_push (ty_rel rho empty_bound U) empty_bound) T p q).
    { intros p q.
      eapply iff_trans.
      - apply ty_rel_open_subst; exact HUlc.
      - apply ty_rel_bound_zero_push. }
    apply (proj2 (may_rel_ext _ _ _ _ Hconv)).
    exact Hres.
  - exists tm_true, tm_true; split; [constructor|]. split; [constructor|].
    split; [apply v_true|]. split; [apply v_true|]. left; auto.
  - exists tm_false, tm_false; split; [constructor|]. split; [constructor|].
    split; [apply v_false|]. split; [apply v_false|]. right; auto.
  - destruct Henv as [Hctx1 [Hctx2 Hctx]].
    assert (Henv0 : env_rel Delta Gamma theta1 theta2 rho xi1 xi2)
      by (repeat split; assumption).
    pose proof (IHHty1 theta1 theta2 rho xi1 xi2 Htheta1 Htheta2 Hrho Hxi1 Hxi2 Henv0) as Hcond.
    pose proof (IHHty2 theta1 theta2 rho xi1 xi2 Htheta1 Htheta2 Hrho Hxi1 Hxi2 Henv0) as Hthen.
    pose proof (IHHty3 theta1 theta2 rho xi1 xi2 Htheta1 Htheta2 Hrho Hxi1 Hxi2 Henv0) as Helse.
    destruct Hcond as (c1 & c2 & Hc1 & Hc2 & Hcv1 & Hcv2 & Hcr).
    assert (HL2 : locally_closed_tm (close_tm theta1 xi1 t2)) by (eapply close_typed_lc; eauto).
    assert (HL3 : locally_closed_tm (close_tm theta1 xi1 t3)) by (eapply close_typed_lc; eauto).
    assert (HR2 : locally_closed_tm (close_tm theta2 xi2 t2)) by (eapply close_typed_lc; eauto).
    assert (HR3 : locally_closed_tm (close_tm theta2 xi2 t3)) by (eapply close_typed_lc; eauto).
    destruct Hcr as [[-> ->]|[-> ->]].
    + destruct Hthen as (v1 & v2 & Hv1 & Hv2 & Hvv1 & Hvv2 & Hvr).
      exists v1, v2; repeat split; try assumption.
      * eapply multi_trans.
        -- apply multi_if_ctx; [exact Hc1|exact HL2|exact HL3].
        -- eapply multi_trans; [eapply multi_step; [apply ST_IfTrue; assumption|constructor]|exact Hv1].
      * eapply multi_trans.
        -- apply multi_if_ctx; [exact Hc2|exact HR2|exact HR3].
        -- eapply multi_trans; [eapply multi_step; [apply ST_IfTrue; eauto|constructor]|exact Hv2].
    + destruct Helse as (v1 & v2 & Hv1 & Hv2 & Hvv1 & Hvv2 & Hvr).
      exists v1, v2; repeat split; try assumption.
      * eapply multi_trans.
        -- apply multi_if_ctx; [exact Hc1|exact HL2|exact HL3].
        -- eapply multi_trans; [eapply multi_step; [apply ST_IfFalse; eauto|constructor]|exact Hv1].
      * eapply multi_trans.
        -- apply multi_if_ctx; [exact Hc2|exact HR2|exact HR3].
        -- eapply multi_trans; [eapply multi_step; [apply ST_IfFalse; eauto|constructor]|exact Hv2].
  - exists tm_zero, tm_zero.
    split; [constructor|]. split; [constructor|].
    split; [apply v_nat; constructor|]. split; [apply v_nat; constructor|].
    exists 0; split; reflexivity.
  - destruct Henv as [Hctx1 [Hctx2 Hctx]].
    assert (Henv0 : env_rel Delta Gamma theta1 theta2 rho xi1 xi2)
      by (repeat split; assumption).
    pose proof (IHHty theta1 theta2 rho xi1 xi2 Htheta1 Htheta2 Hrho Hxi1 Hxi2 Henv0) as Hn.
    destruct Hn as (n1 & n2 & Hn1 & Hn2 & Hnv1 & Hnv2 & Hnr).
    destruct Hnr as [m [-> ->]].
    exists (tm_succ (numeral m)), (tm_succ (numeral m)); repeat split.
    + apply multi_succ_ctx; exact Hn1.
    + apply multi_succ_ctx; exact Hn2.
    + change (value (numeral (S m))); apply numeral_value.
    + change (value (numeral (S m))); apply numeral_value.
    + exists (S m); simpl; auto.
  - destruct Henv as [Hctx1 [Hctx2 Hctx]].
    assert (Henv0 : env_rel Delta Gamma theta1 theta2 rho xi1 xi2)
      by (repeat split; assumption).
    pose proof (IHHty1 theta1 theta2 rho xi1 xi2 Htheta1 Htheta2 Hrho Hxi1 Hxi2 Henv0) as Hn.
    pose proof (IHHty2 theta1 theta2 rho xi1 xi2 Htheta1 Htheta2 Hrho Hxi1 Hxi2 Henv0) as Hb.
    pose proof (IHHty3 theta1 theta2 rho xi1 xi2 Htheta1 Htheta2 Hrho Hxi1 Hxi2 Henv0) as Hs.
    eapply may_rel_natrec; eauto using close_typed_lc.
  - destruct Henv as [Hctx1 [Hctx2 Hctx]].
    assert (Henv0 : env_rel Delta Gamma theta1 theta2 rho xi1 xi2)
      by (repeat split; assumption).
    pose proof (IHHty1 theta1 theta2 rho xi1 xi2 Htheta1 Htheta2 Hrho Hxi1 Hxi2 Henv0) as Hleft.
    pose proof (IHHty2 theta1 theta2 rho xi1 xi2 Htheta1 Htheta2 Hrho Hxi1 Hxi2 Henv0) as Hright.
    destruct Hleft as (v1 & v2 & Hv1 & Hv2 & Hvv1 & Hvv2 & Hrel).
    exists v1, v2; repeat split; try assumption.
    + eapply multi_trans.
      * eapply multi_step; [apply ST_ChoiceLeft; eapply close_typed_lc; eauto|constructor].
      * exact Hv1.
    + eapply multi_trans.
      * eapply multi_step; [apply ST_ChoiceLeft; eapply close_typed_lc; eauto|constructor].
      * exact Hv2.
Qed.

Lemma tm_fv_open_rec_keep : forall t k x y,
  ~ In x (tm_fv t) -> In y (tm_fv t) ->
  In y (tm_fv (open_tm_rec k (tm_fvar x) t)).
Proof.
  induction t; intros k x y Hx Hy; simpl in *;
    try contradiction; try assumption;
    repeat rewrite in_app_iff in *; intuition eauto.
Qed.

Lemma tm_fv_open_ty_rec : forall t k U, tm_fv (open_tm_ty_rec k U t) = tm_fv t.
Proof.
  induction t; intros k U; simpl; try reflexivity;
    try (rewrite IHt; reflexivity);
    try (rewrite IHt1, IHt2; reflexivity);
    try (rewrite IHt1, IHt2, IHt3; reflexivity).
Qed.

Lemma tm_fv_open_ty : forall t U, tm_fv (open_tm_ty t U) = tm_fv t.
Proof. intros; apply tm_fv_open_ty_rec. Qed.

Lemma has_type_fv_ctx : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall x, In x (tm_fv t) -> exists U, lookup_context x Gamma = Some U.
Proof.
  intros Delta Gamma t T Hty; induction Hty as
    [Delta Gamma x T Hlook Hwf
    |L Delta Gamma T1 t2 T2 Hwf Hbody IHbody
    |Delta Gamma t1 t2 T1 T2 Hty1 IHty1 Hty2 IHty2
    |L Delta Gamma t T Hbody IHbody
    |Delta Gamma t T U Hty IHty HwfU
    |Delta Gamma
    |Delta Gamma
    |Delta Gamma t1 t2 t3 T Hty1 IHty1 Hty2 IHty2 Hty3 IHty3
    |Delta Gamma
    |Delta Gamma n Hty IHty
    |Delta Gamma n b s T Hn IHn Hb IHb Hs IHs
    |Delta Gamma t1 t2 T Hty1 IHty1 Hty2 IHty2]; intros y Hy.
  - simpl in Hy. destruct Hy as [<-|[]]. eauto.
  - destruct (fresh_atom (L ++ (tm_fv t2 ++ ctx_vars Gamma))) as [x Hx].
    assert (HnotL : ~ In x L) by (eapply notin_app_l; exact Hx).
    assert (Hnotbody : ~ In x (tm_fv t2))
      by (eapply notin_app_l; eapply notin_app_r; exact Hx).
    assert (Hnotctx : ~ In x (ctx_vars Gamma))
      by (eapply notin_app_r; eapply notin_app_r; exact Hx).
    assert (Hyopen : In y (tm_fv (open_tm t2 (tm_fvar x)))).
    { unfold open_tm. eapply tm_fv_open_rec_keep; eauto. }
    destruct (IHbody x HnotL y Hyopen) as [U Hlook].
    exists U. rewrite lookup_update_eq in Hlook.
    assert (Hyx : y <> x).
    { intro E; subst; apply Hnotbody; exact Hy. }
    rewrite (proj2 (Nat.eqb_neq y x) Hyx) in Hlook.
    exact Hlook.
  - simpl in Hy. apply in_app_iff in Hy as [Hy|Hy].
    + eapply IHty1; eauto.
    + eapply IHty2; eauto.
  - destruct (fresh_atom L) as [X HX].
    simpl in Hy. rewrite <- (tm_fv_open_ty t (Ty_FVar X)) in Hy.
    exact (IHbody X HX y Hy).
  - simpl in Hy. eapply IHty; eauto.
  - simpl in Hy; contradiction.
  - simpl in Hy; contradiction.
  - simpl in Hy. apply in_app_iff in Hy as [Hy|Hy23].
    + eapply IHty1; eauto.
    + apply in_app_iff in Hy23 as [Hy|Hy].
      * eapply IHty2; eauto.
      * eapply IHty3; eauto.
  - simpl in Hy; contradiction.
  - simpl in Hy. eapply IHty; eauto.
  - simpl in Hy. apply in_app_iff in Hy as [Hy|Hy23].
    + eapply IHn; eauto.
    + apply in_app_iff in Hy23 as [Hy|Hy].
      * eapply IHb; eauto.
      * eapply IHs; eauto.
  - simpl in Hy. apply in_app_iff in Hy as [Hy|Hy].
    + eapply IHty1; eauto.
    + eapply IHty2; eauto.
Qed.

Definition identity_ty_env : ty_env := fun X => Ty_FVar X.
Definition zero_tm_env : atom -> tm := fun _ => tm_zero.

Lemma identity_ty_env_ok : ty_env_ok identity_ty_env.
Proof. intros X; constructor. Qed.
Lemma zero_tm_env_ok : term_env_ok zero_tm_env.
Proof. intros x; unfold zero_tm_env; apply v_nat; constructor. Qed.
Lemma close_ty_identity : forall T, close_ty identity_ty_env T = T.
Proof.
  induction T; simpl; try reflexivity;
    try rewrite IHT; try rewrite IHT1, IHT2; reflexivity.
Qed.

Lemma close_tm_identity_fresh : forall t,
  (forall x, ~ In x (tm_fv t)) ->
  close_tm identity_ty_env zero_tm_env t = t.
Proof.
  induction t; intros Hfresh; simpl; try reflexivity.
  - exfalso. apply (Hfresh a). simpl; auto.
  - f_equal.
    + apply close_ty_identity.
    + apply IHt. exact Hfresh.
  - f_equal.
    + apply IHt1. intros x Hx. apply (Hfresh x). simpl; apply in_or_app; left; exact Hx.
    + apply IHt2. intros x Hx. apply (Hfresh x). simpl; apply in_or_app; right; exact Hx.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal.
    + apply IHt. intros x Hx. apply (Hfresh x). simpl; exact Hx.
    + apply close_ty_identity.
  - f_equal.
    + apply IHt1. intros x Hx. apply (Hfresh x). simpl; apply in_or_app; left; exact Hx.
    + apply IHt2. intros x Hx. apply (Hfresh x). simpl; apply in_or_app; right; apply in_or_app; left; exact Hx.
    + apply IHt3. intros x Hx. apply (Hfresh x). simpl; apply in_or_app; right; apply in_or_app; right; exact Hx.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal.
    + apply IHt1. intros x Hx. apply (Hfresh x). simpl; apply in_or_app; left; exact Hx.
    + apply IHt2. intros x Hx. apply (Hfresh x). simpl; apply in_or_app; right; apply in_or_app; left; exact Hx.
    + apply IHt3. intros x Hx. apply (Hfresh x). simpl; apply in_or_app; right; apply in_or_app; right; exact Hx.
  - f_equal.
    + apply IHt1. intros x Hx. apply (Hfresh x). simpl; apply in_or_app; left; exact Hx.
    + apply IHt2. intros x Hx. apply (Hfresh x). simpl; apply in_or_app; right; exact Hx.
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
  intros t Hty U v HU Hv Hvt.
  assert (Hfresh : forall x, ~ In x (tm_fv t)).
  { intros x Hx. destruct (has_type_fv_ctx [] empty t
      (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) Hty x Hx) as [A HA].
    discriminate. }
  set (rho := (fun _ : atom => fun _ _ : tm => False)).
  assert (Henv : env_rel [] empty identity_ty_env identity_ty_env rho zero_tm_env zero_tm_env).
  { unfold env_rel. split.
    - intros X HX; inversion HX.
    - split.
      + intros X HX; inversion HX.
      + intros x A Hlook; simpl in Hlook; discriminate. }
  assert (Hfund : may_rel (ty_rel rho empty_bound
      (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0)))) t t).
  { pose proof (fundamental [] empty t
      (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) Hty
      identity_ty_env identity_ty_env rho zero_tm_env zero_tm_env
      identity_ty_env_ok identity_ty_env_ok
      (ltac:(intros X a b H; contradiction)) zero_tm_env_ok zero_tm_env_ok Henv) as H0.
    rewrite (close_tm_identity_fresh t Hfresh) in H0.
    exact H0.
  }
  destruct Hfund as (f & g & Htf & Htg & Hfv & Hgv & Hfg).
  assert (HUlc : locally_closed_ty U) by (eapply wf_ty_lc; eauto).
  assert (HR : rel_ok (fun a b => a = v /\ b = v)).
  { intros a b [-> ->]; split; exact Hv. }
  assert (Harg : may_rel (fun a b => a = v /\ b = v) v v).
  { exists v, v. split; [constructor|]. split; [constructor|]. split; [exact Hv|]. split; [exact Hv|]. split; reflexivity. }
  unfold ty_rel in Hfg.
  destruct Hfg as [_ [_ Hforall]].
  pose proof (Hforall U U (fun a b => a = v /\ b = v) HUlc HUlc HR) as Hinst.
  assert (Happ : may_rel (fun a b => a = v /\ b = v)
      (tm_app (tm_tapp f U) v) (tm_app (tm_tapp g U) v)).
  { eapply may_rel_app with
      (rho := rho) (bound := bound_push (fun a b => a = v /\ b = v) empty_bound)
      (A := Ty_BVar 0) (B := Ty_BVar 0).
    - exact Hinst.
    - exact Harg.
    - apply value_lc; exact Hv.
    - apply value_lc; exact Hv.
  }
  destruct Happ as (a & b & Ha & Hb & Hva & Hvb & Hab).
  destruct Hab as [-> ->].
  eapply multi_trans.
  - apply multi_app_left.
    + apply multi_tapp_ctx; [exact Htf|apply wf_ty_lc with (Delta := []); exact HU].
    + apply value_lc; exact Hv.
  - exact Ha.
Qed.

End SystemFParametricityIfNondeterminismRecursionHardTask.
