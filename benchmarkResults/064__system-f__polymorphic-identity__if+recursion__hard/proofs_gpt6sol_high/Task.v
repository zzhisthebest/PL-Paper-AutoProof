(** System F parametricity benchmark, Hard variant.
    Features: if-recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFParametricityIfRecursionHardTask.

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


Hint Constructors lc_ty_at lc_tm_at value : core.

Definition fresh (L : list atom) := S (fold_right Nat.max 0 L).

Lemma fresh_not_in : forall L, ~ In (fresh L) L.
Proof.
  assert (Hbound : forall L x, In x L -> x <= fold_right Nat.max 0 L).
  { induction L as [|a L IH]; intros x H; simpl in *; [tauto|].
    destruct H as [->|H]; [lia|]. specialize (IH x H). lia. }
  intros L H. specialize (Hbound L (fresh L) H).
  unfold fresh in Hbound. lia.
Qed.

Lemma lc_ty_open_inv : forall T k X,
  lc_ty_at k (open_ty_rec k (Ty_FVar X) T) -> lc_ty_at (S k) T.
Proof.
  induction T; intros k X H; simpl in H; try (inversion H; subst; constructor; eauto; fail).
  - destruct (Nat.eqb k n) eqn:E; constructor; [apply Nat.eqb_eq in E; lia|].
    inversion H; subst; lia.
Qed.

Lemma lc_tm_open_inv : forall t K k x,
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) -> lc_tm_at K (S k) t.
Proof.
  induction t; intros K k x H; simpl in H;
    try (inversion H; subst; constructor; eauto; fail).
  - destruct (Nat.eqb k n) eqn:E; constructor; [apply Nat.eqb_eq in E; lia|].
    inversion H; subst; lia.
Qed.

Lemma lc_tm_ty_open_inv : forall t K k X,
  lc_tm_at K k (open_tm_ty_rec K (Ty_FVar X) t) -> lc_tm_at (S K) k t.
Proof.
  induction t; intros K k X H; simpl in H;
    inversion H; subst; try (constructor; eauto; fail).
  - constructor; eauto using lc_ty_open_inv.
  - constructor; eauto using lc_ty_open_inv.
Qed.

Lemma wf_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H; induction H; unfold locally_closed_ty in *; eauto.
  - constructor. apply (lc_ty_open_inv T 0 (fresh L)).
    apply H0, fresh_not_in.
Qed.

Lemma typing_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T H; induction H; unfold locally_closed_tm in *; eauto.
  - constructor. exact (wf_lc _ _ H).
    apply (lc_tm_open_inv t2 0 0 (fresh L)).
    exact (H1 (fresh L) (fresh_not_in L)).
  - constructor. apply (lc_tm_ty_open_inv t 0 0 (fresh L)).
    apply H0, fresh_not_in.
  - constructor; eauto. exact (wf_lc _ _ H0).
Qed.

Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof.
  assert (Hnumeric : forall n, numeric_value n -> locally_closed_tm n).
  { intros n H; induction H; unfold locally_closed_tm in *; eauto. }
  intros v H; inversion H; subst; unfold locally_closed_tm; eauto using Hnumeric.
  exact (Hnumeric _ H0).
Qed.

Lemma multi_trans : forall a b c, a -->* b -> b -->* c -> a -->* c.
Proof.
  intros a b c H; induction H; eauto using multi.
Qed.

Lemma multi_app1 : forall a b c, a -->* b -> locally_closed_tm c ->
  tm_app a c -->* tm_app b c.
Proof.
  intros a b c H; induction H; eauto using multi, step.
Qed.

Lemma multi_app2 : forall a b c, value a -> b -->* c ->
  tm_app a b -->* tm_app a c.
Proof.
  intros a b c Ha H; induction H; eauto using multi, step.
Qed.

Lemma multi_tapp : forall a b U, a -->* b -> locally_closed_ty U ->
  tm_tapp a U -->* tm_tapp b U.
Proof.
  intros a b U H HU; induction H; eauto using multi, step.
Qed.

Lemma multi_if : forall a b c d, a -->* b ->
  locally_closed_tm c -> locally_closed_tm d ->
  tm_if a c d -->* tm_if b c d.
Proof.
  intros a b c d H Hc Hd; induction H; eauto using multi, step.
Qed.

Lemma multi_if_true : forall test yes no,
  test -->* tm_true -> locally_closed_tm yes -> locally_closed_tm no ->
  tm_if test yes no -->* yes.
Proof.
  intros test yes no Htest Hyes Hno.
  eapply multi_trans; [apply multi_if; eauto|].
  eapply multi_step; [apply ST_IfTrue; eauto|apply multi_refl].
Qed.

Lemma multi_if_false : forall test yes no,
  test -->* tm_false -> locally_closed_tm yes -> locally_closed_tm no ->
  tm_if test yes no -->* no.
Proof.
  intros test yes no Htest Hyes Hno.
  eapply multi_trans; [apply multi_if; eauto|].
  eapply multi_step; [apply ST_IfFalse; eauto|apply multi_refl].
Qed.

Lemma multi_succ : forall a b, a -->* b -> tm_succ a -->* tm_succ b.
Proof.
  intros a b H; induction H; eauto using multi, step.
Qed.

Lemma multi_rec_arg : forall a b c d, a -->* b ->
  locally_closed_tm c -> locally_closed_tm d ->
  tm_natrec a c d -->* tm_natrec b c d.
Proof.
  intros a b c d H Hc Hd; induction H; eauto using multi, step.
Qed.

Lemma multi_rec_base : forall a b c d, numeric_value a -> b -->* c ->
  locally_closed_tm d -> tm_natrec a b d -->* tm_natrec a c d.
Proof.
  intros a b c d Ha H Hd; induction H; eauto using multi, step.
Qed.

Lemma multi_rec_step : forall a b c d, numeric_value a -> value b ->
  c -->* d -> tm_natrec a b c -->* tm_natrec a b d.
Proof.
  intros a b c d Ha Hb H; induction H; eauto using multi, step.
Qed.

Definition candidate := tm -> tm -> Prop.
Definition candidate_env := nat -> candidate.
Definition free_candidate_env := atom -> candidate.

Definition push_candidate (R : candidate) (rho : candidate_env) : candidate_env :=
  fun i => match i with 0 => R | S j => rho j end.

Fixpoint value_relation (T : ty) (rho : candidate_env)
  (eta : free_candidate_env) (a b : tm) : Prop :=
  value a /\ value b /\
  match T with
  | Ty_BVar i => rho i a b
  | Ty_FVar X => eta X a b
  | Ty_Arrow A B =>
      forall u v, value_relation A rho eta u v ->
        exists a' b', tm_app a u -->* a' /\ tm_app b v -->* b' /\
          value_relation B rho eta a' b'
  | Ty_All B =>
      forall U V (R : candidate),
        locally_closed_ty U -> locally_closed_ty V ->
        exists a' b', tm_tapp a U -->* a' /\ tm_tapp b V -->* b' /\
          value_relation B (push_candidate R rho) eta a' b'
  | Ty_Bool => a = b /\ (a = tm_true \/ a = tm_false)
  | Ty_Nat => a = b /\ numeric_value a
  end.

Definition term_relation (T : ty) (rho : candidate_env)
  (eta : free_candidate_env) (a b : tm) : Prop :=
  exists a' b', a -->* a' /\ b -->* b' /\ value_relation T rho eta a' b'.

Lemma relation_values : forall T rho eta a b,
  value_relation T rho eta a b -> value a /\ value b.
Proof. intros T rho eta a b H; destruct T; simpl in H; tauto. Qed.

Lemma relation_refl_values : forall T rho eta a b,
  value_relation T rho eta a b -> term_relation T rho eta a b.
Proof.
  intros T rho eta a b H; exists a, b; repeat split; eauto using multi.
Qed.

Lemma relation_back : forall T rho eta a b a' b',
  a -->* a' -> b -->* b' -> term_relation T rho eta a' b' ->
  term_relation T rho eta a b.
Proof.
  intros T rho eta a b a' b' Ha Hb [u [v [Hu [Hv H]]]].
  exists u, v; repeat split; eauto using multi_trans.
Qed.

Fixpoint instantiate_type (alpha : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => alpha X
  | Ty_Arrow A B => Ty_Arrow (instantiate_type alpha A) (instantiate_type alpha B)
  | Ty_All A => Ty_All (instantiate_type alpha A)
  | Ty_Bool => Ty_Bool
  | Ty_Nat => Ty_Nat
  end.

Fixpoint instantiate_term (alpha : atom -> ty) (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_abs T t => tm_abs (instantiate_type alpha T) (instantiate_term alpha sigma t)
  | tm_app a b => tm_app (instantiate_term alpha sigma a) (instantiate_term alpha sigma b)
  | tm_tabs t => tm_tabs (instantiate_term alpha sigma t)
  | tm_tapp t T => tm_tapp (instantiate_term alpha sigma t) (instantiate_type alpha T)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if a b c => tm_if (instantiate_term alpha sigma a)
                            (instantiate_term alpha sigma b) (instantiate_term alpha sigma c)
  | tm_zero => tm_zero
  | tm_succ t => tm_succ (instantiate_term alpha sigma t)
  | tm_natrec n b s => tm_natrec (instantiate_term alpha sigma n)
                                  (instantiate_term alpha sigma b) (instantiate_term alpha sigma s)
  end.

Definition override {A : Type} (f : atom -> A) (x : atom) (v : A) : atom -> A :=
  fun y => if Nat.eqb x y then v else f y.

Lemma override_eq : forall A (f : atom -> A) x v, override f x v x = v.
Proof. intros; unfold override; now rewrite Nat.eqb_refl. Qed.

Lemma override_neq : forall A (f : atom -> A) x y v,
  x <> y -> override f x v y = f y.
Proof.
  intros; unfold override; apply Nat.eqb_neq in H; now rewrite H.
Qed.

Fixpoint free_types (T : ty) : list atom :=
  match T with
  | Ty_FVar X => [X]
  | Ty_Arrow A B => free_types A ++ free_types B
  | Ty_All A => free_types A
  | _ => []
  end.

Fixpoint free_term_types (t : tm) : list atom :=
  match t with
  | tm_abs T b => free_types T ++ free_term_types b
  | tm_app a b => free_term_types a ++ free_term_types b
  | tm_tabs b | tm_succ b => free_term_types b
  | tm_tapp b T => free_term_types b ++ free_types T
  | tm_if a b c | tm_natrec a b c =>
      free_term_types a ++ free_term_types b ++ free_term_types c
  | _ => []
  end.

Fixpoint free_terms (t : tm) : list atom :=
  match t with
  | tm_fvar x => [x]
  | tm_abs _ b | tm_tabs b | tm_tapp b _ | tm_succ b => free_terms b
  | tm_app a b => free_terms a ++ free_terms b
  | tm_if a b c | tm_natrec a b c =>
      free_terms a ++ free_terms b ++ free_terms c
  | _ => []
  end.

Lemma lc_ty_weaken : forall T k j,
  lc_ty_at k T -> lc_ty_at (k + j) T.
Proof.
  intros T k j H; induction H; constructor; eauto; lia.
Qed.

Lemma lc_tm_weaken : forall t K k J j,
  lc_tm_at K k t -> lc_tm_at (K + J) (k + j) t.
Proof.
  intros t K k J j H; induction H; try (constructor; eauto; fail).
  - constructor; lia.
  - constructor; eauto using lc_ty_weaken.
  - constructor; eauto using lc_ty_weaken.
Qed.

Lemma lc_type_inst : forall T k alpha,
  lc_ty_at k T ->
  (forall X, locally_closed_ty (alpha X)) ->
  lc_ty_at k (instantiate_type alpha T).
Proof.
  intros T k alpha H; induction H; intros Halpha; simpl;
    try (constructor; eauto; fail).
  - replace k with (0 + k) by lia.
    apply lc_ty_weaken, Halpha.
Qed.

Lemma lc_term_inst : forall t K k alpha sigma,
  lc_tm_at K k t ->
  (forall X, locally_closed_ty (alpha X)) ->
  (forall x, locally_closed_tm (sigma x)) ->
  lc_tm_at K k (instantiate_term alpha sigma t).
Proof.
  intros t K k alpha sigma H; induction H; intros Halpha Hsigma; simpl;
    try (constructor; eauto using lc_type_inst; fail).
  - replace K with (0 + K) by lia.
    replace k with (0 + k) by lia.
    apply lc_tm_weaken, Hsigma.
Qed.

Lemma lc_instantiated : forall t alpha sigma,
  locally_closed_tm t ->
  (forall X, locally_closed_ty (alpha X)) ->
  (forall x, locally_closed_tm (sigma x)) ->
  locally_closed_tm (instantiate_term alpha sigma t).
Proof. exact (fun t alpha sigma => lc_term_inst t 0 0 alpha sigma). Qed.

Lemma lc_ty_open_id : forall T k U,
  lc_ty_at k T -> open_ty_rec k U T = T.
Proof.
  intros T k U H; induction H; simpl; try (f_equal; eauto; fail).
  destruct (Nat.eqb k i) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
Qed.

Lemma lc_tm_open_id : forall t K k u,
  lc_tm_at K k t -> open_tm_rec k u t = t.
Proof.
  intros t K k u H; induction H; simpl; try (f_equal; eauto; fail).
  destruct (Nat.eqb k i) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
Qed.

Lemma lc_tm_ty_open_id : forall t K k U,
  lc_tm_at K k t -> lc_ty_at 0 U -> open_tm_ty_rec K U t = t.
Proof.
  intros t K k U H; induction H; intros HU; simpl;
    try (f_equal; eauto using lc_ty_open_id; fail).
Qed.

Lemma instantiated_type_open : forall T k alpha X U,
  ~ In X (free_types T) ->
  (forall Y, locally_closed_ty (alpha Y)) ->
  instantiate_type (override alpha X U)
    (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k U (instantiate_type alpha T).
Proof.
  induction T; intros k alpha X U Hfresh Halpha; simpl in *;
    try (f_equal; eauto; fail).
  - destruct (Nat.eqb k n); simpl; [now rewrite override_eq|reflexivity].
  - assert (X <> a) by (intro E; subst; apply Hfresh; now left).
    rewrite override_neq by assumption.
    symmetry. apply lc_ty_open_id.
    replace k with (0 + k) by lia. apply lc_ty_weaken, Halpha.
  - assert (H1 : ~ In X (free_types T1))
      by (intro E; apply Hfresh, in_or_app; now left).
    assert (H2 : ~ In X (free_types T2))
      by (intro E; apply Hfresh, in_or_app; now right).
    now rewrite (IHT1 k alpha X U H1 Halpha), (IHT2 k alpha X U H2 Halpha).
Qed.

Lemma instantiated_term_open : forall t K alpha sigma x u,
  ~ In x (free_terms t) ->
  (forall y, locally_closed_tm (sigma y)) ->
  instantiate_term alpha (override sigma x u)
    (open_tm_rec K (tm_fvar x) t) =
  open_tm_rec K u (instantiate_term alpha sigma t).
Proof.
  induction t; intros K alpha sigma x u Hfresh Hsigma; simpl in *;
    try (f_equal; eauto; fail).
  - destruct (Nat.eqb K n); simpl; [now rewrite override_eq|reflexivity].
  - assert (x <> a) by (intro E; subst; apply Hfresh; now left).
    rewrite override_neq by assumption.
    symmetry. apply (lc_tm_open_id (sigma a) 0 K u).
    pose proof (lc_tm_weaken _ 0 0 0 K (Hsigma a)) as Hlc.
    exact Hlc.
  - assert (H1 : ~ In x (free_terms t1))
      by (intro E; apply Hfresh, in_or_app; now left).
    assert (H2 : ~ In x (free_terms t2))
      by (intro E; apply Hfresh, in_or_app; now right).
    now rewrite (IHt1 K alpha sigma x u H1 Hsigma),
      (IHt2 K alpha sigma x u H2 Hsigma).
  - repeat rewrite in_app_iff in Hfresh.
    assert (H1 : ~ In x (free_terms t1)) by tauto.
    assert (H2 : ~ In x (free_terms t2)) by tauto.
    assert (H3 : ~ In x (free_terms t3)) by tauto.
    now rewrite (IHt1 K alpha sigma x u H1 Hsigma),
      (IHt2 K alpha sigma x u H2 Hsigma),
      (IHt3 K alpha sigma x u H3 Hsigma).
  - repeat rewrite in_app_iff in Hfresh.
    assert (H1 : ~ In x (free_terms t1)) by tauto.
    assert (H2 : ~ In x (free_terms t2)) by tauto.
    assert (H3 : ~ In x (free_terms t3)) by tauto.
    now rewrite (IHt1 K alpha sigma x u H1 Hsigma),
      (IHt2 K alpha sigma x u H2 Hsigma),
      (IHt3 K alpha sigma x u H3 Hsigma).
Qed.

Lemma instantiated_term_type_open : forall t K alpha sigma X U,
  ~ In X (free_term_types t) ->
  (forall Y, locally_closed_ty (alpha Y)) ->
  (forall x, locally_closed_tm (sigma x)) ->
  locally_closed_ty U ->
  instantiate_term (override alpha X U) sigma
    (open_tm_ty_rec K (Ty_FVar X) t) =
  open_tm_ty_rec K U (instantiate_term alpha sigma t).
Proof.
  induction t; intros K alpha sigma X U Hfresh Halpha Hsigma HU; simpl in *;
    try (f_equal; eauto; fail).
  - symmetry. apply (lc_tm_ty_open_id (sigma a) K 0 U); eauto.
    pose proof (lc_tm_weaken _ 0 0 K 0 (Hsigma a)) as Hlc.
    exact Hlc.
  - assert (Hty : ~ In X (free_types t))
      by (intro E; apply Hfresh, in_or_app; now left).
    assert (Htm : ~ In X (free_term_types t0))
      by (intro E; apply Hfresh, in_or_app; now right).
    now rewrite (instantiated_type_open t K alpha X U Hty Halpha),
      (IHt K alpha sigma X U Htm Halpha Hsigma HU).
  - assert (H1 : ~ In X (free_term_types t1))
      by (intro E; apply Hfresh, in_or_app; now left).
    assert (H2 : ~ In X (free_term_types t2))
      by (intro E; apply Hfresh, in_or_app; now right).
    now rewrite (IHt1 K alpha sigma X U H1 Halpha Hsigma HU),
      (IHt2 K alpha sigma X U H2 Halpha Hsigma HU).
  - assert (Htm : ~ In X (free_term_types t))
      by (intro E; apply Hfresh, in_or_app; now left).
    assert (Hty : ~ In X (free_types t0))
      by (intro E; apply Hfresh, in_or_app; now right).
    now rewrite (IHt K alpha sigma X U Htm Halpha Hsigma HU),
      (instantiated_type_open t0 K alpha X U Hty Halpha).
  - repeat rewrite in_app_iff in Hfresh.
    assert (H1 : ~ In X (free_term_types t1)) by tauto.
    assert (H2 : ~ In X (free_term_types t2)) by tauto.
    assert (H3 : ~ In X (free_term_types t3)) by tauto.
    now rewrite (IHt1 K alpha sigma X U H1 Halpha Hsigma HU),
      (IHt2 K alpha sigma X U H2 Halpha Hsigma HU),
      (IHt3 K alpha sigma X U H3 Halpha Hsigma HU).
  - repeat rewrite in_app_iff in Hfresh.
    assert (H1 : ~ In X (free_term_types t1)) by tauto.
    assert (H2 : ~ In X (free_term_types t2)) by tauto.
    assert (H3 : ~ In X (free_term_types t3)) by tauto.
    now rewrite (IHt1 K alpha sigma X U H1 Halpha Hsigma HU),
      (IHt2 K alpha sigma X U H2 Halpha Hsigma HU),
      (IHt3 K alpha sigma X U H3 Halpha Hsigma HU).
Qed.

Definition replace_candidate (k : nat) (R : candidate)
  (rho : candidate_env) : candidate_env :=
  fun i => if Nat.eqb k i then R else rho i.

Lemma value_relation_env : forall T rho rho' eta a b,
  (forall i u v, rho i u v <-> rho' i u v) ->
  value_relation T rho eta a b <-> value_relation T rho' eta a b.
Proof.
  induction T; intros rho rho' eta va vb Heq; simpl; try tauto.
  - now rewrite Heq.
  - split; intros [Ha [Hb Hf]]; repeat split; try assumption.
    + intros u v Huv.
      apply (proj2 (IHT1 rho rho' eta u v Heq)) in Huv.
      destruct (Hf u v Huv) as [aa [bb [Haa [Hbb Hr]]]].
      exists aa, bb; repeat split; auto.
      apply (proj1 (IHT2 rho rho' eta aa bb Heq)); exact Hr.
    + intros u v Huv.
      apply (proj1 (IHT1 rho rho' eta u v Heq)) in Huv.
      destruct (Hf u v Huv) as [aa [bb [Haa [Hbb Hr]]]].
      exists aa, bb; repeat split; auto.
      apply (proj2 (IHT2 rho rho' eta aa bb Heq)); exact Hr.
  - assert (Hpush : forall R i u v,
        push_candidate R rho i u v <-> push_candidate R rho' i u v).
    { intros R i u v; destruct i; simpl; [tauto|apply Heq]. }
    split; intros [Ha [Hb Hf]]; repeat split; try assumption.
    + intros U V R HU HV.
      destruct (Hf U V R HU HV) as [aa [bb [Haa [Hbb Hr]]]].
      exists aa, bb; repeat split; auto.
      apply (proj1 (IHT (push_candidate R rho)
        (push_candidate R rho') eta aa bb (Hpush R))); exact Hr.
    + intros U V R HU HV.
      destruct (Hf U V R HU HV) as [aa [bb [Haa [Hbb Hr]]]].
      exists aa, bb; repeat split; auto.
      apply (proj2 (IHT (push_candidate R rho)
        (push_candidate R rho') eta aa bb (Hpush R))); exact Hr.
Qed.

Lemma value_relation_free : forall T rho eta X R a b,
  ~ In X (free_types T) ->
  value_relation T rho (override eta X R) a b <->
  value_relation T rho eta a b.
Proof.
  induction T; intros rho eta X R va vb Hfresh; simpl in *;
    try (tauto; fail).
  - assert (X <> a) by (intro E; subst; apply Hfresh; now left).
    now rewrite override_neq by assumption.
  - assert (H1 : ~ In X (free_types T1))
      by (intro E; apply Hfresh, in_or_app; now left).
    assert (H2 : ~ In X (free_types T2))
      by (intro E; apply Hfresh, in_or_app; now right).
    split; intros [Ha [Hb Hf]]; repeat split; try assumption.
    + intros u v Huv.
      apply (proj2 (IHT1 rho eta X R u v H1)) in Huv.
      destruct (Hf _ _ Huv) as [aa [bb [Haa [Hbb Hr]]]].
      exists aa, bb; repeat split; auto.
      apply (proj1 (IHT2 rho eta X R aa bb H2)); exact Hr.
    + intros u v Huv.
      apply (proj1 (IHT1 rho eta X R u v H1)) in Huv.
      destruct (Hf _ _ Huv) as [aa [bb [Haa [Hbb Hr]]]].
      exists aa, bb; repeat split; auto.
      apply (proj2 (IHT2 rho eta X R aa bb H2)); exact Hr.
  - split; intros [Ha [Hb Hf]]; repeat split; try assumption.
    + intros U V R' HU HV.
      destruct (Hf U V R' HU HV) as [aa [bb [Haa [Hbb Hr]]]].
      exists aa, bb; repeat split; auto.
      apply (proj1 (IHT (push_candidate R' rho) eta X R aa bb Hfresh)); exact Hr.
    + intros U V R' HU HV.
      destruct (Hf U V R' HU HV) as [aa [bb [Haa [Hbb Hr]]]].
      exists aa, bb; repeat split; auto.
      apply (proj2 (IHT (push_candidate R' rho) eta X R aa bb Hfresh)); exact Hr.
Qed.

Lemma value_relation_open_free : forall T k rho eta X R a b,
  ~ In X (free_types T) ->
  value_relation (open_ty_rec k (Ty_FVar X) T) rho
    (override eta X R) a b <->
  value_relation T (replace_candidate k R rho) eta a b.
Proof.
  induction T; intros k rho eta X R va vb Hfresh; simpl in *;
    try (tauto; fail).
  - destruct (Nat.eqb k n) eqn:E; simpl; unfold replace_candidate;
      rewrite E; [now rewrite override_eq|tauto].
  - assert (X <> a) by (intro E; subst; apply Hfresh; now left).
    now rewrite override_neq by assumption.
  - assert (H1 : ~ In X (free_types T1))
      by (intro E; apply Hfresh, in_or_app; now left).
    assert (H2 : ~ In X (free_types T2))
      by (intro E; apply Hfresh, in_or_app; now right).
    split; intros [Ha [Hb Hf]]; repeat split; try assumption.
    + intros u v Huv.
      apply (proj2 (IHT1 k rho eta X R u v H1)) in Huv.
      destruct (Hf _ _ Huv) as [aa [bb [Haa [Hbb Hr]]]].
      exists aa, bb; repeat split; auto.
      apply (proj1 (IHT2 k rho eta X R aa bb H2)); exact Hr.
    + intros u v Huv.
      apply (proj1 (IHT1 k rho eta X R u v H1)) in Huv.
      destruct (Hf _ _ Huv) as [aa [bb [Haa [Hbb Hr]]]].
      exists aa, bb; repeat split; auto.
      apply (proj2 (IHT2 k rho eta X R aa bb H2)); exact Hr.
  - split; intros [Ha [Hb Hf]]; repeat split; try assumption.
    + intros U V R' HU HV.
      destruct (Hf U V R' HU HV) as [aa [bb [Haa [Hbb Hr]]]].
      exists aa, bb; repeat split; auto.
      specialize (IHT (S k) (push_candidate R' rho) eta X R aa bb Hfresh).
      assert (Hswap : forall i u v,
        push_candidate R' (replace_candidate k R rho) i u v <->
        replace_candidate (S k) R (push_candidate R' rho) i u v).
      { intros [|i] u v; unfold push_candidate, replace_candidate;
        simpl; [tauto|destruct (Nat.eqb k i); tauto]. }
      apply (proj2 (value_relation_env T _ _ eta aa bb Hswap)).
      apply (proj1 IHT); exact Hr.
    + intros U V R' HU HV.
      destruct (Hf U V R' HU HV) as [aa [bb [Haa [Hbb Hr]]]].
      exists aa, bb; repeat split; auto.
      specialize (IHT (S k) (push_candidate R' rho) eta X R aa bb Hfresh).
      assert (Hswap : forall i u v,
        push_candidate R' (replace_candidate k R rho) i u v <->
        replace_candidate (S k) R (push_candidate R' rho) i u v).
      { intros [|i] u v; unfold push_candidate, replace_candidate;
        simpl; [tauto|destruct (Nat.eqb k i); tauto]. }
      apply (proj2 IHT).
      apply (proj1 (value_relation_env T _ _ eta aa bb Hswap)); exact Hr.
Qed.

Lemma value_relation_bound : forall T k rho rho' eta a b,
  lc_ty_at k T ->
  (forall i u v, i < k -> rho i u v <-> rho' i u v) ->
  value_relation T rho eta a b <-> value_relation T rho' eta a b.
Proof.
  induction T; intros k rho rho' eta va vb Hlc Hagree;
    inversion Hlc; subst; simpl; try tauto.
  - now rewrite (Hagree n va vb H1).
  - split; intros [Ha [Hb Hf]]; repeat split; try assumption.
    + intros u v Huv.
      apply (proj2 (IHT1 k rho rho' eta u v H2 Hagree)) in Huv.
      destruct (Hf u v Huv) as [aa [bb [Haa [Hbb Hr]]]].
      exists aa, bb; repeat split; auto.
      apply (proj1 (IHT2 k rho rho' eta aa bb H3 Hagree)); exact Hr.
    + intros u v Huv.
      apply (proj1 (IHT1 k rho rho' eta u v H2 Hagree)) in Huv.
      destruct (Hf u v Huv) as [aa [bb [Haa [Hbb Hr]]]].
      exists aa, bb; repeat split; auto.
      apply (proj2 (IHT2 k rho rho' eta aa bb H3 Hagree)); exact Hr.
  - assert (Hpush : forall R i u v, i < S k ->
        push_candidate R rho i u v <-> push_candidate R rho' i u v).
    { intros R [|i] u v Hi; simpl; [tauto|apply Hagree; lia]. }
    split; intros [Ha [Hb Hf]]; repeat split; try assumption.
    + intros U V R HU HV.
      destruct (Hf U V R HU HV) as [aa [bb [Haa [Hbb Hr]]]].
      exists aa, bb; repeat split; auto.
      apply (proj1 (IHT (S k) (push_candidate R rho)
        (push_candidate R rho') eta aa bb H1 (Hpush R))); exact Hr.
    + intros U V R HU HV.
      destruct (Hf U V R HU HV) as [aa [bb [Haa [Hbb Hr]]]].
      exists aa, bb; repeat split; auto.
      apply (proj2 (IHT (S k) (push_candidate R rho)
        (push_candidate R rho') eta aa bb H1 (Hpush R))); exact Hr.
Qed.

Lemma value_relation_open_bound : forall T k U rho eta R a b,
  lc_ty_at 0 U ->
  (forall u v, R u v <-> value_relation U rho eta u v) ->
  value_relation (open_ty_rec k U T) rho eta a b <->
  value_relation T (replace_candidate k R rho) eta a b.
Proof.
  induction T; intros k U rho eta R va vb HU HR; simpl; try tauto.
  - destruct (Nat.eqb k n) eqn:E; simpl; unfold replace_candidate;
      rewrite E; [|tauto].
    split; intro H.
    + destruct (relation_values _ _ _ _ _ H) as [Ha Hb].
      repeat split; try assumption. apply (proj2 (HR va vb)); exact H.
    + destruct H as [_ [_ Hrel]]. apply (proj1 (HR va vb)); exact Hrel.
  - split; intros [Ha [Hb Hf]]; repeat split; try assumption.
    + intros u v Huv.
      apply (proj2 (IHT1 k U rho eta R u v HU HR)) in Huv.
      destruct (Hf u v Huv) as [aa [bb [Haa [Hbb Hr]]]].
      exists aa, bb; repeat split; auto.
      apply (proj1 (IHT2 k U rho eta R aa bb HU HR)); exact Hr.
    + intros u v Huv.
      apply (proj1 (IHT1 k U rho eta R u v HU HR)) in Huv.
      destruct (Hf u v Huv) as [aa [bb [Haa [Hbb Hr]]]].
      exists aa, bb; repeat split; auto.
      apply (proj2 (IHT2 k U rho eta R aa bb HU HR)); exact Hr.
  - assert (Hswap : forall Q i u v,
        push_candidate Q (replace_candidate k R rho) i u v <->
        replace_candidate (S k) R (push_candidate Q rho) i u v).
    { intros Q [|i] u v; unfold push_candidate, replace_candidate;
      simpl; [tauto|destruct (Nat.eqb k i); tauto]. }
    assert (HRpush : forall Q u v,
      R u v <-> value_relation U (push_candidate Q rho) eta u v).
    { intros Q u v. transitivity (value_relation U rho eta u v).
      - exact (HR u v).
      - apply value_relation_bound with (k:=0); auto.
        intros i p q Hi; lia. }
    split; intros [Ha [Hb Hf]]; repeat split; try assumption.
    + intros A B Q HA HB.
      destruct (Hf A B Q HA HB) as [aa [bb [Haa [Hbb Hr]]]].
      exists aa, bb; repeat split; auto.
      apply (proj2 (value_relation_env T _ _ eta aa bb (Hswap Q))).
      apply (proj1 (IHT (S k) U (push_candidate Q rho) eta R aa bb
        HU (HRpush Q))).
      exact Hr.
    + intros A B Q HA HB.
      destruct (Hf A B Q HA HB) as [aa [bb [Haa [Hbb Hr]]]].
      exists aa, bb; repeat split; auto.
      apply (proj2 (IHT (S k) U (push_candidate Q rho) eta R aa bb
        HU (HRpush Q))).
      apply (proj1 (value_relation_env T _ _ eta aa bb (Hswap Q))).
      exact Hr.
Qed.

Lemma lc_ty_open : forall T k U,
  lc_ty_at (S k) T -> lc_ty_at 0 U ->
  lc_ty_at k (open_ty_rec k U T).
Proof.
  induction T; intros k U Ht HU; inversion Ht; subst; simpl;
    try (constructor; eauto; fail).
  - destruct (Nat.eqb k n) eqn:E.
    + replace k with (0 + k) by lia. apply lc_ty_weaken, HU.
    + constructor; apply Nat.eqb_neq in E; lia.
Qed.

Lemma typing_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_ty T.
Proof.
  intros Delta Gamma t T H; induction H; unfold locally_closed_ty in *;
    eauto using wf_lc.
  - exact (wf_lc _ _ H0).
  - constructor. exact (wf_lc _ _ H).
    exact (H1 (fresh L) (fresh_not_in L)).
  - inversion IHhas_type1; subst; assumption.
  - constructor. apply (lc_ty_open_inv T 0 (fresh L)).
    apply H0, fresh_not_in.
  - inversion IHhas_type; subst.
    eapply lc_ty_open; eauto. exact (wf_lc _ _ H0).
Qed.

Lemma value_relation_open_type : forall T U rho eta a b,
  lc_ty_at 1 T -> lc_ty_at 0 U ->
  value_relation (open_ty T U) rho eta a b <->
  value_relation T
    (push_candidate (value_relation U rho eta) rho) eta a b.
Proof.
  intros T U rho eta a b HT HU.
  transitivity (value_relation T
    (replace_candidate 0 (value_relation U rho eta) rho) eta a b).
  - apply value_relation_open_bound; auto. intros; tauto.
  - apply value_relation_bound with (k:=1); auto.
    intros [|i] u v Hi; [simpl; unfold replace_candidate, push_candidate;
      simpl; tauto|lia].
Qed.

Lemma value_relation_open_name : forall T X rho eta R a b,
  lc_ty_at 1 T -> ~ In X (free_types T) ->
  value_relation (open_ty T (Ty_FVar X)) rho
    (override eta X R) a b <->
  value_relation T (push_candidate R rho) eta a b.
Proof.
  intros T X rho eta R a b HT Hfresh.
  transitivity (value_relation T (replace_candidate 0 R rho) eta a b).
  - apply value_relation_open_free; auto.
  - apply value_relation_bound with (k:=1); auto.
    intros [|i] u v Hi; [simpl; unfold replace_candidate, push_candidate;
      simpl; tauto|lia].
Qed.

Lemma numeric_value_value : forall n, numeric_value n -> value n.
Proof. intros; now constructor. Qed.

Lemma value_relation_nat : forall rho eta n,
  numeric_value n -> value_relation Ty_Nat rho eta n n.
Proof.
  intros rho eta n H; simpl; repeat split; eauto using value, numeric_value.
Qed.

Lemma rec_values_related : forall T rho eta n b1 b2 s1 s2,
  numeric_value n ->
  value_relation T rho eta b1 b2 ->
  value_relation (Ty_Arrow Ty_Nat (Ty_Arrow T T)) rho eta s1 s2 ->
  term_relation T rho eta
    (tm_natrec n b1 s1) (tm_natrec n b2 s2).
Proof.
  intros T rho eta n b1 b2 s1 s2 Hn.
  induction Hn as [|n Hn IH]; intros Hb Hs.
  - destruct (relation_values _ _ _ _ _ Hb) as [Hb1 Hb2].
    destruct (relation_values _ _ _ _ _ Hs) as [Hs1 Hs2].
    eapply relation_back; [eapply multi_step; [constructor; eauto|constructor]
      |eapply multi_step; [constructor; eauto|constructor]
      |apply relation_refl_values; exact Hb].
  - destruct (relation_values _ _ _ _ _ Hb) as [Hb1 Hb2].
    destruct (relation_values _ _ _ _ _ Hs) as [Hs1 Hs2].
    pose proof (IH Hb Hs) as [r1 [r2 [Hr1 [Hr2 Hr]]]].
    destruct Hs as [_ [_ Hs]].
    destruct (Hs n n (value_relation_nat rho eta n Hn))
      as [f1 [f2 [Hf1 [Hf2 Hf]]]].
    destruct Hf as [Hfv1 [Hfv2 Happly]].
    destruct (Happly r1 r2 Hr) as [w1 [w2 [Hw1 [Hw2 Hw]]]].
    exists w1, w2; repeat split; try exact Hw.
    + eapply multi_trans.
      * eapply multi_step; [apply ST_RecSucc; eauto|apply multi_refl].
      * eapply multi_trans.
        -- apply multi_app1; [exact Hf1|].
           unfold locally_closed_tm; constructor.
           ++ apply value_lc, numeric_value_value; exact Hn.
           ++ apply value_lc; exact Hb1.
           ++ apply value_lc; exact Hs1.
        -- eapply multi_trans.
           ++ apply multi_app2; eauto.
           ++ exact Hw1.
    + eapply multi_trans.
      * eapply multi_step; [apply ST_RecSucc; eauto|apply multi_refl].
      * eapply multi_trans.
        -- apply multi_app1; [exact Hf2|].
           unfold locally_closed_tm; constructor.
           ++ apply value_lc, numeric_value_value; exact Hn.
           ++ apply value_lc; exact Hb2.
           ++ apply value_lc; exact Hs2.
        -- eapply multi_trans.
           ++ apply multi_app2; eauto.
           ++ exact Hw2.
Qed.

Definition free_context_types (Gamma : context) : list atom :=
  concat (map (fun p => free_types (snd p)) Gamma).

Lemma lookup_free_types : forall Gamma x T X,
  lookup_context x Gamma = Some T ->
  ~ In X (free_context_types Gamma) -> ~ In X (free_types T).
Proof.
  induction Gamma as [|[y A] Gamma IH]; intros x T X Hlookup Hfresh;
    simpl in *; [discriminate|].
  destruct (Nat.eqb x y) eqn:E.
  - inversion Hlookup; subst. intro Hin.
    apply Hfresh, in_or_app; now left.
  - apply (IH x T X); [exact Hlookup|].
    intro Hin; apply Hfresh, in_or_app; now right.
Qed.

Lemma lookup_not_in : forall Gamma x,
  ~ In x (map fst Gamma) -> lookup_context x Gamma = None.
Proof.
  induction Gamma as [|[y T] Gamma IH]; intros x Hfresh;
    simpl in *; [reflexivity|].
  assert (x <> y) by (intro E; subst; apply Hfresh; now left).
  destruct (Nat.eqb x y) eqn:E.
  { apply Nat.eqb_eq in E; contradiction. }
  apply IH. intro Hin; apply Hfresh; now right.
Qed.

Lemma instantiated_typed_lc : forall Delta Gamma t T alpha sigma,
  has_type Delta Gamma t T ->
  (forall X, locally_closed_ty (alpha X)) ->
  (forall x, value (sigma x)) ->
  locally_closed_tm (instantiate_term alpha sigma t).
Proof.
  intros Delta Gamma t T alpha sigma Ht Halpha Hsigma.
  apply lc_instantiated.
  - eapply typing_lc; eauto.
  - exact Halpha.
  - intros x; apply value_lc, Hsigma.
Qed.

Theorem fundamental_relation : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall rho eta alpha beta sigma tau,
    (forall X, locally_closed_ty (alpha X) /\ locally_closed_ty (beta X)) ->
    (forall x, value (sigma x) /\ value (tau x)) ->
    (forall x A, lookup_context x Gamma = Some A ->
      value_relation A rho eta (sigma x) (tau x)) ->
    term_relation T rho eta
      (instantiate_term alpha sigma t) (instantiate_term beta tau t).
Proof.
  intros Delta Gamma t T Htyping.
  induction Htyping; intros rho eta alpha beta sigma tau Halpha Hsigma Hgamma;
    simpl.
  - apply relation_refl_values. apply Hgamma; assumption.
  - apply relation_refl_values. simpl.
    assert (Habs : has_type Delta Gamma (tm_abs T1 t2) (Ty_Arrow T1 T2)).
    { eapply T_Abs; eauto. }
    assert (Hlc1 : locally_closed_tm
      (instantiate_term alpha sigma (tm_abs T1 t2))).
    { eapply instantiated_typed_lc; [exact Habs|exact (fun X => proj1 (Halpha X))|
        exact (fun x => proj1 (Hsigma x))]. }
    assert (Hlc2 : locally_closed_tm
      (instantiate_term beta tau (tm_abs T1 t2))).
    { eapply instantiated_typed_lc; [exact Habs|exact (fun X => proj2 (Halpha X))|
        exact (fun x => proj2 (Hsigma x))]. }
    repeat split; try (constructor; assumption).
    intros u v Huv.
    set (x := fresh (L ++ map fst Gamma ++ free_terms t2)).
    assert (HxL : ~ In x L).
    { unfold x; intro E; apply (fresh_not_in (L ++ map fst Gamma ++ free_terms t2)).
      apply in_or_app; now left. }
    assert (HxGamma : ~ In x (map fst Gamma)).
    { unfold x; intro E; apply (fresh_not_in (L ++ map fst Gamma ++ free_terms t2)).
      apply in_or_app; right; apply in_or_app; now left. }
    assert (HxTerm : ~ In x (free_terms t2)).
    { unfold x; intro E; apply (fresh_not_in (L ++ map fst Gamma ++ free_terms t2)).
      apply in_or_app; right; apply in_or_app; now right. }
    assert (Hsigma' : forall y,
      value (override sigma x u y) /\ value (override tau x v y)).
    { intro y; destruct (Nat.eqb x y) eqn:E; unfold override;
        rewrite E; [apply relation_values in Huv; exact Huv|apply Hsigma]. }
    assert (Hgamma' : forall y A,
      lookup_context y ((x, T1) :: Gamma) = Some A ->
      value_relation A rho eta (override sigma x u y) (override tau x v y)).
    { intros y A Hy. simpl in Hy.
      destruct (Nat.eqb y x) eqn:E.
      - apply Nat.eqb_eq in E; subst y.
        repeat rewrite override_eq. inversion Hy; subst; exact Huv.
      - apply Nat.eqb_neq in E.
        rewrite override_neq by lia. rewrite override_neq by lia.
        apply Hgamma; exact Hy. }
    pose proof (H1 x HxL rho eta alpha beta
      (override sigma x u) (override tau x v) Halpha Hsigma' Hgamma') as Hbody.
    unfold open_tm in Hbody.
    rewrite (instantiated_term_open t2 0 alpha sigma x u HxTerm
      (fun y => value_lc _ (proj1 (Hsigma y)))) in Hbody.
    rewrite (instantiated_term_open t2 0 beta tau x v HxTerm
      (fun y => value_lc _ (proj2 (Hsigma y)))) in Hbody.
    destruct (relation_values _ _ _ _ _ Huv) as [Hu Hv].
    eapply relation_back; [eapply multi_step; [apply ST_AppAbs; eauto using value_lc|
      apply multi_refl]|eapply multi_step; [apply ST_AppAbs; eauto using value_lc|
      apply multi_refl]|exact Hbody].
  - destruct (IHHtyping1 rho eta alpha beta sigma tau Halpha Hsigma Hgamma)
      as [a [b [Ha [Hb Hfun]]]].
    destruct (IHHtyping2 rho eta alpha beta sigma tau Halpha Hsigma Hgamma)
      as [u [v [Hu [Hv Harg]]]].
    destruct Hfun as [Hav [Hbv Happly]].
    destruct (Happly u v Harg) as [c [d [Hc [Hd Hcd]]]].
    exists c, d; repeat split; try exact Hcd.
    + eapply multi_trans.
      * apply multi_app1; [exact Ha|].
        eapply instantiated_typed_lc; [exact Htyping2|exact (fun X => proj1 (Halpha X))|
          exact (fun x => proj1 (Hsigma x))].
      * eapply multi_trans; [apply multi_app2; eauto|exact Hc].
    + eapply multi_trans.
      * apply multi_app1; [exact Hb|].
        eapply instantiated_typed_lc; [exact Htyping2|exact (fun X => proj2 (Halpha X))|
          exact (fun x => proj2 (Hsigma x))].
      * eapply multi_trans; [apply multi_app2; eauto|exact Hd].
  - apply relation_refl_values. simpl.
    assert (Htabs : has_type Delta Gamma (tm_tabs t) (Ty_All T)).
    { eapply T_TAbs; eauto. }
    assert (Hlc1 : locally_closed_tm (instantiate_term alpha sigma (tm_tabs t))).
    { eapply instantiated_typed_lc; [exact Htabs|exact (fun X => proj1 (Halpha X))|
        exact (fun x => proj1 (Hsigma x))]. }
    assert (Hlc2 : locally_closed_tm (instantiate_term beta tau (tm_tabs t))).
    { eapply instantiated_typed_lc; [exact Htabs|exact (fun X => proj2 (Halpha X))|
        exact (fun x => proj2 (Hsigma x))]. }
    repeat split; try (constructor; assumption).
    intros U V R HU HV.
    set (X := fresh (L ++ free_term_types t ++ free_types T ++
      free_context_types Gamma)).
    assert (HXL : ~ In X L).
    { unfold X; intro E; apply (fresh_not_in
        (L ++ free_term_types t ++ free_types T ++ free_context_types Gamma)).
      apply in_or_app; now left. }
    assert (HXtm : ~ In X (free_term_types t)).
    { unfold X; intro E; apply (fresh_not_in
        (L ++ free_term_types t ++ free_types T ++ free_context_types Gamma)).
      apply in_or_app; right; apply in_or_app; now left. }
    assert (HXty : ~ In X (free_types T)).
    { unfold X; intro E; apply (fresh_not_in
        (L ++ free_term_types t ++ free_types T ++ free_context_types Gamma)).
      apply in_or_app; right; apply in_or_app; right; apply in_or_app; now left. }
    assert (HXctx : ~ In X (free_context_types Gamma)).
    { unfold X; intro E; apply (fresh_not_in
        (L ++ free_term_types t ++ free_types T ++ free_context_types Gamma)).
      apply in_or_app; right; apply in_or_app; right; apply in_or_app; now right. }
    assert (HT : lc_ty_at 1 T).
    { apply (lc_ty_open_inv T 0 X).
      exact (typing_type_lc _ _ _ _ (H X HXL)). }
    assert (Halpha' : forall Y,
      locally_closed_ty (override alpha X U Y) /\
      locally_closed_ty (override beta X V Y)).
    { intro Y; unfold override; destruct (Nat.eqb X Y); auto. }
    assert (Hgamma' : forall y A, lookup_context y Gamma = Some A ->
      value_relation A rho (override eta X R) (sigma y) (tau y)).
    { intros y A Hy. apply (proj2 (value_relation_free A rho eta X R
        (sigma y) (tau y) (lookup_free_types Gamma y A X Hy HXctx))).
      apply Hgamma; exact Hy. }
    pose proof (H0 X HXL rho (override eta X R)
      (override alpha X U) (override beta X V) sigma tau
      Halpha' Hsigma Hgamma') as Hbody.
    unfold open_tm_ty in Hbody.
    rewrite (instantiated_term_type_open t 0 alpha sigma X U HXtm
      (fun Y => proj1 (Halpha Y))
      (fun y => value_lc _ (proj1 (Hsigma y))) HU) in Hbody.
    rewrite (instantiated_term_type_open t 0 beta tau X V HXtm
      (fun Y => proj2 (Halpha Y))
      (fun y => value_lc _ (proj2 (Hsigma y))) HV) in Hbody.
    destruct Hbody as [a [b [Ha [Hb Hab]]]].
    exists a, b; repeat split.
    + eapply multi_trans; [eapply multi_step;
        [apply ST_TAppTabs; eauto|apply multi_refl]|exact Ha].
    + eapply multi_trans; [eapply multi_step;
        [apply ST_TAppTabs; eauto|apply multi_refl]|exact Hb].
    + apply (proj1 (value_relation_open_name T X rho eta R a b HT HXty));
        exact Hab.
  - destruct (IHHtyping rho eta alpha beta sigma tau Halpha Hsigma Hgamma)
      as [a [b [Ha [Hb Hall]]]].
    destruct Hall as [Hav [Hbv Hall]].
    assert (HU1 : locally_closed_ty (instantiate_type alpha U)).
    { apply lc_type_inst; [exact (wf_lc _ _ H)|exact (fun X => proj1 (Halpha X))]. }
    assert (HU2 : locally_closed_ty (instantiate_type beta U)).
    { apply lc_type_inst; [exact (wf_lc _ _ H)|exact (fun X => proj2 (Halpha X))]. }
    destruct (Hall (instantiate_type alpha U) (instantiate_type beta U)
      (value_relation U rho eta) HU1 HU2)
      as [c [d [Hc [Hd Hcd]]]].
    assert (HT : lc_ty_at 1 T).
    { pose proof (typing_type_lc _ _ _ _ Htyping) as Hty.
      inversion Hty; assumption. }
    exists c, d; repeat split.
    + eapply multi_trans; [apply multi_tapp; eauto|exact Hc].
    + eapply multi_trans; [apply multi_tapp; eauto|exact Hd].
    + apply (proj2 (value_relation_open_type T U rho eta c d HT
        (wf_lc _ _ H))); exact Hcd.
  - apply relation_refl_values. simpl; repeat split; auto using value.
  - apply relation_refl_values. simpl; repeat split; auto using value.
  - destruct (IHHtyping1 rho eta alpha beta sigma tau Halpha Hsigma Hgamma)
      as [a [b [Ha [Hb Hbool]]]].
    destruct Hbool as [Hav [Hbv [Heq [Htrue|Hfalse]]]]; subst b.
    + subst a.
      eapply relation_back.
      * apply multi_if_true; [exact Ha| |].
        -- eapply instantiated_typed_lc; [exact Htyping2|
             exact (fun X => proj1 (Halpha X))|exact (fun x => proj1 (Hsigma x))].
        -- eapply instantiated_typed_lc; [exact Htyping3|
             exact (fun X => proj1 (Halpha X))|exact (fun x => proj1 (Hsigma x))].
      * apply multi_if_true; [exact Hb| |].
        -- eapply instantiated_typed_lc; [exact Htyping2|
             exact (fun X => proj2 (Halpha X))|exact (fun x => proj2 (Hsigma x))].
        -- eapply instantiated_typed_lc; [exact Htyping3|
             exact (fun X => proj2 (Halpha X))|exact (fun x => proj2 (Hsigma x))].
      * apply IHHtyping2; assumption.
    + subst a.
      eapply relation_back.
      * apply multi_if_false; [exact Ha| |].
        -- eapply instantiated_typed_lc; [exact Htyping2|
             exact (fun X => proj1 (Halpha X))|exact (fun x => proj1 (Hsigma x))].
        -- eapply instantiated_typed_lc; [exact Htyping3|
             exact (fun X => proj1 (Halpha X))|exact (fun x => proj1 (Hsigma x))].
      * apply multi_if_false; [exact Hb| |].
        -- eapply instantiated_typed_lc; [exact Htyping2|
             exact (fun X => proj2 (Halpha X))|exact (fun x => proj2 (Hsigma x))].
        -- eapply instantiated_typed_lc; [exact Htyping3|
             exact (fun X => proj2 (Halpha X))|exact (fun x => proj2 (Hsigma x))].
      * apply IHHtyping3; assumption.
  - apply relation_refl_values. apply value_relation_nat. constructor.
  - destruct (IHHtyping rho eta alpha beta sigma tau Halpha Hsigma Hgamma)
      as [a [b [Ha [Hb Hnat]]]].
    destruct Hnat as [_ [_ [Heq Hnum]]]; subst b.
    exists (tm_succ a), (tm_succ a); repeat split;
      eauto using multi_succ, value_relation_nat, numeric_value.
  - destruct (IHHtyping1 rho eta alpha beta sigma tau Halpha Hsigma Hgamma)
      as [a [a' [Ha [Ha' Hnat]]]].
    destruct (IHHtyping2 rho eta alpha beta sigma tau Halpha Hsigma Hgamma)
      as [base1 [base2 [Hb [Hb' Hbase]]]].
    destruct (IHHtyping3 rho eta alpha beta sigma tau Halpha Hsigma Hgamma)
      as [step1 [step2 [Hs [Hs' Hstep]]]].
    destruct Hnat as [_ [_ [Heq Hnum]]]; subst a'.
    destruct (relation_values _ _ _ _ _ Hbase) as [Hbv1 Hbv2].
    eapply relation_back.
    + eapply multi_trans.
      * apply multi_rec_arg; [exact Ha| |].
        -- eapply instantiated_typed_lc; [exact Htyping2|
             exact (fun X => proj1 (Halpha X))|exact (fun x => proj1 (Hsigma x))].
        -- eapply instantiated_typed_lc; [exact Htyping3|
             exact (fun X => proj1 (Halpha X))|exact (fun x => proj1 (Hsigma x))].
      * eapply multi_trans.
        -- apply multi_rec_base; [exact Hnum|exact Hb|].
           eapply instantiated_typed_lc; [exact Htyping3|
             exact (fun X => proj1 (Halpha X))|exact (fun x => proj1 (Hsigma x))].
        -- apply multi_rec_step; [exact Hnum|exact Hbv1|exact Hs].
    + eapply multi_trans.
      * apply multi_rec_arg; [exact Ha'| |].
        -- eapply instantiated_typed_lc; [exact Htyping2|
             exact (fun X => proj2 (Halpha X))|exact (fun x => proj2 (Hsigma x))].
        -- eapply instantiated_typed_lc; [exact Htyping3|
             exact (fun X => proj2 (Halpha X))|exact (fun x => proj2 (Hsigma x))].
      * eapply multi_trans.
        -- apply multi_rec_base; [exact Hnum|exact Hb'|].
           eapply instantiated_typed_lc; [exact Htyping3|
             exact (fun X => proj2 (Halpha X))|exact (fun x => proj2 (Hsigma x))].
        -- apply multi_rec_step; [exact Hnum|exact Hbv2|exact Hs'].
    + eapply rec_values_related; eauto.
Qed.

Lemma free_terms_open : forall t k y u,
  In y (free_terms t) -> In y (free_terms (open_tm_rec k u t)).
Proof.
  induction t; intros k y u H; simpl in *; try contradiction;
    try (apply in_app_iff in H as [H|H]; apply in_app_iff;
      [left; eauto|right; eauto]; fail);
    try (eauto; fail).
  - repeat rewrite in_app_iff in *.
    destruct H as [H|[H|H]]; [left|right; left|right; right]; eauto.
  - repeat rewrite in_app_iff in *.
    destruct H as [H|[H|H]]; [left|right; left|right; right]; eauto.
Qed.

Lemma free_terms_open_type : forall t k U,
  free_terms (open_tm_ty_rec k U t) = free_terms t.
Proof.
  induction t; intros k U; simpl; try (f_equal; eauto; fail);
    try (rewrite ?IHt1, ?IHt2, ?IHt3; reflexivity).
  all: rewrite IHt; reflexivity.
Qed.

Lemma typing_free_term : forall Delta Gamma t T y,
  has_type Delta Gamma t T ->
  In y (free_terms t) -> exists A, lookup_context y Gamma = Some A.
Proof.
  intros Delta Gamma t T y Htyping.
  induction Htyping; simpl; intros Hfree; try contradiction.
  - destruct Hfree as [->|[]]; exists T; assumption.
  - set (x := fresh (L ++ [y])).
    assert (HxL : ~ In x L).
    { unfold x; intro E; apply (fresh_not_in (L ++ [y])).
      apply in_or_app; now left. }
    assert (Hxy : x <> y).
    { unfold x; intro E; subst; apply (fresh_not_in (L ++ [y])).
      apply in_or_app; right; now left. }
    destruct (H1 x HxL (free_terms_open t2 0 y (tm_fvar x) Hfree))
      as [A HA].
    simpl in HA. destruct (Nat.eqb y x) eqn:E.
    + apply Nat.eqb_eq in E; symmetry in E; contradiction.
    + exists A; exact HA.
  - apply in_app_iff in Hfree as [Hfree|Hfree];
      [apply IHHtyping1|apply IHHtyping2]; exact Hfree.
  - set (X := fresh L).
    assert (HXL : ~ In X L) by (unfold X; apply fresh_not_in).
    apply (H0 X HXL).
    unfold open_tm_ty.
    rewrite free_terms_open_type; exact Hfree.
  - apply IHHtyping; exact Hfree.
  - repeat rewrite in_app_iff in Hfree.
    destruct Hfree as [Hfree|[Hfree|Hfree]];
      [apply IHHtyping1|apply IHHtyping2|apply IHHtyping3]; exact Hfree.
  - apply IHHtyping; exact Hfree.
  - repeat rewrite in_app_iff in Hfree.
    destruct Hfree as [Hfree|[Hfree|Hfree]];
      [apply IHHtyping1|apply IHHtyping2|apply IHHtyping3]; exact Hfree.
Qed.

Lemma instantiated_identity_type : forall T,
  instantiate_type Ty_FVar T = T.
Proof. induction T; simpl; congruence. Qed.

Lemma instantiated_closed_term : forall t sigma,
  (forall x, ~ In x (free_terms t)) ->
  instantiate_term Ty_FVar sigma t = t.
Proof.
  induction t; intros sigma Hclosed; simpl in *;
    try (f_equal; eauto using instantiated_identity_type; fail).
  - exfalso. apply (Hclosed a); now left.
  - f_equal; [apply IHt1|apply IHt2]; intros x Hin;
      apply (Hclosed x); apply in_or_app; tauto.
  - f_equal; [apply IHt1|apply IHt2|apply IHt3]; intros x Hin;
      apply (Hclosed x); repeat rewrite in_app_iff; tauto.
  - f_equal; [apply IHt1|apply IHt2|apply IHt3]; intros x Hin;
      apply (Hclosed x); repeat rewrite in_app_iff; tauto.
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
  intros t Ht U v HU Hv Hvt.
  assert (Hclosed : forall x, ~ In x (free_terms t)).
  { intros x Hin.
    destruct (typing_free_term [] empty t
      (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) x Ht Hin)
      as [A HA]. discriminate. }
  set (rho := (fun (_ : nat) (_ _ : tm) => False)).
  set (eta := (fun (_ : atom) (_ _ : tm) => False)).
  set (sigma := (fun (_ : atom) => v)).
  pose proof (fundamental_relation [] empty t
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) Ht
    rho eta Ty_FVar Ty_FVar sigma sigma) as Hfund.
  assert (Halpha : forall X,
    locally_closed_ty (Ty_FVar X) /\ locally_closed_ty (Ty_FVar X)).
  { intro X; split; constructor. }
  assert (Hsigma : forall x, value (sigma x) /\ value (sigma x)).
  { intro x; split; exact Hv. }
  specialize (Hfund Halpha Hsigma).
  assert (Hgamma : forall x A, lookup_context x empty = Some A ->
    value_relation A rho eta (sigma x) (sigma x)).
  { intros x A Hlookup; discriminate. }
  specialize (Hfund Hgamma).
  rewrite (instantiated_closed_term t sigma Hclosed) in Hfund.
  destruct Hfund as [p [q [Hp [Hq Hpoly]]]].
  destruct Hpoly as [_ [_ Hpoly]].
  set (R := (fun a b : tm => a = v /\ b = v)).
  destruct (Hpoly U U R (wf_lc _ _ HU) (wf_lc _ _ HU))
    as [f [g [Hf [Hg Hfun]]]].
  destruct Hfun as [_ [_ Hfun]].
  assert (Harg : value_relation (Ty_BVar 0)
    (push_candidate R rho) eta v v).
  { simpl; repeat split; auto. }
  destruct (Hfun v v Harg) as [r [s [Hr [Hs Hresult]]]].
  destruct Hresult as [_ [_ [Heq _]]].
  subst r.
  eapply multi_trans.
  - apply multi_app1.
    + eapply multi_trans; [apply multi_tapp;
        [exact Hp|exact (wf_lc _ _ HU)]|exact Hf].
    + apply value_lc; exact Hv.
  - exact Hr.
Qed.

End SystemFParametricityIfRecursionHardTask.
