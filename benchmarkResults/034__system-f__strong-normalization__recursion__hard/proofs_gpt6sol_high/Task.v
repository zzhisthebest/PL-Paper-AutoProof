(** System F CBV strong-normalization benchmark, Hard variant.
    Features: recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFNormalizationRecursionHardTask.

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

Lemma lc_ty_weaken : forall T k j,
  lc_ty_at k T -> k <= j -> lc_ty_at j T.
Proof.
  intros T k j H; revert j.
  induction H; intros j Hle.
  - apply lc_ty_bvar; lia.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; eauto.
  - apply lc_ty_all. apply IHlc_ty_at. lia.
  - apply lc_ty_nat.
Qed.

Lemma lc_tm_weaken : forall t K k J j,
  lc_tm_at K k t -> K <= J -> k <= j -> lc_tm_at J j t.
Proof.
  intros t K k J j H; revert J j.
  induction H; intros J j HK Hk.
  - apply lc_tm_bvar; lia.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + eapply lc_ty_weaken; eauto.
    + apply IHlc_tm_at; lia.
  - apply lc_tm_app; eauto.
  - apply lc_tm_tabs. apply IHlc_tm_at; lia.
  - apply lc_tm_tapp; eauto using lc_ty_weaken.
  - apply lc_tm_zero.
  - apply lc_tm_succ; eauto.
  - apply lc_tm_rec; eauto.
Qed.

Lemma lc_ty_open_rec : forall T depth U,
  lc_ty_at (S depth) T -> lc_ty_at depth U ->
  lc_ty_at depth (open_ty_rec depth U T).
Proof.
  intros T; induction T; intros depth U HT HU; inversion HT; subst; simpl.
  - destruct (Nat.eqb depth n) eqn:Heq.
    + exact HU.
    + apply lc_ty_bvar. apply Nat.eqb_neq in Heq. lia.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; eauto.
  - apply lc_ty_all. apply IHT. eassumption.
    eapply lc_ty_weaken; eauto; lia.
  - apply lc_ty_nat.
Qed.

Lemma lc_tm_open_rec : forall t depth K u,
  lc_tm_at K (S depth) t -> lc_tm_at K 0 u ->
  lc_tm_at K depth (open_tm_rec depth u t).
Proof.
  intros t; induction t; intros depth K u HT HU; inversion HT; subst; simpl.
  - destruct (Nat.eqb depth n) eqn:Heq.
    + eapply lc_tm_weaken; eauto; lia.
    + apply lc_tm_bvar. apply Nat.eqb_neq in Heq. lia.
  - apply lc_tm_fvar.
  - apply lc_tm_abs; eauto using lc_tm_weaken.
  - apply lc_tm_app; eauto.
  - apply lc_tm_tabs. apply IHt; eauto.
    eapply lc_tm_weaken; eauto; lia.
  - apply lc_tm_tapp; eauto.
  - apply lc_tm_zero.
  - apply lc_tm_succ; eauto.
  - apply lc_tm_rec; eauto.
Qed.

Lemma lc_tm_ty_open_rec : forall t depth k U,
  lc_tm_at (S depth) k t -> lc_ty_at depth U ->
  lc_tm_at depth k (open_tm_ty_rec depth U t).
Proof.
  intros t; induction t; intros depth k U HT HU; inversion HT; subst; simpl.
  - apply lc_tm_bvar; auto.
  - apply lc_tm_fvar.
  - apply lc_tm_abs; eauto using lc_ty_open_rec.
  - apply lc_tm_app; eauto.
  - apply lc_tm_tabs. apply IHt; auto.
    eapply lc_ty_weaken; eauto; lia.
  - apply lc_tm_tapp; eauto using lc_ty_open_rec.
  - apply lc_tm_zero.
  - apply lc_tm_succ; eauto.
  - apply lc_tm_rec; eauto.
Qed.

Lemma lc_ty_open_inverse : forall T depth U,
  lc_ty_at depth (open_ty_rec depth U T) -> lc_ty_at (S depth) T.
Proof.
  intros T; induction T; intros depth U H; simpl in H.
  - destruct (Nat.eqb depth n) eqn:Heq.
    + apply Nat.eqb_eq in Heq; subst. apply lc_ty_bvar; lia.
    + inversion H; subst. apply lc_ty_bvar; lia.
  - apply lc_ty_fvar.
  - inversion H; subst. apply lc_ty_arrow; eauto.
  - inversion H; subst. apply lc_ty_all. apply IHT with (U := U); auto.
  - apply lc_ty_nat.
Qed.

Lemma lc_tm_open_inverse : forall t depth K u,
  lc_tm_at K depth (open_tm_rec depth u t) ->
  lc_tm_at K (S depth) t.
Proof.
  intros t; induction t; intros depth K u H; simpl in H.
  - destruct (Nat.eqb depth n) eqn:Heq.
    + apply Nat.eqb_eq in Heq; subst. apply lc_tm_bvar; lia.
    + inversion H; subst. apply lc_tm_bvar; lia.
  - apply lc_tm_fvar.
  - inversion H; subst. apply lc_tm_abs; eauto.
  - inversion H; subst. apply lc_tm_app; eauto.
  - inversion H; subst. apply lc_tm_tabs; eauto.
  - inversion H; subst. apply lc_tm_tapp; eauto.
  - apply lc_tm_zero.
  - inversion H; subst. apply lc_tm_succ; eauto.
  - inversion H; subst. apply lc_tm_rec; eauto.
Qed.

Lemma lc_tm_ty_open_inverse : forall t depth k U,
  lc_tm_at depth k (open_tm_ty_rec depth U t) ->
  lc_tm_at (S depth) k t.
Proof.
  intros t; induction t; intros depth k U H; simpl in H.
  - inversion H; subst. apply lc_tm_bvar; auto.
  - apply lc_tm_fvar.
  - inversion H; subst. apply lc_tm_abs;
      eauto using lc_ty_open_inverse.
  - inversion H; subst. apply lc_tm_app; eauto.
  - inversion H; subst. apply lc_tm_tabs; eauto.
  - inversion H; subst. apply lc_tm_tapp;
      eauto using lc_ty_open_inverse.
  - apply lc_tm_zero.
  - inversion H; subst. apply lc_tm_succ; eauto.
  - inversion H; subst. apply lc_tm_rec; eauto.
Qed.

Definition fresh_atom (L : list atom) : atom :=
  S (fold_right Nat.max 0 L).

Lemma fold_max_bound : forall L x,
  In x L -> x <= fold_right Nat.max 0 L.
Proof.
  induction L as [|y L IH]; simpl; intros x H.
  - contradiction.
  - destruct H as [<-|H]; [lia|specialize (IH _ H); lia].
Qed.

Lemma fresh_atom_not_in : forall L, ~ In (fresh_atom L) L.
Proof.
  intros L H; unfold fresh_atom in H.
  pose proof (fold_max_bound _ _ H); lia.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H; induction H.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; auto.
  - apply lc_ty_all.
    specialize (H0 (fresh_atom L) (fresh_atom_not_in L)).
    apply lc_ty_open_inverse with (U := Ty_FVar (fresh_atom L)); exact H0.
  - apply lc_ty_nat.
Qed.

Lemma has_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T H; induction H.
  - apply lc_tm_fvar.
  - apply lc_tm_abs; [apply wf_ty_lc with (Delta := Delta); auto|].
    specialize (H1 (fresh_atom L) (fresh_atom_not_in L)).
    apply lc_tm_open_inverse with (u := tm_fvar (fresh_atom L)); exact H1.
  - apply lc_tm_app; auto.
  - apply lc_tm_tabs.
    specialize (H0 (fresh_atom L) (fresh_atom_not_in L)).
    apply lc_tm_ty_open_inverse with (U := Ty_FVar (fresh_atom L)); exact H0.
  - apply lc_tm_tapp; [assumption|apply wf_ty_lc with (Delta := Delta); auto].
  - apply lc_tm_zero.
  - apply lc_tm_succ; auto.
  - apply lc_tm_rec; auto.
Qed.

Lemma numeric_value_lc : forall n, numeric_value n -> locally_closed_tm n.
Proof.
  intros n H; induction H; constructor; auto.
Qed.

Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof.
  intros v H; inversion H; subst; eauto using numeric_value_lc.
Qed.

Lemma step_lc : forall t u,
  t --> u -> locally_closed_tm t -> locally_closed_tm u.
Proof.
  intros t u H; induction H; intros Hlc;
    unfold locally_closed_tm in *; inversion Hlc; subst;
    eauto 12 using lc_tm_open_rec, lc_tm_ty_open_rec, value_lc, numeric_value_lc.
  - inversion H; subst. eapply lc_tm_open_rec; eauto using value_lc.
  - inversion H; subst. eapply lc_tm_ty_open_rec; eauto.
  - apply lc_tm_app.
    + apply lc_tm_app; eauto using value_lc.
      apply numeric_value_lc; assumption.
    + apply lc_tm_rec; eauto using value_lc.
      apply numeric_value_lc; assumption.
Qed.

Record candidate (P : tm -> Prop) : Prop := {
  candidate_sn : forall t, P t -> strongly_normalizing t;
  candidate_lc : forall t, P t -> locally_closed_tm t;
  candidate_step : forall t u, P t -> t --> u -> P u;
  candidate_expand : forall t,
    locally_closed_tm t -> ~ value t ->
    (forall u, t --> u -> P u) -> P t
}.

Definition type_environment := list (tm -> Prop).
Definition free_type_environment := atom -> tm -> Prop.

Fixpoint reducible (T : ty) (rho : type_environment)
  (eta : free_type_environment) (t : tm) : Prop :=
  match T with
  | Ty_BVar n => match nth_error rho n with Some P => P t
      | None => locally_closed_tm t /\ strongly_normalizing t end
  | Ty_FVar X => eta X t
  | Ty_Arrow A B =>
      locally_closed_tm t /\ strongly_normalizing t /\
      (forall v, t -->* v -> value v ->
         exists body, exists annotation, v = tm_abs annotation body /\
           forall w, reducible A rho eta w -> value w ->
             reducible B rho eta (open_tm body w))
  | Ty_All A =>
      locally_closed_tm t /\ strongly_normalizing t /\
      (forall v, t -->* v -> value v ->
         exists body, v = tm_tabs body /\
           forall U (P : tm -> Prop), locally_closed_ty U -> candidate P ->
             reducible A (P :: rho) eta (open_tm_ty body U))
  | Ty_Nat =>
      locally_closed_tm t /\ strongly_normalizing t /\
      (forall v, t -->* v -> value v -> numeric_value v)
  end.

Lemma multi_trans : forall t u v,
  t -->* u -> u -->* v -> t -->* v.
Proof.
  intros t u v H; induction H; intros Huv; eauto using multi.
Qed.

Lemma sn_step : forall t u,
  strongly_normalizing t -> t --> u -> strongly_normalizing u.
Proof.
  intros t u H Hstep; inversion H; eauto.
Qed.

Definition saturated (Q : tm -> Prop) (t : tm) : Prop :=
  locally_closed_tm t /\ strongly_normalizing t /\
  forall v, t -->* v -> value v -> Q v.

Lemma saturated_candidate : forall Q, candidate (saturated Q).
Proof.
  intros Q; constructor.
  - intros t [_ [H _]]; exact H.
  - intros t [H _]; exact H.
  - intros t u [Hlc [Hsn Hvalues]] Hstep.
    split; [eapply step_lc; eauto|].
    split; [eapply sn_step; eauto|].
    intros v Hmulti Hv. apply Hvalues; auto.
    eapply multi_step; eauto.
  - intros t Hlc Hnot Hsuccessors.
    split; [exact Hlc|].
    split.
    + constructor. intros v Htv.
      destruct (Hsuccessors v Htv) as [_ [Hsn _]]; exact Hsn.
    + intros v Hmulti Hv. inversion Hmulti; subst.
      * contradiction.
      * destruct (Hsuccessors _ H) as [_ [_ Hvalues]].
        apply Hvalues; assumption.
Qed.

Lemma reducible_candidate : forall T rho eta,
  (forall P, In P rho -> candidate P) ->
  (forall X, candidate (eta X)) ->
  candidate (reducible T rho eta).
Proof.
  intros T; induction T; intros rho eta Henv Hfree; simpl.
  - destruct (nth_error rho n) as [P|] eqn:HP.
    + apply Henv. apply nth_error_In with (n := n); exact HP.
    + constructor.
      * intros t [_ H]; exact H.
      * intros t [H _]; exact H.
      * intros t u [Hlc Hsn] Hstep.
        split; [eapply step_lc; eauto|eapply sn_step; eauto].
      * intros t Hlc Hnot Hsucc. split; [exact Hlc|].
        constructor; intros u Hstep.
        destruct (Hsucc u Hstep) as [_ Hsn]; exact Hsn.
  - apply Hfree.
  - apply saturated_candidate.
  - apply saturated_candidate.
  - apply saturated_candidate.
Qed.

Lemma numeric_no_step : forall n u,
  numeric_value n -> n --> u -> False.
Proof.
  intros n u Hnum; revert u.
  induction Hnum; intros u Hstep; inversion Hstep; subst; eauto.
Qed.

Lemma value_no_step : forall v u, value v -> v --> u -> False.
Proof.
  intros v u Hvalue Hstep; inversion Hvalue; subst;
    inversion Hstep; subst; eauto using numeric_no_step.
Qed.

Lemma reducible_app : forall A B rho eta t1 t2,
  (forall P, In P rho -> candidate P) ->
  (forall X, candidate (eta X)) ->
  reducible (Ty_Arrow A B) rho eta t1 ->
  reducible A rho eta t2 ->
  reducible B rho eta (tm_app t1 t2).
Proof.
  intros A B rho eta t1 t2 Henv Hfree H1 H2.
  pose proof (reducible_candidate B rho eta Henv Hfree) as CB.
  pose proof (reducible_candidate A rho eta Henv Hfree) as CA.
  pose proof (reducible_candidate (Ty_Arrow A B) rho eta Henv Hfree) as CF.
  pose proof (candidate_sn _ CF _ H1) as SN1.
  revert t2 H1 H2.
  induction SN1 as [t1 _ IH1]; intros t2 H1 H2.
  pose proof (candidate_sn _ CA _ H2) as SN2.
  revert H2.
  induction SN2 as [t2 _ IH2]; intros H2.
  apply (candidate_expand _ CB).
  - apply lc_tm_app; [apply (candidate_lc _ CF); exact H1|
                      apply (candidate_lc _ CA); exact H2].
  - intros Hvalue; inversion Hvalue; subst;
      match goal with Hnum : numeric_value (tm_app _ _) |- _ => inversion Hnum end.
  - intros u Hstep. inversion Hstep; subst.
    + destruct H1 as [_ [_ Hvalues]].
      destruct (Hvalues _ (multi_refl _) (v_abs _ _ H3)) as
        [body [annotation [Heq Hbody]]].
      inversion Heq; subst. apply Hbody; assumption.
    + apply IH1; [exact H3|apply (candidate_step _ CF _ _ H1 H3)|exact H2].
    + apply IH2; [assumption|eapply candidate_step; eauto].
Qed.

Lemma reducible_tapp : forall A rho eta t U P,
  (forall P, In P rho -> candidate P) ->
  (forall X, candidate (eta X)) ->
  locally_closed_ty U -> candidate P ->
  reducible (Ty_All A) rho eta t ->
  reducible A (P :: rho) eta (tm_tapp t U).
Proof.
  intros A rho eta t U P Henv Hfree HU CU Ht.
  pose proof (reducible_candidate A (P :: rho) eta)
    as CA.
  assert (Henv' : forall Q, In Q (P :: rho) -> candidate Q).
  { intros Q [Heq|H]; [subst; exact CU|apply Henv; exact H]. }
  specialize (CA Henv' Hfree).
  pose proof (reducible_candidate (Ty_All A) rho eta Henv Hfree) as CT.
  pose proof (candidate_sn _ CT _ Ht) as Hsn.
  induction Hsn as [t _ IH].
  apply (candidate_expand _ CA).
  - apply lc_tm_tapp; [apply (candidate_lc _ CT); exact Ht|exact HU].
  - intros Hv; inversion Hv; subst;
      match goal with Hnum : numeric_value (tm_tapp _ _) |- _ => inversion Hnum end.
  - intros u Hstep. inversion Hstep; subst.
    + destruct Ht as [_ [_ Hvalues]].
      destruct (Hvalues _ (multi_refl _) (v_tabs _ H1)) as [body [Heq Hbody]].
      inversion Heq; subst. apply Hbody; assumption.
    + apply IH. eassumption. eapply candidate_step; eauto.
Qed.

Lemma reducible_zero : forall rho eta,
  reducible Ty_Nat rho eta tm_zero.
Proof.
  intros rho eta; simpl.
  split; [apply lc_tm_zero|].
  split.
  - constructor; intros u Hstep; inversion Hstep.
  - intros v Hmulti Hv; inversion Hmulti; subst.
    + constructor.
    + exfalso; eapply numeric_no_step; [constructor|eassumption].
Qed.

Lemma reducible_succ : forall rho eta n,
  reducible Ty_Nat rho eta n ->
  reducible Ty_Nat rho eta (tm_succ n).
Proof.
  intros rho eta n [Hlc [Hsn Hvalues]].
  revert Hlc Hvalues.
  induction Hsn as [n _ IH]; intros Hlc Hvalues.
  simpl.
  split; [apply lc_tm_succ; exact Hlc|].
  split.
  - constructor. intros u Hstep; inversion Hstep; subst.
    destruct (IH _ H0) as [_ [Hsn' _]].
    + eapply step_lc; eauto.
    + intros v Hmulti Hv. apply Hvalues; auto.
      eapply multi_step; eauto.
    + exact Hsn'.
  - intros v Hmulti Hv.
    inversion Hmulti; subst.
    + inversion Hv; subst; assumption.
    + inversion H; subst.
      destruct (IH _ H2) as [_ [_ Hvalid]].
      * eapply step_lc; eauto.
      * intros w Hmulti' Hw. apply Hvalues; auto.
        eapply multi_step; eauto.
      * apply Hvalid with (v := v); auto.
Qed.

Lemma numeral_numeric : forall count, numeric_value (numeral count).
Proof.
  induction count; simpl; constructor; assumption.
Qed.

Lemma numeric_reducible : forall rho eta n,
  numeric_value n -> reducible Ty_Nat rho eta n.
Proof.
  intros rho eta n Hnumeric; simpl.
  split; [apply numeric_value_lc; assumption|].
  split.
  - constructor; intros u Hstep.
    exfalso; eapply numeric_no_step; eauto.
  - intros v Hmulti Hv. inversion Hmulti; subst; auto.
    exfalso; eapply numeric_no_step; eauto.
Qed.

Lemma reducible_rec_numeral : forall count T rho eta b s,
  (forall P, In P rho -> candidate P) ->
  (forall X, candidate (eta X)) ->
  reducible T rho eta b ->
  reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) rho eta s ->
  reducible T rho eta (tm_natrec (numeral count) b s).
Proof.
  intros count T rho eta; induction count as [|count IH];
    intros b s Henv Hfree Hb Hs.
  all: pose proof (reducible_candidate T rho eta Henv Hfree) as CB.
  all: pose proof (reducible_candidate (Ty_Arrow Ty_Nat (Ty_Arrow T T))
    rho eta Henv Hfree) as CS.
  all: pose proof (candidate_sn _ CB _ Hb) as SNb.
  all: revert s Hb Hs.
  all: induction SNb as [b _ IHb]; intros s Hb Hs.
  all: pose proof (candidate_sn _ CS _ Hs) as SNs.
  all: revert Hs.
  all: induction SNs as [s _ IHs]; intros Hs.
  all: apply (candidate_expand _ CB).
  all: try (apply lc_tm_rec;
    [apply numeric_value_lc, numeral_numeric|
     apply (candidate_lc _ CB); exact Hb|
     apply (candidate_lc _ CS); exact Hs]).
  all: try (intros Hv; inversion Hv; subst;
    match goal with Hn : numeric_value (tm_natrec _ _ _) |- _ => inversion Hn end).
  all: intros u Hstep; inversion Hstep; subst;
    try (match goal with H : tm_zero --> _ |- _ => inversion H end);
    try (match goal with H : (tm_succ _) --> _ |- _ =>
      exfalso; eapply numeric_no_step;
      [apply nv_succ, numeral_numeric|exact H] end);
    try (apply IHb; [eassumption|
      eapply candidate_step; eauto|exact Hs]);
    try (apply IHs; [eassumption|eapply candidate_step; eauto]).
  - exact Hb.
  - apply (reducible_app T T rho eta); auto.
    eapply reducible_app; eauto using numeric_reducible, numeral_numeric.
Qed.

Lemma numeric_is_numeral : forall n,
  numeric_value n -> exists count, n = numeral count.
Proof.
  intros n H; induction H as [|n _ [count Heq]].
  - exists 0; reflexivity.
  - exists (S count); simpl; congruence.
Qed.

Lemma reducible_rec : forall T rho eta n b s,
  (forall P, In P rho -> candidate P) ->
  (forall X, candidate (eta X)) ->
  reducible Ty_Nat rho eta n ->
  reducible T rho eta b ->
  reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) rho eta s ->
  reducible T rho eta (tm_natrec n b s).
Proof.
  intros T rho eta n b s Henv Hfree Hn Hb Hs.
  pose proof (reducible_candidate T rho eta Henv Hfree) as CB.
  pose proof (reducible_candidate Ty_Nat rho eta Henv Hfree) as CN.
  pose proof (reducible_candidate (Ty_Arrow Ty_Nat (Ty_Arrow T T))
    rho eta Henv Hfree) as CS.
  pose proof (candidate_sn _ CN _ Hn) as SNn.
  revert b s Hn Hb Hs.
  induction SNn as [n _ IHn]; intros b s Hn Hb Hs.
  pose proof (candidate_sn _ CB _ Hb) as SNb.
  revert s Hn Hb Hs.
  induction SNb as [b _ IHb]; intros s Hn Hb Hs.
  pose proof (candidate_sn _ CS _ Hs) as SNs.
  revert Hn Hs.
  induction SNs as [s _ IHs]; intros Hn Hs.
  apply (candidate_expand _ CB).
  - apply lc_tm_rec; [apply (candidate_lc _ CN); exact Hn|
      apply (candidate_lc _ CB); exact Hb|
      apply (candidate_lc _ CS); exact Hs].
  - intros Hv; inversion Hv; subst;
      match goal with Hnum : numeric_value (tm_natrec _ _ _) |- _ => inversion Hnum end.
  - intros u Hstep; inversion Hstep; subst;
      try (apply IHn; [eassumption|eapply candidate_step; eauto|
        exact Hb|exact Hs]);
      try (apply IHb; [eassumption|exact Hn|
        eapply candidate_step; eauto|exact Hs]);
      try (apply IHs; [eassumption|exact Hn|
        eapply candidate_step; eauto]).
    + exact Hb.
    + match goal with Hnum : numeric_value ?pred |- _ =>
        destruct (numeric_is_numeral _ Hnum) as [count Heq]; subst pred end.
      apply (reducible_app T T rho eta); auto.
      eapply reducible_app; eauto using numeric_reducible, numeral_numeric.
      apply reducible_rec_numeral; assumption.
Qed.

Lemma reducible_abs : forall A B rho eta annotation body,
  locally_closed_tm (tm_abs annotation body) ->
  (forall w, reducible A rho eta w -> value w ->
     reducible B rho eta (open_tm body w)) ->
  reducible (Ty_Arrow A B) rho eta (tm_abs annotation body).
Proof.
  intros A B rho eta annotation body Hlc Hbody; simpl.
  split; [exact Hlc|].
  split.
  - constructor; intros u Hstep.
    exfalso; eapply value_no_step; [apply v_abs; exact Hlc|exact Hstep].
  - intros v Hmulti Hv; inversion Hmulti; subst.
    + exists body, annotation; split; [reflexivity|exact Hbody].
    + exfalso; eapply value_no_step; [apply v_abs; exact Hlc|eassumption].
Qed.

Lemma reducible_tabs : forall A rho eta body,
  locally_closed_tm (tm_tabs body) ->
  (forall U P, locally_closed_ty U -> candidate P ->
     reducible A (P :: rho) eta (open_tm_ty body U)) ->
  reducible (Ty_All A) rho eta (tm_tabs body).
Proof.
  intros A rho eta body Hlc Hbody; simpl.
  split; [exact Hlc|].
  split.
  - constructor; intros u Hstep.
    exfalso; eapply value_no_step; [apply v_tabs; exact Hlc|exact Hstep].
  - intros v Hmulti Hv; inversion Hmulti; subst.
    + exists body; split; [reflexivity|exact Hbody].
    + exfalso; eapply value_no_step; [apply v_tabs; exact Hlc|eassumption].
Qed.

Lemma reducible_rho_agree : forall T k rho1 rho2 eta t,
  lc_ty_at k T ->
  (forall i, i < k -> nth_error rho1 i = nth_error rho2 i) ->
  (reducible T rho1 eta t <-> reducible T rho2 eta t).
Proof.
  intros T; induction T; intros k rho1 rho2 eta t Hlc Hagree;
    inversion Hlc; subst; simpl.
  - match goal with Hindex : n < k |- _ => rewrite (Hagree n Hindex) end.
    reflexivity.
  - reflexivity.
  - assert (Hreverse : forall i, i < k -> nth_error rho2 i = nth_error rho1 i).
    { intros i Hi; symmetry; apply Hagree; exact Hi. }
    split.
    + intros [Hclosed [Hsn Hvalues]].
      split; [exact Hclosed|]. split; [exact Hsn|].
      intros v Hmulti Hv.
      destruct (Hvalues v Hmulti Hv) as [body [annotation [Heq Hbody]]].
      exists body, annotation; split; [exact Heq|].
      intros w Hw Hwv.
      match goal with Harg : lc_ty_at k T1, Hres : lc_ty_at k T2 |- _ =>
        apply (proj1 (IHT2 k rho1 rho2 eta (open_tm body w) Hres Hagree));
        apply Hbody; [apply (proj2 (IHT1 k rho1 rho2 eta w Harg Hagree));
          exact Hw|exact Hwv] end.
    + intros [Hclosed [Hsn Hvalues]].
      split; [exact Hclosed|]. split; [exact Hsn|].
      intros v Hmulti Hv.
      destruct (Hvalues v Hmulti Hv) as [body [annotation [Heq Hbody]]].
      exists body, annotation; split; [exact Heq|].
      intros w Hw Hwv.
      match goal with Harg : lc_ty_at k T1, Hres : lc_ty_at k T2 |- _ =>
        apply (proj2 (IHT2 k rho1 rho2 eta (open_tm body w) Hres Hagree));
        apply Hbody; [apply (proj1 (IHT1 k rho1 rho2 eta w Harg Hagree));
          exact Hw|exact Hwv] end.
  - assert (Hcons : forall P i, i < S k ->
        nth_error (P :: rho1) i = nth_error (P :: rho2) i).
    { intros P [|i] Hi; simpl; [reflexivity|apply Hagree; lia]. }
    split.
    + intros [Hclosed [Hsn Hvalues]].
      split; [exact Hclosed|]. split; [exact Hsn|].
      intros v Hmulti Hv.
      destruct (Hvalues v Hmulti Hv) as [body [Heq Hbody]].
      exists body; split; [exact Heq|].
      intros U P HU HP.
      match goal with Hinner : lc_ty_at (S k) T |- _ =>
        apply (proj1 (IHT (S k) (P :: rho1) (P :: rho2) eta
          (open_tm_ty body U) Hinner (Hcons P))); apply Hbody; assumption end.
    + intros [Hclosed [Hsn Hvalues]].
      split; [exact Hclosed|]. split; [exact Hsn|].
      intros v Hmulti Hv.
      destruct (Hvalues v Hmulti Hv) as [body [Heq Hbody]].
      exists body; split; [exact Heq|].
      intros U P HU HP.
      match goal with Hinner : lc_ty_at (S k) T |- _ =>
        apply (proj2 (IHT (S k) (P :: rho1) (P :: rho2) eta
          (open_tm_ty body U) Hinner (Hcons P))); apply Hbody; assumption end.
  - reflexivity.
Qed.

Lemma reducible_ty_open : forall T prefix suffix U eta t,
  lc_ty_at (S (length prefix)) T -> locally_closed_ty U ->
  (reducible (open_ty_rec (length prefix) U T)
     (prefix ++ suffix) eta t <->
   reducible T (prefix ++ reducible U suffix eta :: suffix) eta t).
Proof.
  intros T; induction T; intros prefix suffix U eta t Hlc HU;
    inversion Hlc; subst; simpl.
  - destruct (Nat.eqb (length prefix) n) eqn:Heq.
    + apply Nat.eqb_eq in Heq; subst n.
      rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. simpl.
      apply reducible_rho_agree with (k := 0); [exact HU|].
      intros i Hi; lia.
    + apply Nat.eqb_neq in Heq.
      assert (n < length prefix) by lia.
      simpl.
      rewrite nth_error_app1 by assumption.
      rewrite nth_error_app1 by assumption.
      reflexivity.
  - reflexivity.
  - split.
    + intros [Hclosed [Hsn Hvalues]].
      split; [exact Hclosed|]. split; [exact Hsn|].
      intros v Hmulti Hv.
      destruct (Hvalues v Hmulti Hv) as [body [annotation [Heq Hbody]]].
      exists body, annotation; split; [exact Heq|].
      intros w Hw Hwv.
      match goal with Harg : lc_ty_at (S (length prefix)) T1,
        Hres : lc_ty_at (S (length prefix)) T2 |- _ =>
        apply (proj1 (IHT2 prefix suffix U eta (open_tm body w) Hres HU));
        apply Hbody; [apply (proj2 (IHT1 prefix suffix U eta w Harg HU));
          exact Hw|exact Hwv] end.
    + intros [Hclosed [Hsn Hvalues]].
      split; [exact Hclosed|]. split; [exact Hsn|].
      intros v Hmulti Hv.
      destruct (Hvalues v Hmulti Hv) as [body [annotation [Heq Hbody]]].
      exists body, annotation; split; [exact Heq|].
      intros w Hw Hwv.
      match goal with Harg : lc_ty_at (S (length prefix)) T1,
        Hres : lc_ty_at (S (length prefix)) T2 |- _ =>
        apply (proj2 (IHT2 prefix suffix U eta (open_tm body w) Hres HU));
        apply Hbody; [apply (proj1 (IHT1 prefix suffix U eta w Harg HU));
          exact Hw|exact Hwv] end.
  - split.
    + intros [Hclosed [Hsn Hvalues]].
      split; [exact Hclosed|]. split; [exact Hsn|].
      intros v Hmulti Hv.
      destruct (Hvalues v Hmulti Hv) as [body [Heq Hbody]].
      exists body; split; [exact Heq|].
      intros V P HV HP.
      match goal with Hinner : lc_ty_at (S (S (length prefix))) T |- _ =>
        apply (proj1 (IHT (P :: prefix) suffix U eta
          (open_tm_ty body V) Hinner HU)) end.
      apply Hbody; assumption.
    + intros [Hclosed [Hsn Hvalues]].
      split; [exact Hclosed|]. split; [exact Hsn|].
      intros v Hmulti Hv.
      destruct (Hvalues v Hmulti Hv) as [body [Heq Hbody]].
      exists body; split; [exact Heq|].
      intros V P HV HP.
      match goal with Hinner : lc_ty_at (S (S (length prefix))) T |- _ =>
        apply (proj2 (IHT (P :: prefix) suffix U eta
          (open_tm_ty body V) Hinner HU)) end.
      apply Hbody; assumption.
  - reflexivity.
Qed.

Fixpoint map_ty (theta : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar n => Ty_BVar n
  | Ty_FVar X => theta X
  | Ty_Arrow A B => Ty_Arrow (map_ty theta A) (map_ty theta B)
  | Ty_All A => Ty_All (map_ty theta A)
  | Ty_Nat => Ty_Nat
  end.

Fixpoint map_tm_ty (theta : atom -> ty) (t : tm) : tm :=
  match t with
  | tm_bvar n => tm_bvar n
  | tm_fvar x => tm_fvar x
  | tm_abs T body => tm_abs (map_ty theta T) (map_tm_ty theta body)
  | tm_app f a => tm_app (map_tm_ty theta f) (map_tm_ty theta a)
  | tm_tabs body => tm_tabs (map_tm_ty theta body)
  | tm_tapp f U => tm_tapp (map_tm_ty theta f) (map_ty theta U)
  | tm_zero => tm_zero
  | tm_succ n => tm_succ (map_tm_ty theta n)
  | tm_natrec n b s => tm_natrec (map_tm_ty theta n)
      (map_tm_ty theta b) (map_tm_ty theta s)
  end.

Fixpoint map_tm (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar n => tm_bvar n
  | tm_fvar x => sigma x
  | tm_abs T body => tm_abs T (map_tm sigma body)
  | tm_app f a => tm_app (map_tm sigma f) (map_tm sigma a)
  | tm_tabs body => tm_tabs (map_tm sigma body)
  | tm_tapp f U => tm_tapp (map_tm sigma f) U
  | tm_zero => tm_zero
  | tm_succ n => tm_succ (map_tm sigma n)
  | tm_natrec n b s => tm_natrec (map_tm sigma n)
      (map_tm sigma b) (map_tm sigma s)
  end.

Lemma lc_ty_open_identity : forall T k depth U,
  lc_ty_at k T -> k <= depth -> open_ty_rec depth U T = T.
Proof.
  intros T k depth U H; revert depth U.
  induction H; intros depth U Hle; simpl.
  - destruct (Nat.eqb depth i) eqn:Heq; [apply Nat.eqb_eq in Heq; lia|reflexivity].
  - reflexivity.
  - f_equal; eauto.
  - f_equal. apply IHlc_ty_at; lia.
  - reflexivity.
Qed.

Lemma lc_tm_open_identity : forall t K k depth u,
  lc_tm_at K k t -> k <= depth -> open_tm_rec depth u t = t.
Proof.
  intros t K k depth u H; revert depth u.
  induction H; intros depth u Hle; simpl.
  - destruct (Nat.eqb depth i) eqn:Heq; [apply Nat.eqb_eq in Heq; lia|reflexivity].
  - reflexivity.
  - f_equal. apply IHlc_tm_at; lia.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - reflexivity.
  - f_equal; eauto.
  - f_equal; eauto.
Qed.

Lemma lc_tm_ty_open_identity : forall t K k depth U,
  lc_tm_at K k t -> K <= depth -> open_tm_ty_rec depth U t = t.
Proof.
  intros t K k depth U H; revert depth U.
  induction H; intros depth U Hle; simpl; try reflexivity.
  - f_equal; eauto using lc_ty_open_identity.
  - f_equal; eauto.
  - f_equal. apply IHlc_tm_at; lia.
  - f_equal; eauto using lc_ty_open_identity.
  - f_equal; eauto.
  - f_equal; eauto.
Qed.

Lemma map_ty_open : forall T theta U depth,
  (forall X, locally_closed_ty (theta X)) ->
  map_ty theta (open_ty_rec depth U T) =
  open_ty_rec depth (map_ty theta U) (map_ty theta T).
Proof.
  intros T; induction T; intros theta U depth Htheta; simpl;
    try (f_equal; eauto; fail).
  - destruct (Nat.eqb depth n); reflexivity.
  - symmetry. eapply lc_ty_open_identity; [exact (Htheta a)|lia].
Qed.

Lemma map_tm_open : forall t sigma u depth,
  (forall x, locally_closed_tm (sigma x)) ->
  map_tm sigma (open_tm_rec depth u t) =
  open_tm_rec depth (map_tm sigma u) (map_tm sigma t).
Proof.
  intros t; induction t; intros sigma u depth Hsigma; simpl;
    try (f_equal; eauto; fail).
  - destruct (Nat.eqb depth n); reflexivity.
  - symmetry. eapply lc_tm_open_identity; [exact (Hsigma a)|lia].
Qed.

Lemma map_tm_ty_open : forall t theta u depth,
  map_tm_ty theta (open_tm_rec depth u t) =
  open_tm_rec depth (map_tm_ty theta u) (map_tm_ty theta t).
Proof.
  intros t; induction t; intros theta u depth; simpl;
    try (f_equal; eauto; fail).
  destruct (Nat.eqb depth n); reflexivity.
Qed.

Lemma map_tm_ty_open_ty : forall t theta U depth,
  (forall X, locally_closed_ty (theta X)) ->
  map_tm_ty theta (open_tm_ty_rec depth U t) =
  open_tm_ty_rec depth (map_ty theta U) (map_tm_ty theta t).
Proof.
  intros t; induction t; intros theta U depth Htheta; simpl;
    try (f_equal; eauto using map_ty_open; fail).
Qed.

Lemma map_tm_open_ty : forall t sigma U depth,
  (forall x, locally_closed_tm (sigma x)) ->
  map_tm sigma (open_tm_ty_rec depth U t) =
  open_tm_ty_rec depth U (map_tm sigma t).
Proof.
  intros t; induction t; intros sigma U depth Hsigma; simpl;
    try (f_equal; eauto; fail).
  symmetry. eapply lc_tm_ty_open_identity; [exact (Hsigma a)|lia].
Qed.

Fixpoint type_atoms (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow A B => type_atoms A ++ type_atoms B
  | Ty_All A => type_atoms A
  | Ty_Nat => []
  end.

Fixpoint term_atoms (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs _ body => term_atoms body
  | tm_app f a => term_atoms f ++ term_atoms a
  | tm_tabs body => term_atoms body
  | tm_tapp f _ => term_atoms f
  | tm_zero => []
  | tm_succ n => term_atoms n
  | tm_natrec n b s => term_atoms n ++ term_atoms b ++ term_atoms s
  end.

Fixpoint term_type_atoms (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_fvar _ | tm_zero => []
  | tm_abs T body => type_atoms T ++ term_type_atoms body
  | tm_app f a => term_type_atoms f ++ term_type_atoms a
  | tm_tabs body => term_type_atoms body
  | tm_tapp f U => term_type_atoms f ++ type_atoms U
  | tm_succ n => term_type_atoms n
  | tm_natrec n b s =>
      term_type_atoms n ++ term_type_atoms b ++ term_type_atoms s
  end.

Fixpoint context_type_atoms (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (_, T) :: rest => type_atoms T ++ context_type_atoms rest
  end.

Lemma map_ty_agree : forall T theta theta',
  (forall X, In X (type_atoms T) -> theta X = theta' X) ->
  map_ty theta T = map_ty theta' T.
Proof.
  induction T; intros theta theta' Hagree; simpl in *; try reflexivity.
  - apply Hagree; auto.
  - f_equal.
    + apply IHT1; intros X HX; apply Hagree; apply in_or_app; auto.
    + apply IHT2; intros X HX; apply Hagree; apply in_or_app; auto.
  - f_equal. apply IHT; exact Hagree.
Qed.

Lemma map_tm_agree : forall t sigma sigma',
  (forall x, In x (term_atoms t) -> sigma x = sigma' x) ->
  map_tm sigma t = map_tm sigma' t.
Proof.
  induction t; intros sigma sigma' Hagree; simpl in *; try reflexivity.
  - apply Hagree; auto.
  - f_equal. apply IHt; exact Hagree.
  - f_equal.
    + apply IHt1; intros x Hx; apply Hagree; apply in_or_app; auto.
    + apply IHt2; intros x Hx; apply Hagree; apply in_or_app; auto.
  - f_equal. apply IHt; exact Hagree.
  - f_equal. apply IHt; exact Hagree.
  - f_equal. apply IHt; exact Hagree.
  - f_equal.
    + apply IHt1; intros x Hx; apply Hagree. apply in_or_app; auto.
    + apply IHt2; intros x Hx; apply Hagree.
      apply in_or_app; right; apply in_or_app; auto.
    + apply IHt3; intros x Hx; apply Hagree.
      repeat (apply in_or_app; right); auto.
Qed.

Lemma map_tm_ty_agree : forall t theta theta',
  (forall X, In X (term_type_atoms t) -> theta X = theta' X) ->
  map_tm_ty theta t = map_tm_ty theta' t.
Proof.
  induction t; intros theta theta' Hagree; simpl in *; try reflexivity.
  - f_equal.
    + apply map_ty_agree; intros X HX; apply Hagree; apply in_or_app; auto.
    + apply IHt; intros X HX; apply Hagree; apply in_or_app; auto.
  - f_equal.
    + apply IHt1; intros X HX; apply Hagree; apply in_or_app; auto.
    + apply IHt2; intros X HX; apply Hagree; apply in_or_app; auto.
  - f_equal. apply IHt; exact Hagree.
  - f_equal.
    + apply IHt; intros X HX; apply Hagree; apply in_or_app; auto.
    + apply map_ty_agree; intros X HX; apply Hagree; apply in_or_app; auto.
  - f_equal. apply IHt; exact Hagree.
  - f_equal.
    + apply IHt1; intros X HX; apply Hagree. apply in_or_app; auto.
    + apply IHt2; intros X HX; apply Hagree.
      apply in_or_app; right; apply in_or_app; auto.
    + apply IHt3; intros X HX; apply Hagree.
      repeat (apply in_or_app; right); auto.
Qed.

Lemma reducible_eta_agree : forall T rho eta eta' t,
  (forall X, In X (type_atoms T) -> eta X = eta' X) ->
  (reducible T rho eta t <-> reducible T rho eta' t).
Proof.
  intros T; induction T; intros rho eta eta' t Hagree; simpl.
  - reflexivity.
  - rewrite (Hagree a (or_introl eq_refl)); reflexivity.
  - assert (Harg : forall X, In X (type_atoms T1) -> eta X = eta' X).
    { intros X HX; apply Hagree, in_or_app; auto. }
    assert (Hres : forall X, In X (type_atoms T2) -> eta X = eta' X).
    { intros X HX; apply Hagree, in_or_app; auto. }
    split.
    + intros [Hclosed [Hsn Hvalues]].
      split; [exact Hclosed|]. split; [exact Hsn|].
      intros v Hmulti Hv.
      destruct (Hvalues v Hmulti Hv) as [body [annotation [Heq Hbody]]].
      exists body, annotation; split; [exact Heq|].
      intros w Hw Hwv.
      apply (proj1 (IHT2 rho eta eta' (open_tm body w) Hres)).
      apply Hbody; [apply (proj2 (IHT1 rho eta eta' w Harg)); exact Hw|exact Hwv].
    + intros [Hclosed [Hsn Hvalues]].
      split; [exact Hclosed|]. split; [exact Hsn|].
      intros v Hmulti Hv.
      destruct (Hvalues v Hmulti Hv) as [body [annotation [Heq Hbody]]].
      exists body, annotation; split; [exact Heq|].
      intros w Hw Hwv.
      apply (proj2 (IHT2 rho eta eta' (open_tm body w) Hres)).
      apply Hbody; [apply (proj1 (IHT1 rho eta eta' w Harg)); exact Hw|exact Hwv].
  - split.
    + intros [Hclosed [Hsn Hvalues]].
      split; [exact Hclosed|]. split; [exact Hsn|].
      intros v Hmulti Hv.
      destruct (Hvalues v Hmulti Hv) as [body [Heq Hbody]].
      exists body; split; [exact Heq|].
      intros U P HU HP.
      apply (proj1 (IHT (P :: rho) eta eta' (open_tm_ty body U)
        Hagree)); apply Hbody; assumption.
    + intros [Hclosed [Hsn Hvalues]].
      split; [exact Hclosed|]. split; [exact Hsn|].
      intros v Hmulti Hv.
      destruct (Hvalues v Hmulti Hv) as [body [Heq Hbody]].
      exists body; split; [exact Heq|].
      intros U P HU HP.
      apply (proj2 (IHT (P :: rho) eta eta' (open_tm_ty body U)
        Hagree)); apply Hbody; assumption.
  - reflexivity.
Qed.

Definition eta_update (eta : free_type_environment) (X : atom)
  (P : tm -> Prop) : free_type_environment :=
  fun Y => if Nat.eqb X Y then P else eta Y.

Lemma reducible_open_fvar : forall T X P rho eta t,
  lc_ty_at 1 T -> ~ In X (type_atoms T) ->
  (reducible (open_ty T (Ty_FVar X)) rho (eta_update eta X P) t
   <-> reducible T (P :: rho) eta t).
Proof.
  intros T X P rho eta t Hlc Hfresh.
  unfold open_ty.
  set (etaX := eta_update eta X P).
  assert (HeqP : reducible (Ty_FVar X) rho etaX = P).
  { simpl; unfold etaX, eta_update; rewrite Nat.eqb_refl; reflexivity. }
  transitivity (reducible T (P :: rho) etaX t).
  - change (reducible (open_ty_rec (length (@nil (tm -> Prop)))
      (Ty_FVar X) T) ([] ++ rho) etaX t
      <-> reducible T ([] ++ P :: rho) etaX t).
    rewrite <- HeqP.
    apply reducible_ty_open; [exact Hlc|apply lc_ty_fvar].
  - apply reducible_eta_agree.
    intros Y HY; unfold etaX, eta_update.
    destruct (Nat.eqb X Y) eqn:Heq.
    + apply Nat.eqb_eq in Heq. exfalso; apply Hfresh; rewrite Heq; exact HY.
    + reflexivity.
Qed.

Lemma map_ty_lc : forall T k theta,
  lc_ty_at k T ->
  (forall X, locally_closed_ty (theta X)) ->
  lc_ty_at k (map_ty theta T).
Proof.
  intros T k theta H; induction H; intros Htheta; simpl.
  - apply lc_ty_bvar; assumption.
  - eapply lc_ty_weaken; [apply Htheta|lia].
  - apply lc_ty_arrow; auto.
  - apply lc_ty_all; auto.
  - apply lc_ty_nat.
Qed.

Lemma map_tm_ty_lc : forall t K k theta,
  lc_tm_at K k t ->
  (forall X, locally_closed_ty (theta X)) ->
  lc_tm_at K k (map_tm_ty theta t).
Proof.
  intros t K k theta H; induction H; intros Htheta; simpl.
  - apply lc_tm_bvar; assumption.
  - apply lc_tm_fvar.
  - apply lc_tm_abs; eauto using map_ty_lc.
  - apply lc_tm_app; auto.
  - apply lc_tm_tabs; auto.
  - apply lc_tm_tapp; eauto using map_ty_lc.
  - apply lc_tm_zero.
  - apply lc_tm_succ; auto.
  - apply lc_tm_rec; auto.
Qed.

Lemma map_tm_lc : forall t K k sigma,
  lc_tm_at K k t ->
  (forall x, locally_closed_tm (sigma x)) ->
  lc_tm_at K k (map_tm sigma t).
Proof.
  intros t K k sigma H; induction H; intros Hsigma; simpl.
  - apply lc_tm_bvar; assumption.
  - eapply lc_tm_weaken; [apply Hsigma|lia|lia].
  - apply lc_tm_abs; auto.
  - apply lc_tm_app; auto.
  - apply lc_tm_tabs; auto.
  - apply lc_tm_tapp; auto.
  - apply lc_tm_zero.
  - apply lc_tm_succ; auto.
  - apply lc_tm_rec; auto.
Qed.

Lemma has_type_ty_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_ty T.
Proof.
  intros Delta Gamma t T H; induction H.
  - apply wf_ty_lc with (Delta := Delta); assumption.
  - apply lc_ty_arrow; [apply wf_ty_lc with (Delta := Delta); assumption|
      apply H1 with (x := fresh_atom L); apply fresh_atom_not_in].
  - inversion IHhas_type1; assumption.
  - apply lc_ty_all.
    apply lc_ty_open_inverse with (U := Ty_FVar (fresh_atom L)).
    apply H0 with (X := fresh_atom L); apply fresh_atom_not_in.
  - inversion IHhas_type; subst.
    eapply lc_ty_open_rec; [eassumption|apply wf_ty_lc with (Delta := Delta); assumption].
  - apply lc_ty_nat.
  - apply lc_ty_nat.
  - apply IHhas_type2.
Qed.

Lemma term_atoms_map_tm_ty : forall t theta,
  term_atoms (map_tm_ty theta t) = term_atoms t.
Proof.
  induction t; intros theta; simpl; try reflexivity;
    try (rewrite IHt; reflexivity);
    try (rewrite IHt1, IHt2; reflexivity).
  rewrite IHt1, IHt2, IHt3; reflexivity.
Qed.

Lemma lookup_type_atoms : forall Gamma x T X,
  lookup_context x Gamma = Some T ->
  In X (type_atoms T) -> In X (context_type_atoms Gamma).
Proof.
  induction Gamma as [|[y A] Gamma IH]; intros x T X Hlookup HX; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:Heq.
    + inversion Hlookup; subst. apply in_or_app; auto.
    + apply in_or_app; right; eapply IH; eauto.
Qed.

Definition realizes (Gamma : context) (sigma : atom -> tm)
  (eta : free_type_environment) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    reducible T [] eta (sigma x).

Lemma empty_candidates : forall P, In P ([] : type_environment) -> candidate P.
Proof.
  intros P H; inversion H.
Qed.

Lemma fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall theta sigma eta,
    (forall X, locally_closed_ty (theta X)) ->
    (forall x, locally_closed_tm (sigma x)) ->
    (forall X, candidate (eta X)) ->
    realizes Gamma sigma eta ->
    reducible T [] eta (map_tm sigma (map_tm_ty theta t)).
Proof.
  intros Delta Gamma t T Htyping; induction Htyping;
    intros theta sigma eta Htheta Hsigma Hfree Hreal; simpl.
  - apply Hreal; assumption.
  - apply reducible_abs.
    + change (locally_closed_tm (map_tm sigma
        (map_tm_ty theta (tm_abs T1 t2)))).
      apply map_tm_lc; [apply map_tm_ty_lc|exact Hsigma].
      * eapply has_type_lc. eapply T_Abs; eauto.
      * exact Htheta.
    + intros w Hw Hwv.
      set (x := fresh_atom (L ++ term_atoms t2)).
      assert (HfreshL : ~ In x L).
      { intros Hin; apply (fresh_atom_not_in (L ++ term_atoms t2));
          apply in_or_app; left; exact Hin. }
      assert (HfreshT : ~ In x (term_atoms t2)).
      { intros Hin; apply (fresh_atom_not_in (L ++ term_atoms t2));
          apply in_or_app; right; exact Hin. }
      set (sigma' := fun y => if Nat.eqb x y then w else sigma y).
      assert (Hsigma' : forall y, locally_closed_tm (sigma' y)).
      { intros y; unfold sigma'. destruct (Nat.eqb x y).
        - eapply candidate_lc;
            [apply (reducible_candidate T1 [] eta empty_candidates Hfree)|exact Hw].
        - apply Hsigma. }
      assert (Hreal' : realizes (update Gamma x T1) sigma' eta).
      { intros y A Hlookup; simpl in Hlookup.
        destruct (Nat.eqb y x) eqn:Heq.
        - apply Nat.eqb_eq in Heq; subst y. inversion Hlookup; subst A.
          unfold sigma'; rewrite Nat.eqb_refl; exact Hw.
        - unfold sigma'. rewrite Nat.eqb_sym, Heq. apply Hreal; exact Hlookup. }
      pose proof (H1 x HfreshL theta sigma' eta Htheta Hsigma' Hfree Hreal')
        as Hbody.
      unfold open_tm in Hbody.
      rewrite (map_tm_ty_open t2 theta (tm_fvar x) 0) in Hbody.
      cbn [map_tm_ty] in Hbody.
      rewrite (map_tm_open (map_tm_ty theta t2) sigma' (tm_fvar x) 0
        Hsigma') in Hbody.
      simpl in Hbody.
      assert (Hsame : map_tm sigma' (map_tm_ty theta t2) =
        map_tm sigma (map_tm_ty theta t2)).
      { apply map_tm_agree. rewrite term_atoms_map_tm_ty.
        intros y Hy; unfold sigma'.
        destruct (Nat.eqb x y) eqn:Heq.
        - apply Nat.eqb_eq in Heq; subst y; contradiction.
        - reflexivity. }
      rewrite Hsame in Hbody. unfold sigma' in Hbody.
      rewrite Nat.eqb_refl in Hbody. exact Hbody.
  - eapply reducible_app; eauto using empty_candidates.
  - apply reducible_tabs.
    + change (locally_closed_tm (map_tm sigma
        (map_tm_ty theta (tm_tabs t)))).
      apply map_tm_lc; [apply map_tm_ty_lc|exact Hsigma].
      * eapply has_type_lc. eapply T_TAbs; eauto.
      * exact Htheta.
    + intros U P HU HP.
      set (X := fresh_atom (L ++ term_type_atoms t ++
        type_atoms T ++ context_type_atoms Gamma)).
      assert (Hfresh : ~ In X (L ++ term_type_atoms t ++
        type_atoms T ++ context_type_atoms Gamma)).
      { unfold X; apply fresh_atom_not_in. }
      assert (HfreshL : ~ In X L).
      { intros Hin; apply Hfresh, in_or_app; auto. }
      assert (HfreshTerm : ~ In X (term_type_atoms t)).
      { intros Hin; apply Hfresh, in_or_app; right;
          apply in_or_app; auto. }
      assert (HfreshType : ~ In X (type_atoms T)).
      { intros Hin; apply Hfresh, in_or_app; right;
          apply in_or_app; right; apply in_or_app; auto. }
      assert (HfreshGamma : ~ In X (context_type_atoms Gamma)).
      { intros Hin; apply Hfresh, in_or_app; right;
          apply in_or_app; right; apply in_or_app; auto. }
      set (theta' := fun Y => if Nat.eqb X Y then U else theta Y).
      set (eta' := eta_update eta X P).
      assert (Htheta' : forall Y, locally_closed_ty (theta' Y)).
      { intros Y; unfold theta'; destruct (Nat.eqb X Y); auto. }
      assert (Hfree' : forall Y, candidate (eta' Y)).
      { intros Y; unfold eta', eta_update.
        destruct (Nat.eqb X Y); auto. }
      assert (Hreal' : realizes Gamma sigma eta').
      { intros y A Hlookup.
        assert (HagreeA : forall Y, In Y (type_atoms A) -> eta Y = eta' Y).
        { intros Y HY; unfold eta', eta_update.
          destruct (Nat.eqb X Y) eqn:Heq; [|reflexivity].
          apply Nat.eqb_eq in Heq. exfalso; apply HfreshGamma.
          rewrite Heq. eapply lookup_type_atoms; eauto. }
        apply (proj1 (reducible_eta_agree A [] eta eta' (sigma y) HagreeA)).
        apply Hreal; assumption. }
      pose proof (H0 X HfreshL theta' sigma eta' Htheta' Hsigma Hfree' Hreal')
        as Hbody.
      assert (HlcT : lc_ty_at 1 T).
      { apply lc_ty_open_inverse with (U := Ty_FVar X).
        eapply has_type_ty_lc; apply H; exact HfreshL. }
      assert (Hterm : map_tm sigma
        (map_tm_ty theta' (open_tm_ty t (Ty_FVar X))) =
        open_tm_ty (map_tm sigma (map_tm_ty theta t)) U).
      { unfold open_tm_ty.
        rewrite (map_tm_ty_open_ty t theta' (Ty_FVar X) 0 Htheta').
        cbn [map_ty]. unfold theta' at 1. rewrite Nat.eqb_refl.
        rewrite (map_tm_ty_agree t theta' theta).
        - apply map_tm_open_ty; exact Hsigma.
        - intros Y HY; unfold theta'.
          destruct (Nat.eqb X Y) eqn:Heq; [|reflexivity].
          apply Nat.eqb_eq in Heq. exfalso; apply HfreshTerm.
          rewrite Heq; exact HY. }
      rewrite Hterm in Hbody.
      apply (proj1 (reducible_open_fvar T X P [] eta _ HlcT HfreshType)).
      exact Hbody.
  - assert (HlcT : lc_ty_at 1 T).
    { pose proof (has_type_ty_lc _ _ _ _ Htyping) as Hall.
      inversion Hall; assumption. }
    assert (HlcU : locally_closed_ty U).
    { eapply wf_ty_lc; eassumption. }
    unfold open_ty.
    apply (proj2 (reducible_ty_open T [] [] U eta
      (tm_tapp (map_tm sigma (map_tm_ty theta t)) (map_ty theta U))
      HlcT HlcU)).
    eapply reducible_tapp with (P := reducible U [] eta).
    + apply empty_candidates.
    + exact Hfree.
    + apply map_ty_lc; assumption.
    + apply reducible_candidate; [apply empty_candidates|exact Hfree].
    + apply IHHtyping; assumption.
  - apply (reducible_zero [] eta).
  - apply (reducible_succ [] eta). apply IHHtyping; assumption.
  - eapply reducible_rec with (rho := []) (eta := eta);
      eauto using empty_candidates.
Qed.

Lemma map_ty_identity : forall T,
  map_ty Ty_FVar T = T.
Proof.
  induction T; simpl; f_equal; auto.
Qed.

Lemma map_tm_ty_identity : forall t,
  map_tm_ty Ty_FVar t = t.
Proof.
  induction t; simpl; f_equal; auto using map_ty_identity.
Qed.

Lemma map_tm_identity : forall t,
  map_tm tm_fvar t = t.
Proof.
  induction t; simpl; f_equal; auto.
Qed.

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  intros t T Htyping.
  set (eta := fun _ : atom => saturated (fun _ : tm => True)).
  assert (Hfree : forall X, candidate (eta X)).
  { intros X; apply saturated_candidate. }
  assert (Hred : reducible T [] eta
    (map_tm tm_fvar (map_tm_ty Ty_FVar t))).
  { apply (fundamental [] [] t T Htyping).
    - intros X; apply lc_ty_fvar.
    - intros x; apply lc_tm_fvar.
    - exact Hfree.
    - intros x A Hlookup; discriminate. }
  rewrite map_tm_identity, map_tm_ty_identity in Hred.
  exact (candidate_sn _ (reducible_candidate T [] eta
    empty_candidates Hfree) t Hred).
Qed.

End SystemFNormalizationRecursionHardTask.
