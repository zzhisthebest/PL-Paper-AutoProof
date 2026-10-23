(** System F CBV strong-normalization benchmark, Hard variant.
    Features: nondeterminism-recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFNormalizationNondeterminismRecursionHardTask.

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

(* Construct the logical relation and supporting proofs here. *)

Lemma lc_ty_weaken : forall K K' T,
  K <= K' -> lc_ty_at K T -> lc_ty_at K' T.
Proof.
  intros K K' T Hle Hlc. revert K' Hle.
  induction Hlc; intros K' Hle; eauto using lc_ty_at; try lia.
  - constructor. lia.
  - constructor. apply IHHlc. lia.
Qed.

Lemma lc_tm_weaken : forall K K' k k' t,
  K <= K' -> k <= k' -> lc_tm_at K k t -> lc_tm_at K' k' t.
Proof.
  intros K K' k k' t HK Hk Hlc.
  revert K' k' HK Hk.
  induction Hlc; intros K' k' HK Hk; eauto using lc_tm_at, lc_ty_weaken; try lia.
  - constructor. lia.
  - constructor.
    + eapply lc_ty_weaken; eauto.
    + apply IHHlc; lia.
  - constructor. apply IHHlc; lia.
Qed.

Lemma lc_ty_open_rec : forall K T U,
  lc_ty_at (S K) T -> lc_ty_at K U ->
  lc_ty_at K (open_ty_rec K U T).
Proof.
  intros K T U HT HU. remember (S K) as J eqn:HJ.
  revert K HJ HU. induction HT; intros K0 HJ HU; subst; simpl;
    eauto using lc_ty_at.
  - destruct (Nat.eqb K0 i) eqn:E.
    + apply Nat.eqb_eq in E; subst. exact HU.
    + constructor. apply Nat.eqb_neq in E. lia.
  - constructor. apply IHHT with (K := S K0); auto.
    apply lc_ty_weaken with (K := K0); auto; lia.
Qed.

Lemma lc_tm_open_rec : forall K k t u,
  lc_tm_at K (S k) t -> lc_tm_at K k u ->
  lc_tm_at K k (open_tm_rec k u t).
Proof.
  intros K k t u HT HU. remember (S k) as j eqn:Hj.
  revert k Hj HU. induction HT; intros k0 Hj HU; subst; simpl;
    eauto using lc_tm_at.
  - destruct (Nat.eqb k0 i) eqn:E.
    + apply Nat.eqb_eq in E; subst. exact HU.
    + constructor. apply Nat.eqb_neq in E. lia.
  - constructor; auto. apply IHHT with (k := S k0); auto.
    apply lc_tm_weaken with (K := K) (k := k0); auto; lia.
  - constructor. apply IHHT with (k := k0); auto.
    apply lc_tm_weaken with (K := K) (k := k0); auto; lia.
Qed.

Lemma lc_tm_ty_open_rec : forall K k t U,
  lc_tm_at (S K) k t -> lc_ty_at K U ->
  lc_tm_at K k (open_tm_ty_rec K U t).
Proof.
  intros K k t U HT HU. remember (S K) as J eqn:HJ.
  revert K HJ HU. induction HT; intros K0 HJ HU; subst; simpl;
    eauto using lc_tm_at, lc_ty_open_rec.
  - constructor. apply IHHT with (K := S K0); auto.
    apply lc_ty_weaken with (K := K0); auto; lia.
Qed.

Lemma numeric_value_lc : forall n, numeric_value n -> locally_closed_tm n.
Proof.
  intros n H. induction H; simpl; constructor; auto.
Qed.

Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof.
  intros v H. inversion H; subst; eauto using numeric_value_lc.
Qed.

Lemma step_lc : forall t u, t --> u -> locally_closed_tm t ->
  locally_closed_tm u.
Proof.
  intros t u Hs. induction Hs; intro Hlc; inversion Hlc; subst;
    eauto using lc_tm_at, value_lc.
  - inversion H; subst. eapply lc_tm_open_rec; eauto using value_lc.
  - constructor; eauto. apply IHHs; assumption.
  - constructor; eauto. apply IHHs; assumption.
  - inversion H; subst. eapply lc_tm_ty_open_rec; eauto.
  - constructor; eauto. apply IHHs; assumption.
  - constructor; eauto. apply IHHs; assumption.
  - constructor; eauto. apply IHHs; assumption.
  - constructor; eauto. apply IHHs; assumption.
  - constructor; eauto. apply IHHs; assumption.
  - repeat constructor; eauto using numeric_value_lc, value_lc.
    all: apply numeric_value_lc; assumption.
Qed.

Lemma numeric_no_step : forall n u,
  numeric_value n -> n --> u -> False.
Proof.
  intros n u Hn. revert u. induction Hn; intros u Hs;
    inversion Hs; subst; eauto.
Qed.

Lemma value_no_step : forall v u, value v -> v --> u -> False.
Proof.
  intros v u Hv Hs. inversion Hv; subst; inversion Hs; subst;
    eauto using numeric_no_step.
Qed.

Definition value_pred := tm -> Prop.

Definition red (P : value_pred) (t : tm) : Prop :=
  locally_closed_tm t /\ strongly_normalizing t /\
  forall v, t -->* v -> value v -> P v.

Definition under (P : value_pred) (b : nat -> value_pred) :
  nat -> value_pred :=
  fun i => match i with O => P | S j => b j end.

Fixpoint interp (T : ty) (b : nat -> value_pred)
    (e : atom -> value_pred) : value_pred :=
  match T with
  | Ty_BVar i => b i
  | Ty_FVar X => e X
  | Ty_Arrow T1 T2 =>
      fun v => forall a, red (interp T1 b e) a -> value a ->
        red (interp T2 b e) (tm_app v a)
  | Ty_All T1 =>
      fun v => forall U P, locally_closed_ty U ->
        red (interp T1 (under P b) e) (tm_tapp v U)
  | Ty_Nat => numeric_value
  end.

Definition reducible (T : ty) (b : nat -> value_pred)
    (e : atom -> value_pred) (t : tm) : Prop :=
  red (interp T b e) t.

Lemma red_lc : forall P t, red P t -> locally_closed_tm t.
Proof. intros P t [H _]. exact H. Qed.

Lemma red_sn : forall P t, red P t -> strongly_normalizing t.
Proof. intros P t [_ [H _]]. exact H. Qed.

Lemma red_value : forall P v, red P v -> value v -> P v.
Proof.
  intros P v [_ [_ H]] Hv. apply H with (v := v); auto.
  constructor.
Qed.

Lemma red_step : forall P t u, red P t -> t --> u -> red P u.
Proof.
  intros P t u [Hlc [Hsn Hval]] Hstep.
  split; [eauto using step_lc|].
  split.
  - inversion Hsn; subst. eauto.
  - intros v Hmulti Hv. apply Hval with (v := v); auto.
    econstructor; eauto.
Qed.

Lemma red_intro : forall P t,
  locally_closed_tm t ->
  (value t -> P t) ->
  (forall u, t --> u -> red P u) -> red P t.
Proof.
  intros P t Hlc Hval Hstep. split; [exact Hlc|]. split.
  - constructor. intros u Hu. exact (red_sn _ _ (Hstep u Hu)).
  - intros v Hmulti Hv. inversion Hmulti; subst.
    + apply Hval; assumption.
    + destruct (Hstep y H) as [_ [_ HH]].
      eapply HH; eauto.
Qed.

Lemma red_of_value : forall P v,
  value v -> P v -> red P v.
Proof.
  intros P v Hv HP. apply red_intro; eauto using value_lc.
  intros u Hu. exfalso. eapply value_no_step; eauto.
Qed.

Lemma red_app : forall A B b e f a,
  red (interp (Ty_Arrow A B) b e) f ->
  red (interp A b e) a ->
  red (interp B b e) (tm_app f a).
Proof.
  intros A B b e f a Rf Ra.
  pose proof (red_sn _ _ Rf) as Hf.
  revert a Rf Ra. induction Hf as [f Hf IHf]; intros a Rf Ra.
  pose proof (red_sn _ _ Ra) as Ha.
  revert Ra. induction Ha as [a Ha IHa]; intros Ra.
  apply red_intro.
  - constructor; [exact (red_lc _ _ Rf)|exact (red_lc _ _ Ra)].
  - intro Hv. inversion Hv; subst; inversion H.
  - intros u Hu. inversion Hu; subst.
    + pose proof (red_value _ _ Rf (v_abs _ _ H1)) as Hfun.
      pose proof (Hfun a Ra H3) as Happ.
      eapply red_step; eauto.
    + apply IHf; eauto using red_step.
    + apply IHa; eauto using red_step.
Qed.

Lemma red_tapp : forall T b e f U P,
  red (interp (Ty_All T) b e) f ->
  locally_closed_ty U ->
  red (interp T (under P b) e) (tm_tapp f U).
Proof.
  intros T b e f U P Rf HU.
  pose proof (red_sn _ _ Rf) as Hsn.
  induction Hsn as [f Hf IHf].
  apply red_intro.
  - constructor; [exact (red_lc _ _ Rf)|exact HU].
  - intro Hv. inversion Hv; subst; inversion H.
  - intros u Hstep. inversion Hstep; subst.
    + pose proof (red_value _ _ Rf (v_tabs _ H1)) as Hpoly.
      pose proof (Hpoly U P HU) as Happ.
      eapply red_step; eauto.
    + apply IHf; eauto using red_step.
Qed.

Lemma red_succ : forall b e n,
  red (interp Ty_Nat b e) n ->
  red (interp Ty_Nat b e) (tm_succ n).
Proof.
  intros b e n Rn. pose proof (red_sn _ _ Rn) as Hsn.
  induction Hsn as [n Hn IHn].
  apply red_intro.
  - constructor. exact (red_lc _ _ Rn).
  - intro Hv. inversion Hv; subst. inversion H; subst.
    constructor. eapply red_value; eauto.
  - intros u Hu. inversion Hu; subst. apply IHn; eauto using red_step.
Qed.

Lemma red_choice : forall P t1 t2,
  red P t1 -> red P t2 -> red P (tm_choice t1 t2).
Proof.
  intros P t1 t2 R1 R2. apply red_intro.
  - constructor; [exact (red_lc _ _ R1)|exact (red_lc _ _ R2)].
  - intro Hv. inversion Hv; subst; inversion H.
  - intros u Hu. inversion Hu; subst; assumption.
Qed.

Lemma red_rec_values : forall T b_env e n b s,
  numeric_value n ->
  value b -> value s ->
  red (interp T b_env e) b ->
  red (interp (Ty_Arrow Ty_Nat (Ty_Arrow T T)) b_env e) s ->
  red (interp T b_env e) (tm_natrec n b s).
Proof.
  intros T b_env e n b s Hn.
  induction Hn; intros Hb Hs Rb Rs.
  - apply red_intro.
    + constructor; [constructor|exact (red_lc _ _ Rb)|exact (red_lc _ _ Rs)].
    + intro Hv. inversion Hv; subst; inversion H.
    + intros u Hu. inversion Hu; subst; eauto.
      * exfalso. eapply (numeric_no_step tm_zero n'); eauto. constructor.
      * exfalso. eapply (value_no_step b b'); eauto.
      * exfalso. eapply (value_no_step s s'); eauto.
  - apply red_intro.
    + constructor; [constructor; exact (numeric_value_lc _ Hn)|exact (red_lc _ _ Rb)|exact (red_lc _ _ Rs)].
    + intro Hv. inversion Hv; subst; inversion H.
    + intros u Hu. inversion Hu; subst; eauto.
      * exfalso. eapply (numeric_no_step (tm_succ n) n'); eauto.
        constructor; assumption.
      * exfalso. eapply (value_no_step b b'); eauto.
      * exfalso. eapply (value_no_step s s'); eauto.
      * eapply red_app.
        -- eapply red_app; eauto.
           apply red_of_value; [constructor; exact Hn|exact Hn].
        -- apply IHHn; assumption.
Qed.

Lemma red_rec_value_n : forall T b_env e n b s,
  numeric_value n ->
  red (interp T b_env e) b ->
  red (interp (Ty_Arrow Ty_Nat (Ty_Arrow T T)) b_env e) s ->
  red (interp T b_env e) (tm_natrec n b s).
Proof.
  intros T b_env e n b s Hn Rb Rs.
  pose proof (red_sn _ _ Rb) as Hbsn.
  revert s Rb Rs. induction Hbsn as [b Hbstep IHb]; intros s Rb Rs.
  pose proof (red_sn _ _ Rs) as Hssn.
  revert Rs. induction Hssn as [s Hsstep IHs]; intro Rs.
  apply red_intro.
  - constructor; [exact (numeric_value_lc _ Hn)|exact (red_lc _ _ Rb)|exact (red_lc _ _ Rs)].
  - intro Hv. inversion Hv; subst; inversion H.
  - intros u Hu. inversion Hu; subst.
    + exfalso. eapply numeric_no_step; eauto.
    + apply IHb; eauto using red_step.
    + apply IHs; eauto using red_step.
    + exact Rb.
    + eapply red_step; [|exact Hu]. eapply red_rec_values; eauto.
Qed.

Lemma red_rec : forall T b_env e n b s,
  red (interp Ty_Nat b_env e) n ->
  red (interp T b_env e) b ->
  red (interp (Ty_Arrow Ty_Nat (Ty_Arrow T T)) b_env e) s ->
  red (interp T b_env e) (tm_natrec n b s).
Proof.
  intros T b_env e n b s Rn Rb Rs.
  pose proof (red_sn _ _ Rn) as Hnsn.
  revert b s Rn Rb Rs. induction Hnsn as [n Hnstep IHn];
    intros b s Rn Rb Rs.
  apply red_intro.
  - constructor; [exact (red_lc _ _ Rn)|exact (red_lc _ _ Rb)|exact (red_lc _ _ Rs)].
  - intro Hv. inversion Hv; subst; inversion H.
  - intros u Hu. inversion Hu; subst.
    + apply IHn; eauto using red_step.
    + eapply red_step; [|exact Hu]. eapply red_rec_value_n; eauto.
    + eapply red_step; [|exact Hu]. eapply red_rec_value_n; eauto.
    + eapply red_step; [|exact Hu]. eapply red_rec_value_n; eauto.
      constructor.
    + eapply red_step; [|exact Hu]. eapply red_rec_value_n; eauto.
      constructor; assumption.
Qed.

Lemma lc_ty_unopen_rec : forall K T X,
  lc_ty_at K (open_ty_rec K (Ty_FVar X) T) ->
  lc_ty_at (S K) T.
Proof.
  intros K T X. revert K. induction T; intros K H; simpl in H;
    eauto using lc_ty_at.
  - destruct (Nat.eqb K n) eqn:E.
    + apply Nat.eqb_eq in E; subst. constructor. lia.
    + inversion H; subst. constructor. lia.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor. apply IHT with (K := S K); auto.
Qed.

Lemma lc_tm_unopen_rec : forall K k t x,
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) ->
  lc_tm_at K (S k) t.
Proof.
  intros K k t x. revert K k. induction t; intros K k H; simpl in H;
    eauto using lc_tm_at.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst. constructor. lia.
    + inversion H; subst. constructor. lia.
  - inversion H; subst. constructor; auto.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
Qed.

Lemma lc_tm_ty_unopen_rec : forall K k t X,
  lc_tm_at K k (open_tm_ty_rec K (Ty_FVar X) t) ->
  lc_tm_at (S K) k t.
Proof.
  intros K k t X. revert K k. induction t; intros K k H; simpl in H;
    eauto using lc_tm_at.
  - constructor. inversion H; lia.
  - inversion H; subst. constructor.
    + eapply lc_ty_unopen_rec; eauto.
    + eapply IHt; eauto.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor. apply IHt with (K := S K); auto.
  - inversion H; subst. constructor.
    + eapply IHt; eauto.
    + eapply lc_ty_unopen_rec; eauto.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor; eauto.
Qed.

Lemma in_fold_max : forall (L : list atom) (x : atom),
  In x L -> x <= fold_right Nat.max 0 L.
Proof.
  induction L as [|a L IH]; intros x H; simpl in *.
  - contradiction.
  - destruct H as [E|H]; subst; [lia|]. specialize (IH x H). lia.
Qed.

Lemma fresh_atom : forall (L : list atom), exists x, ~ In x L.
Proof.
  intro L. exists (S (fold_right Nat.max 0 L)).
  intro H. pose proof (in_fold_max L _ H). lia.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T Hwf. induction Hwf.
  - constructor.
  - constructor; assumption.
  - destruct (fresh_atom L) as [X HX].
    constructor. eapply lc_ty_unopen_rec.
    apply H0. exact HX.
  - constructor.
Qed.

Lemma has_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T Hty. induction Hty.
  - constructor.
  - destruct (fresh_atom L) as [x Hx].
    constructor; [exact (wf_ty_lc _ _ H)|].
    eapply lc_tm_unopen_rec. apply H1. exact Hx.
  - constructor; assumption.
  - destruct (fresh_atom L) as [X HX].
    constructor. eapply lc_tm_ty_unopen_rec.
    apply H0. exact HX.
  - constructor; [exact IHHty|exact (wf_ty_lc _ _ H)].
  - constructor.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
Qed.

Fixpoint inst_ty (tau : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => tau X
  | Ty_Arrow A B => Ty_Arrow (inst_ty tau A) (inst_ty tau B)
  | Ty_All A => Ty_All (inst_ty tau A)
  | Ty_Nat => Ty_Nat
  end.

Fixpoint inst_tm (tau : atom -> ty) (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_abs T t => tm_abs (inst_ty tau T) (inst_tm tau sigma t)
  | tm_app t u => tm_app (inst_tm tau sigma t) (inst_tm tau sigma u)
  | tm_tabs t => tm_tabs (inst_tm tau sigma t)
  | tm_tapp t T => tm_tapp (inst_tm tau sigma t) (inst_ty tau T)
  | tm_zero => tm_zero
  | tm_succ t => tm_succ (inst_tm tau sigma t)
  | tm_natrec n b s => tm_natrec (inst_tm tau sigma n)
      (inst_tm tau sigma b) (inst_tm tau sigma s)
  | tm_choice t u => tm_choice (inst_tm tau sigma t) (inst_tm tau sigma u)
  end.

Definition tau_closed (tau : atom -> ty) : Prop :=
  forall X, locally_closed_ty (tau X).
Definition sigma_closed (sigma : atom -> tm) : Prop :=
  forall x, locally_closed_tm (sigma x).

Lemma inst_ty_lc : forall tau K T,
  tau_closed tau -> lc_ty_at K T -> lc_ty_at K (inst_ty tau T).
Proof.
  intros tau K T Htau Hlc. induction Hlc; simpl;
    eauto using lc_ty_at.
  - eapply lc_ty_weaken with (K := 0); [lia|apply Htau].
Qed.

Lemma inst_tm_lc : forall tau sigma K k t,
  tau_closed tau -> sigma_closed sigma ->
  lc_tm_at K k t -> lc_tm_at K k (inst_tm tau sigma t).
Proof.
  intros tau sigma K k t Htau Hsigma Hlc.
  induction Hlc; simpl; eauto using lc_tm_at, inst_ty_lc.
  - eapply lc_tm_weaken with (K := 0) (k := 0);
      [lia|lia|apply Hsigma].
Qed.

Lemma open_ty_rec_id : forall K T k U,
  lc_ty_at K T -> K <= k -> open_ty_rec k U T = T.
Proof.
  intros K T k U Hlc. revert k.
  induction Hlc; intros j Hj; simpl; f_equal; eauto; try lia.
  - destruct (Nat.eqb j i) eqn:E; auto.
    apply Nat.eqb_eq in E. lia.
  - apply IHHlc. lia.
Qed.

Lemma open_tm_rec_id : forall K j t k u,
  lc_tm_at K j t -> j <= k -> open_tm_rec k u t = t.
Proof.
  intros K j t k u Hlc. revert k.
  induction Hlc; intros m Hm; simpl; f_equal; eauto; try lia.
  - destruct (Nat.eqb m i) eqn:E; auto.
    apply Nat.eqb_eq in E. lia.
  - apply IHHlc. lia.
Qed.

Lemma open_tm_ty_rec_id : forall K j t k U,
  lc_tm_at K j t -> K <= k -> open_tm_ty_rec k U t = t.
Proof.
  intros K j t k U Hlc. revert k.
  induction Hlc; intros m Hm; simpl; f_equal; eauto; try lia.
  - eapply open_ty_rec_id; eauto.
  - apply IHHlc. lia.
  - eapply open_ty_rec_id; eauto.
Qed.

Fixpoint ftv_ty (T : ty) : list atom :=
  match T with
  | Ty_FVar X => [X]
  | Ty_Arrow A B => ftv_ty A ++ ftv_ty B
  | Ty_All A => ftv_ty A
  | _ => []
  end.

Fixpoint fv_tm (t : tm) : list atom :=
  match t with
  | tm_fvar x => [x]
  | tm_abs _ t | tm_tabs t | tm_succ t => fv_tm t
  | tm_app t u | tm_choice t u => fv_tm t ++ fv_tm u
  | tm_tapp t _ => fv_tm t
  | tm_natrec n b s => fv_tm n ++ fv_tm b ++ fv_tm s
  | _ => []
  end.

Fixpoint ftv_tm (t : tm) : list atom :=
  match t with
  | tm_abs T t => ftv_ty T ++ ftv_tm t
  | tm_app t u | tm_choice t u => ftv_tm t ++ ftv_tm u
  | tm_tabs t | tm_succ t => ftv_tm t
  | tm_tapp t T => ftv_tm t ++ ftv_ty T
  | tm_natrec n b s => ftv_tm n ++ ftv_tm b ++ ftv_tm s
  | _ => []
  end.

Definition set_at {A} (f : atom -> A) (x : atom) (a : A) : atom -> A :=
  fun y => if Nat.eqb x y then a else f y.

Lemma inst_ty_open_var : forall T tau X U k,
  ~ In X (ftv_ty T) -> tau_closed tau ->
  inst_ty (set_at tau X U) (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k U (inst_ty tau T).
Proof.
  induction T; intros tau X U k Hfresh Htau; simpl in *; auto.
  - destruct (Nat.eqb k n); simpl; auto.
    unfold set_at. rewrite Nat.eqb_refl. reflexivity.
  - assert (X <> a) by (intro E; subst; apply Hfresh; simpl; auto).
    unfold set_at. assert ((X =? a) = false) as E
      by (apply Nat.eqb_neq; assumption). rewrite E.
    symmetry. apply open_ty_rec_id with (K := 0); auto.
    apply Htau. lia.
  - f_equal; [apply IHT1|apply IHT2]; auto;
      rewrite in_app_iff in Hfresh; tauto.
  - f_equal. apply IHT; auto.
Qed.

Lemma inst_tm_open_var : forall t tau sigma x v k,
  ~ In x (fv_tm t) -> sigma_closed sigma ->
  inst_tm tau (set_at sigma x v) (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k v (inst_tm tau sigma t).
Proof.
  induction t; intros tau sigma x v k Hfresh Hsigma; simpl in *; auto.
  - destruct (Nat.eqb k n); simpl; auto.
    unfold set_at. rewrite Nat.eqb_refl. reflexivity.
  - assert (x <> a) by (intro E; subst; apply Hfresh; simpl; auto).
    unfold set_at. assert ((x =? a) = false) as E
      by (apply Nat.eqb_neq; assumption). rewrite E.
    symmetry. apply open_tm_rec_id with (K := 0) (j := 0); auto.
    apply Hsigma. lia.
  - f_equal. apply IHt; auto.
  - f_equal; [apply IHt1|apply IHt2]; auto;
      rewrite in_app_iff in Hfresh; tauto.
  - f_equal. apply IHt; auto.
  - f_equal. apply IHt; auto.
  - f_equal. apply IHt; auto.
  - f_equal; [apply IHt1|apply IHt2|apply IHt3]; auto;
      repeat rewrite in_app_iff in Hfresh; tauto.
  - f_equal; [apply IHt1|apply IHt2]; auto;
      rewrite in_app_iff in Hfresh; tauto.
Qed.

Lemma inst_tm_ty_open_var : forall t tau sigma X U k,
  ~ In X (ftv_tm t) -> tau_closed tau -> sigma_closed sigma ->
  inst_tm (set_at tau X U) sigma (open_tm_ty_rec k (Ty_FVar X) t) =
  open_tm_ty_rec k U (inst_tm tau sigma t).
Proof.
  induction t; intros tau sigma X U k Hfresh Htau Hsigma;
    simpl in *; auto.
  - symmetry. apply open_tm_ty_rec_id with (K := 0) (j := 0); auto.
    apply Hsigma. lia.
  - f_equal.
    + apply inst_ty_open_var; auto.
      rewrite in_app_iff in Hfresh; tauto.
    + apply IHt; auto. rewrite in_app_iff in Hfresh; tauto.
  - f_equal; [apply IHt1|apply IHt2]; auto;
      rewrite in_app_iff in Hfresh; tauto.
  - f_equal. apply IHt; auto.
  - f_equal.
    + apply IHt; auto. rewrite in_app_iff in Hfresh; tauto.
    + apply inst_ty_open_var; auto.
      rewrite in_app_iff in Hfresh; tauto.
  - f_equal. apply IHt; auto.
  - f_equal; [apply IHt1|apply IHt2|apply IHt3]; auto;
      repeat rewrite in_app_iff in Hfresh; tauto.
  - f_equal; [apply IHt1|apply IHt2]; auto;
      rewrite in_app_iff in Hfresh; tauto.
Qed.

Definition peq (P Q : value_pred) : Prop :=
  forall v, P v <-> Q v.

Lemma peq_refl : forall P, peq P P.
Proof. firstorder. Qed.

Lemma peq_sym : forall P Q, peq P Q -> peq Q P.
Proof. firstorder. Qed.

Lemma peq_trans : forall P Q R, peq P Q -> peq Q R -> peq P R.
Proof. firstorder. Qed.

Lemma red_peq : forall P Q, peq P Q -> forall t,
  red P t <-> red Q t.
Proof.
  intros P Q H t. unfold red. split.
  - intros [Hlc [Hsn Hv]]. split; [exact Hlc|].
    split; [exact Hsn|]. intros v Hm Hval.
    apply (proj1 (H v)). exact (Hv v Hm Hval).
  - intros [Hlc [Hsn Hv]]. split; [exact Hlc|].
    split; [exact Hsn|]. intros v Hm Hval.
    apply (proj2 (H v)). exact (Hv v Hm Hval).
Qed.

Lemma interp_ext : forall T b1 b2 e1 e2,
  (forall i, peq (b1 i) (b2 i)) ->
  (forall X, peq (e1 X) (e2 X)) ->
  peq (interp T b1 e1) (interp T b2 e2).
Proof.
  induction T; intros b1 b2 e1 e2 Hb He; simpl; auto.
  - intros v. split; intros H a Ra Ha.
    + apply (proj1 (red_peq _ _ (IHT2 _ _ _ _ Hb He) _)).
      apply H; auto. apply (proj2 (red_peq _ _ (IHT1 _ _ _ _ Hb He) _)); exact Ra.
    + apply (proj2 (red_peq _ _ (IHT2 _ _ _ _ Hb He) _)).
      apply H; auto. apply (proj1 (red_peq _ _ (IHT1 _ _ _ _ Hb He) _)); exact Ra.
  - intros v. split; intros H U P HU.
    + apply (proj1 (red_peq _ _ (IHT (under P b1) (under P b2) e1 e2
        (fun i => match i with O => peq_refl _ | S j => Hb j end) He) _)).
      apply H; assumption.
    + apply (proj2 (red_peq _ _ (IHT (under P b1) (under P b2) e1 e2
        (fun i => match i with O => peq_refl _ | S j => Hb j end) He) _)).
      apply H; assumption.
  - apply peq_refl.
Qed.

Lemma interp_support : forall K T b1 b2 e,
  lc_ty_at K T ->
  (forall i, i < K -> peq (b1 i) (b2 i)) ->
  peq (interp T b1 e) (interp T b2 e).
Proof.
  intros K T b1 b2 e Hlc. revert b1 b2.
  induction Hlc; intros b1 b2 Hb; simpl; auto using peq_refl.
  - intros v. split; intros H a Ra Ha.
    + apply (proj1 (red_peq _ _ (IHHlc2 _ _ Hb) _)).
      apply H; auto. apply (proj2 (red_peq _ _ (IHHlc1 _ _ Hb) _)); exact Ra.
    + apply (proj2 (red_peq _ _ (IHHlc2 _ _ Hb) _)).
      apply H; auto. apply (proj1 (red_peq _ _ (IHHlc1 _ _ Hb) _)); exact Ra.
  - intros v. split; intros H U P HU;
      assert (Hunder : forall i, i < S k ->
        peq (under P b1 i) (under P b2 i))
        by (intros [|i] Hi; simpl; [apply peq_refl|apply Hb; lia]).
    + apply (proj1 (red_peq _ _ (IHHlc _ _ Hunder) _)).
      apply H; assumption.
    + apply (proj2 (red_peq _ _ (IHHlc _ _ Hunder) _)).
      apply H; assumption.
Qed.

Definition replace_b (k : nat) (P : value_pred)
    (b : nat -> value_pred) : nat -> value_pred :=
  fun i => if Nat.eqb k i then P else b i.

Lemma interp_open_rec : forall T k U b e,
  locally_closed_ty U ->
  peq (interp (open_ty_rec k U T) b e)
      (interp T (replace_b k (interp U b e) b) e).
Proof.
  induction T; intros k U b e HU; simpl.
  - unfold replace_b. destruct (Nat.eqb k n); apply peq_refl.
  - apply peq_refl.
  - intros v. split; intros H a Ra Ha.
    + apply (proj1 (red_peq _ _ (IHT2 _ _ _ _ HU) _)).
      apply H; auto.
      apply (proj2 (red_peq _ _ (IHT1 _ _ _ _ HU) _)); exact Ra.
    + apply (proj2 (red_peq _ _ (IHT2 _ _ _ _ HU) _)).
      apply H; auto.
      apply (proj1 (red_peq _ _ (IHT1 _ _ _ _ HU) _)); exact Ra.
  - intros v. split; intros H V Q HV.
    + assert (Henv : forall i,
          peq (replace_b (S k) (interp U (under Q b) e) (under Q b) i)
              (under Q (replace_b k (interp U b e) b) i)).
      { intros [|i]; simpl; [apply peq_refl|].
        unfold replace_b. simpl.
        destruct (Nat.eqb k i); [|apply peq_refl].
        eapply interp_support; [exact HU|]. intros j Hj. lia. }
      pose proof (peq_trans _ _ _ (IHT _ _ _ _ HU)
        (interp_ext T _ _ e e Henv (fun _ => peq_refl _))) as Heq.
      apply (proj1 (red_peq _ _ Heq _)). apply H; assumption.
    + assert (Henv : forall i,
          peq (replace_b (S k) (interp U (under Q b) e) (under Q b) i)
              (under Q (replace_b k (interp U b e) b) i)).
      { intros [|i]; simpl; [apply peq_refl|].
        unfold replace_b. simpl.
        destruct (Nat.eqb k i); [|apply peq_refl].
        eapply interp_support; [exact HU|]. intros j Hj. lia. }
      pose proof (peq_trans _ _ _ (IHT _ _ _ _ HU)
        (interp_ext T _ _ e e Henv (fun _ => peq_refl _))) as Heq.
      apply (proj2 (red_peq _ _ Heq _)). apply H; assumption.
  - apply peq_refl.
Qed.

Lemma interp_open_var_rec : forall T k X P b e,
  ~ In X (ftv_ty T) ->
  peq (interp (open_ty_rec k (Ty_FVar X) T) b (set_at e X P))
      (interp T (replace_b k P b) e).
Proof.
  induction T; intros k X P b e Hfresh; simpl in *.
  - unfold replace_b. destruct (Nat.eqb k n); simpl.
    + unfold set_at. rewrite Nat.eqb_refl. apply peq_refl.
    + apply peq_refl.
  - assert (X <> a) by (intro E; subst; apply Hfresh; simpl; auto).
    unfold set_at. assert ((X =? a) = false) as E
      by (apply Nat.eqb_neq; assumption). rewrite E.
    apply peq_refl.
  - intros v. split; intros H a Ra Ha.
    + apply (proj1 (red_peq _ _ (IHT2 _ _ _ _ _
        (fun Hin => Hfresh (in_or_app _ _ _ (or_intror Hin)))) _)).
      apply H; auto.
      apply (proj2 (red_peq _ _ (IHT1 _ _ _ _ _
        (fun Hin => Hfresh (in_or_app _ _ _ (or_introl Hin)))) _)); exact Ra.
    + apply (proj2 (red_peq _ _ (IHT2 _ _ _ _ _
        (fun Hin => Hfresh (in_or_app _ _ _ (or_intror Hin)))) _)).
      apply H; auto.
      apply (proj1 (red_peq _ _ (IHT1 _ _ _ _ _
        (fun Hin => Hfresh (in_or_app _ _ _ (or_introl Hin)))) _)); exact Ra.
  - intros v. split; intros H U Q HU;
      assert (Henv : forall i,
        peq (replace_b (S k) P (under Q b) i)
            (under Q (replace_b k P b) i))
        by (intros [|i]; simpl; unfold replace_b; simpl; apply peq_refl);
      pose proof (peq_trans _ _ _ (IHT _ _ _ _ _ Hfresh)
        (interp_ext T _ _ e e Henv (fun _ => peq_refl _))) as Heq.
    + apply (proj1 (red_peq _ _ Heq _)). apply H; assumption.
    + apply (proj2 (red_peq _ _ Heq _)). apply H; assumption.
  - apply peq_refl.
Qed.

Definition empty_b : nat -> value_pred := fun _ _ => False.

Lemma interp_open_root : forall T U e,
  locally_closed_ty U ->
  peq (interp (open_ty T U) empty_b e)
      (interp T (under (interp U empty_b e) empty_b) e).
Proof.
  intros T U e HU. unfold open_ty.
  eapply peq_trans.
  - apply interp_open_rec. exact HU.
  - apply interp_ext; [|intro; apply peq_refl].
    intros [|i]; unfold replace_b, empty_b, under; simpl;
      apply peq_refl.
Qed.

Lemma interp_open_var_root : forall T X P e,
  ~ In X (ftv_ty T) ->
  peq (interp (open_ty T (Ty_FVar X)) empty_b (set_at e X P))
      (interp T (under P empty_b) e).
Proof.
  intros T X P e Hfresh. unfold open_ty.
  eapply peq_trans.
  - apply interp_open_var_rec. exact Hfresh.
  - apply interp_ext; [|intro; apply peq_refl].
    intros [|i]; unfold replace_b, empty_b, under; simpl;
      apply peq_refl.
Qed.

Lemma interp_ftv : forall T b e1 e2,
  (forall X, In X (ftv_ty T) -> peq (e1 X) (e2 X)) ->
  peq (interp T b e1) (interp T b e2).
Proof.
  induction T; intros b e1 e2 He; simpl in *.
  - apply peq_refl.
  - apply He. simpl; auto.
  - intros v. split; intros H a Ra Ha.
    + assert (H1 : peq (interp T1 b e1) (interp T1 b e2)).
      { apply IHT1. intros X HX. apply He. apply in_or_app. left; exact HX. }
      assert (H2 : peq (interp T2 b e1) (interp T2 b e2)).
      { apply IHT2. intros X HX. apply He. apply in_or_app. right; exact HX. }
      apply (proj1 (red_peq _ _ H2 _)).
      apply H; auto. apply (proj2 (red_peq _ _ H1 _)); exact Ra.
    + assert (H1 : peq (interp T1 b e1) (interp T1 b e2)).
      { apply IHT1. intros X HX. apply He. apply in_or_app. left; exact HX. }
      assert (H2 : peq (interp T2 b e1) (interp T2 b e2)).
      { apply IHT2. intros X HX. apply He. apply in_or_app. right; exact HX. }
      apply (proj2 (red_peq _ _ H2 _)).
      apply H; auto. apply (proj1 (red_peq _ _ H1 _)); exact Ra.
  - intros v. split; intros H U P HU.
    + apply (proj1 (red_peq _ _ (IHT _ _ _ He) _)).
      apply H; assumption.
    + apply (proj2 (red_peq _ _ (IHT _ _ _ He) _)).
      apply H; assumption.
  - apply peq_refl.
Qed.

Lemma interp_avoid : forall T b e X P,
  ~ In X (ftv_ty T) ->
  peq (interp T b e) (interp T b (set_at e X P)).
Proof.
  intros T b e X P Hfresh. apply interp_ftv.
  intros Y HY. unfold set_at.
  assert (X <> Y) by (intro E; subst; contradiction).
  assert ((X =? Y) = false) as E by (apply Nat.eqb_neq; assumption).
  rewrite E. apply peq_refl.
Qed.

Fixpoint ftv_context (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (_, T) :: rest => ftv_ty T ++ ftv_context rest
  end.

Lemma lookup_ftv : forall Gamma x T X,
  lookup_context x Gamma = Some T ->
  In X (ftv_ty T) -> In X (ftv_context Gamma).
Proof.
  induction Gamma as [|[y U] Gamma IH]; intros x T X Hlook HIn;
    simpl in *; try discriminate.
  destruct (Nat.eqb x y) eqn:E.
  - inversion Hlook; subst. apply in_or_app. left; assumption.
  - apply in_or_app. right. eapply IH; eauto.
Qed.

Lemma red_beta : forall P T t v,
  locally_closed_tm (tm_abs T t) -> value v ->
  red P (open_tm t v) -> red P (tm_app (tm_abs T t) v).
Proof.
  intros P T t v Habs Hv Rbody. apply red_intro.
  - constructor; [exact Habs|exact (value_lc _ Hv)].
  - intro Hval. inversion Hval; subst; inversion H.
  - intros u Hu. inversion Hu; subst.
    + exact Rbody.
    + exfalso. eapply (value_no_step (tm_abs T t));
        [constructor; exact Habs|eassumption].
    + exfalso. eapply (value_no_step v); [exact Hv|eassumption].
Qed.

Lemma red_tbeta : forall P t U,
  locally_closed_tm (tm_tabs t) -> locally_closed_ty U ->
  red P (open_tm_ty t U) -> red P (tm_tapp (tm_tabs t) U).
Proof.
  intros P t U Htabs HU Rbody. apply red_intro.
  - constructor; assumption.
  - intro Hval. inversion Hval; subst; inversion H.
  - intros u Hstep. inversion Hstep; subst; eauto.
    exfalso. eapply value_no_step; [constructor; exact Htabs|eassumption].
Qed.

Definition env_sat (Gamma : context) (e : atom -> value_pred)
    (sigma : atom -> tm) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    red (interp T empty_b e) (sigma x).

Lemma tau_closed_set : forall tau X U,
  tau_closed tau -> locally_closed_ty U ->
  tau_closed (set_at tau X U).
Proof.
  intros tau X U Htau HU Y. unfold set_at.
  destruct (Nat.eqb X Y); auto.
Qed.

Lemma sigma_closed_set : forall sigma x v,
  sigma_closed sigma -> locally_closed_tm v ->
  sigma_closed (set_at sigma x v).
Proof.
  intros sigma x v Hsigma Hv y. unfold set_at.
  destruct (Nat.eqb x y); auto.
Qed.

Lemma env_sat_set : forall Gamma e sigma x T v,
  env_sat Gamma e sigma -> red (interp T empty_b e) v ->
  env_sat (update Gamma x T) e (set_at sigma x v).
Proof.
  intros Gamma e sigma x T v Henv Rv y V Hlook.
  unfold update in Hlook. simpl in Hlook.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E; subst. inversion Hlook; subst.
    unfold set_at. rewrite Nat.eqb_refl. exact Rv.
  - assert ((x =? y) = false) as E' by
      (apply Nat.eqb_neq; apply Nat.eqb_neq in E; lia).
    unfold set_at. rewrite E'. eapply Henv; eauto.
Qed.

Lemma env_sat_ty_set : forall Gamma e sigma X P,
  env_sat Gamma e sigma -> ~ In X (ftv_context Gamma) ->
  env_sat Gamma (set_at e X P) sigma.
Proof.
  intros Gamma e sigma X P Henv Hfresh y T Hlook.
  apply (proj1 (red_peq _ _
    (interp_avoid T empty_b e X P
      (fun Hin => Hfresh (lookup_ftv _ _ _ _ Hlook Hin))) _)).
  eapply Henv; eauto.
Qed.

Theorem fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall tau sigma e,
  tau_closed tau -> sigma_closed sigma -> env_sat Gamma e sigma ->
  red (interp T empty_b e) (inst_tm tau sigma t).
Proof.
  intros Delta Gamma t T Hty. induction Hty;
    intros tau sigma e Htau Hsigma Henv; simpl.
  - eapply Henv; eauto.
  - destruct (fresh_atom (L ++ fv_tm t2)) as [x Hfresh].
    assert (HxL : ~ In x L) by
      (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (Hxt : ~ In x (fv_tm t2)) by
      (intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
    apply red_of_value.
    + apply v_abs.
      change (locally_closed_tm (inst_tm tau sigma (tm_abs T1 t2))).
      eapply inst_tm_lc; eauto.
      eapply has_type_lc. econstructor; eauto.
    + intros a Ra Hva. eapply red_beta.
      * change (locally_closed_tm (inst_tm tau sigma (tm_abs T1 t2))).
        eapply inst_tm_lc; eauto.
        eapply has_type_lc. econstructor; eauto.
      * exact Hva.
      * unfold open_tm. rewrite <- (inst_tm_open_var t2 tau sigma x a 0 Hxt Hsigma).
        apply (H1 x HxL tau (set_at sigma x a) e).
        -- exact Htau.
        -- apply sigma_closed_set; [exact Hsigma|exact (value_lc _ Hva)].
        -- apply env_sat_set; assumption.
  - eapply red_app; eauto.
  - destruct (fresh_atom
      (L ++ ftv_tm t ++ ftv_ty T ++ ftv_context Gamma)) as [X Hfresh].
    assert (HXL : ~ In X L) by
      (intro Hin; apply Hfresh; repeat rewrite in_app_iff; tauto).
    assert (HXt : ~ In X (ftv_tm t)) by
      (intro Hin; apply Hfresh; repeat rewrite in_app_iff; tauto).
    assert (HXT : ~ In X (ftv_ty T)) by
      (intro Hin; apply Hfresh; repeat rewrite in_app_iff; tauto).
    assert (HXG : ~ In X (ftv_context Gamma)) by
      (intro Hin; apply Hfresh; repeat rewrite in_app_iff; tauto).
    apply red_of_value.
    + apply v_tabs.
      change (locally_closed_tm (inst_tm tau sigma (tm_tabs t))).
      eapply inst_tm_lc; eauto.
      eapply has_type_lc. econstructor; eauto.
    + intros U P HU.
      eapply red_tbeta.
      * change (locally_closed_tm (inst_tm tau sigma (tm_tabs t))).
        eapply inst_tm_lc; eauto.
        eapply has_type_lc. econstructor; eauto.
      * exact HU.
      * unfold open_tm_ty.
        rewrite <- (inst_tm_ty_open_var t tau sigma X U 0 HXt Htau Hsigma).
        apply (proj1 (red_peq _ _
          (interp_open_var_root T X P e HXT) _)).
        apply H0; auto using tau_closed_set, env_sat_ty_set.
  - apply (proj2 (red_peq _ _
      (interp_open_root T U e (wf_ty_lc _ _ H)) _)).
    eapply red_tapp; eauto.
    eapply inst_ty_lc; [exact Htau|exact (wf_ty_lc _ _ H)].
  - apply red_of_value; constructor; constructor.
  - eapply red_succ; eauto.
  - eapply red_rec; eauto.
  - eapply red_choice; eauto.
Qed.

Lemma inst_ty_id : forall T,
  inst_ty (fun X => Ty_FVar X) T = T.
Proof.
  induction T; simpl; f_equal; auto.
Qed.

Lemma inst_tm_id : forall t,
  inst_tm (fun X => Ty_FVar X) (fun x => tm_fvar x) t = t.
Proof.
  induction t; simpl; f_equal; auto using inst_ty_id.
Qed.

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  intros t T Hty.
  pose proof (fundamental [] empty t T Hty
    (fun X => Ty_FVar X) (fun x => tm_fvar x)
    (fun _ => numeric_value)) as Hfund.
  assert (tau_closed (fun X => Ty_FVar X)) as Htau.
  { intro X. constructor. }
  assert (sigma_closed (fun x => tm_fvar x)) as Hsigma.
  { intro x. constructor. }
  assert (env_sat empty (fun _ => numeric_value)
    (fun x => tm_fvar x)) as Henv.
  { intros x U Hlook. discriminate. }
  specialize (Hfund Htau Hsigma Henv).
  rewrite inst_tm_id in Hfund.
  exact (red_sn _ _ Hfund).
Qed.

End SystemFNormalizationNondeterminismRecursionHardTask.
