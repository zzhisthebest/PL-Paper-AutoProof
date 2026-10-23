(** System F CBV strong-normalization benchmark, Hard variant.
    Features: nondeterminism. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFNormalizationNondeterminismHardTask.

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

  | Ty_All : ty -> ty.

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

Notation "'choice' t1 'or' t2" := (tm_choice t1 t2)
  (in custom systemf_tm at level 200, t1 custom systemf_tm, t2 custom systemf_tm at level 200) : systemf_scope.

Fixpoint open_ty_rec (k : nat) (U T : ty) : ty :=
  match T with
  | Ty_BVar i => if Nat.eqb k i then U else Ty_BVar i
  | Ty_FVar X => Ty_FVar X
  | Ty_Arrow T1 T2 =>
      Ty_Arrow (open_ty_rec k U T1) (open_ty_rec k U T2)
  | Ty_All T1 => Ty_All (open_ty_rec (S k) U T1)
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
  end.

Fixpoint tm_ty_subst (X : atom) (U : ty) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T t1 => tm_abs (ty_subst X U T) (tm_ty_subst X U t1)
  | tm_app t1 t2 => tm_app (tm_ty_subst X U t1) (tm_ty_subst X U t2)
  | tm_tabs t1 => tm_tabs (tm_ty_subst X U t1)
  | tm_tapp t1 T => tm_tapp (tm_ty_subst X U t1) (ty_subst X U T)
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
      lc_ty_at k (Ty_All T).

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
  | lc_tm_choice : forall K k t1 t2,
      lc_tm_at K k t1 -> lc_tm_at K k t2 -> lc_tm_at K k (tm_choice t1 t2).

Definition locally_closed_tm (t : tm) : Prop := lc_tm_at 0 0 t.

Inductive value : tm -> Prop :=
  | v_abs : forall T t,
      locally_closed_tm (tm_abs T t) ->
      value (tm_abs T t)
  | v_tabs : forall t,
      locally_closed_tm (tm_tabs t) ->
      value (tm_tabs t).

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
      wf_ty Delta (Ty_All T).

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

Inductive neutral : tm -> Prop :=
  | neutral_app : forall t1 t2, neutral (tm_app t1 t2)
  | neutral_tapp : forall t T, neutral (tm_tapp t T)
  | neutral_choice : forall t1 t2, neutral (tm_choice t1 t2).

Lemma lc_ty_weaken : forall k T, lc_ty_at k T -> lc_ty_at (S k) T.
Proof.
  intros k T H; induction H.
  - apply lc_ty_bvar; lia.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; assumption.
  - apply lc_ty_all; assumption.
Qed.

Lemma lc_tm_weaken : forall K k t, lc_tm_at K k t -> lc_tm_at K (S k) t.
Proof.
  intros K k t H; induction H.
  - apply lc_tm_bvar; lia.
  - apply lc_tm_fvar.
  - apply lc_tm_abs; assumption.
  - apply lc_tm_app; assumption.
  - apply lc_tm_tabs; assumption.
  - apply lc_tm_tapp; assumption.
  - apply lc_tm_choice; assumption.
Qed.

Lemma lc_tm_ty_weaken : forall K k t, lc_tm_at K k t -> lc_tm_at (S K) k t.
Proof.
  intros K k t H; induction H.
  - apply lc_tm_bvar.
    assumption.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + apply lc_ty_weaken; assumption.
    + assumption.
  - apply lc_tm_app; assumption.
  - apply lc_tm_tabs; assumption.
  - apply lc_tm_tapp.
    + assumption.
    + apply lc_ty_weaken; assumption.
  - apply lc_tm_choice; assumption.
Qed.

Lemma lc_ty_open_rec : forall j k T U,
  lc_ty_at j T -> j = S k -> lc_ty_at k U ->
  lc_ty_at k (open_ty_rec k U T).
Proof.
  intros j k T U H; revert k U.
  induction H; intros k0 U Ej Hu; simpl.
  - destruct (Nat.eqb k0 i) eqn:E.
    + apply Nat.eqb_eq in E; subst; exact Hu.
    + constructor. apply Nat.eqb_neq in E. lia.
  - apply lc_ty_fvar.
  - constructor; [apply IHlc_ty_at1 | apply IHlc_ty_at2]; assumption.
  - constructor. apply IHlc_ty_at with (k := S k0).
    + congruence.
    + apply lc_ty_weaken in Hu. exact Hu.
Qed.

Lemma lc_tm_open_rec : forall J K j k t u,
  lc_tm_at J j t -> J = K -> j = S k -> lc_tm_at K k u ->
  lc_tm_at K k (open_tm_rec k u t).
Proof.
  intros J K j k t u H; revert K k u.
  induction H; intros K0 k0 u EK Ej Hu; simpl.
  - destruct (Nat.eqb k0 i) eqn:E.
    + apply Nat.eqb_eq in E; subst; exact Hu.
    + constructor. apply Nat.eqb_neq in E. lia.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + subst K0; exact H.
    + apply lc_tm_weaken in Hu.
      apply IHlc_tm_at with (K := K0) (k := S k0).
      * exact EK.
      * congruence.
      * exact Hu.
  - apply lc_tm_app; [apply IHlc_tm_at1 | apply IHlc_tm_at2]; assumption.
  - apply lc_tm_tabs. apply IHlc_tm_at with (K := S K0) (k := k0).
    + congruence.
    + exact Ej.
    + apply lc_tm_ty_weaken in Hu. exact Hu.
  - apply lc_tm_tapp.
    + apply IHlc_tm_at; assumption.
    + rewrite <- EK; exact H0.
  - apply lc_tm_choice; [apply IHlc_tm_at1 | apply IHlc_tm_at2]; assumption.
Qed.

Lemma lc_tm_ty_open_rec : forall J K k t U,
  lc_tm_at J k t -> J = S K -> lc_ty_at K U ->
  lc_tm_at K k (open_tm_ty_rec K U t).
Proof.
  intros J K k t U H; revert K U.
  induction H; intros K0 U EJ HU; simpl.
  - apply lc_tm_bvar; assumption.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + eapply lc_ty_open_rec; eauto.
    + apply IHlc_tm_at; assumption.
  - apply lc_tm_app; [apply IHlc_tm_at1 | apply IHlc_tm_at2]; assumption.
  - apply lc_tm_tabs. apply IHlc_tm_at.
    + congruence.
    + apply lc_ty_weaken; exact HU.
  - apply lc_tm_tapp.
    + apply IHlc_tm_at; assumption.
    + eapply lc_ty_open_rec; eauto.
  - apply lc_tm_choice; [apply IHlc_tm_at1 | apply IHlc_tm_at2]; assumption.
Qed.

Lemma lc_open_tm : forall t u,
  lc_tm_at 0 1 t -> locally_closed_tm u ->
  locally_closed_tm (open_tm t u).
Proof. intros; eapply lc_tm_open_rec; eauto. Qed.

Lemma lc_open_tm_ty : forall t U,
  lc_tm_at 1 0 t -> locally_closed_ty U ->
  locally_closed_tm (open_tm_ty t U).
Proof. intros; eapply lc_tm_ty_open_rec; eauto. Qed.

Lemma lc_ty_open : forall T U,
  lc_ty_at 1 T -> locally_closed_ty U ->
  locally_closed_ty (open_ty T U).
Proof. intros; eapply lc_ty_open_rec; eauto. Qed.

Lemma lc_ty_open_inv_rec : forall k T X,
  lc_ty_at k (open_ty_rec k (Ty_FVar X) T) ->
  lc_ty_at (S k) T.
Proof.
  intros k T; revert k; induction T; intros k X H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst; constructor; lia.
    + inversion H; constructor; apply Nat.eqb_neq in E; lia.
  - constructor.
  - inversion H; constructor; eauto.
  - inversion H; constructor. eauto.
Qed.

Fixpoint ty_max (L : list atom) : nat :=
  match L with | [] => 0 | x :: L' => Nat.max x (ty_max L') end.

Lemma in_ty_max : forall x L, In x L -> x <= ty_max L.
Proof.
  intros x L H; induction L as [|y L IH]; simpl in *; [contradiction|].
  destruct H as [->|H].
  - apply Nat.le_max_l.
  - apply Nat.le_trans with (m := ty_max L).
    + apply IH; exact H.
    + apply Nat.le_max_r.
Qed.

Lemma ty_fresh : forall L, ~ In (S (ty_max L)) L.
Proof.
  intros L H. pose proof (in_ty_max _ _ H). lia.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H; induction H as
    [ Delta X Hin
    | Delta T1 T2 H1 IH1 H2 IH2
    | L Delta T Hopen IHopen ].
  - constructor.
  - constructor; assumption.
  - apply lc_ty_all. specialize (Hopen (S (ty_max L))).
    pose proof (ty_fresh L) as Hfresh.
    eapply lc_ty_open_inv_rec.
    eapply IHopen; exact Hfresh.
Qed.

Lemma sn_reduct : forall t u, strongly_normalizing t -> t --> u ->
  strongly_normalizing u.
Proof.
  intros t u H Hu; inversion H; eauto.
Qed.

Lemma value_not_neutral : forall t, value t -> ~ neutral t.
Proof. intros t Hv Hn; induction Hn; inversion Hv. Qed.

Record cand : Type := {
  cand_pred : tm -> Prop;
  cand_lc : forall t, cand_pred t -> locally_closed_tm t;
  cand_sn : forall t, cand_pred t -> strongly_normalizing t;
  cand_step : forall t u, t --> u -> cand_pred t -> cand_pred u;
  cand_neutral : forall t, locally_closed_tm t -> neutral t ->
    (forall u, t --> u -> cand_pred u) -> cand_pred t
}.

Arguments cand_pred _ _.

Lemma sn_all_reducts : forall t,
  (forall u, t --> u -> strongly_normalizing u) ->
  strongly_normalizing t.
Proof. intros; constructor; auto. Qed.

Lemma value_lc : forall t, value t -> locally_closed_tm t.
Proof. intros t H; inversion H; assumption. Qed.

Lemma lc_abs_body : forall T t,
  locally_closed_tm (tm_abs T t) -> lc_tm_at 0 1 t.
Proof. intros; unfold locally_closed_tm in H; inversion H; assumption. Qed.

Lemma lc_tabs_body : forall t,
  locally_closed_tm (tm_tabs t) -> lc_tm_at 1 0 t.
Proof. intros; unfold locally_closed_tm in H; inversion H; assumption. Qed.

Lemma lc_app_left : forall t1 t2,
  locally_closed_tm (tm_app t1 t2) -> locally_closed_tm t1.
Proof. intros; unfold locally_closed_tm in H; inversion H; assumption. Qed.

Lemma lc_app_right : forall t1 t2,
  locally_closed_tm (tm_app t1 t2) -> locally_closed_tm t2.
Proof. intros; unfold locally_closed_tm in H; inversion H; assumption. Qed.

Lemma lc_tapp_left : forall t T,
  locally_closed_tm (tm_tapp t T) -> locally_closed_tm t.
Proof. intros; unfold locally_closed_tm in H; inversion H; assumption. Qed.

Lemma step_lc : forall t u, locally_closed_tm t -> t --> u ->
  locally_closed_tm u.
Proof.
  intros t u Hlc Hs; revert Hlc; induction Hs as
    [ T t v Habs Hv
    | t1 t1' t2 Hstep IHstep Hlc2
    | v1 t2 t2' Hv1 Hstep IHstep
    | t T Htabs HT
    | t t' T Hstep IHstep HT
    | t1 t2 H1 H2
    | t1 t2 H1 H2 ]; intro Hlc.
  unfold locally_closed_tm in Hlc.
  - eapply lc_tm_open_rec.
    all: try reflexivity.
    all: try (apply value_lc; assumption).
    all: eapply lc_abs_body; eapply lc_app_left; exact Hlc.
  - apply lc_tm_app.
    + inversion Hlc; apply IHstep; assumption.
    + inversion Hlc; eauto.
  - apply lc_tm_app.
    + apply value_lc; exact Hv1.
    + inversion Hlc; apply IHstep; assumption.
  - eapply lc_tm_ty_open_rec.
    + eapply lc_tabs_body; eapply lc_tapp_left; exact Hlc.
    + reflexivity.
    + exact HT.
  - apply lc_tm_tapp.
    + inversion Hlc; apply IHstep; assumption.
    + exact HT.
  - inversion Hlc; assumption.
  - inversion Hlc; assumption.
Qed.

Definition cand_arrow (A B : cand) : cand.
Proof.
  refine {| cand_pred := fun t =>
    locally_closed_tm t /\ strongly_normalizing t /\
    (forall u, cand_pred A u -> cand_pred B (tm_app t u)) |}.
  - intros t [Hl [Hs Hf]]. exact Hl.
  - intros t [Hl [Hs Hf]]. exact Hs.
  - intros t u Htu [Hl [Hs Hf]].
    split; [eapply step_lc; eauto|].
    split; [eapply sn_reduct; eauto|].
    intros v Hv.
    eapply cand_step; eauto.
    apply ST_App1; eauto using cand_lc.
  - intros t Hl Hn Hr.
    split; [exact Hl|].
    split.
    + apply sn_all_reducts. intros u Htu.
      destruct (Hr u Htu) as [_ [Hsu _]]. exact Hsu.
    + intros v Hv.
      apply cand_neutral with (t := tm_app t v).
      * apply lc_tm_app; [exact Hl | eapply cand_lc; eauto].
      * apply neutral_app.
      * intros w Htw.
        inversion Htw; subst.
        -- exfalso.
           match goal with
           | Hn0 : neutral (tm_abs _ _) |- _ => inversion Hn0
           end.
        -- match goal with
           | Hs0 : ?q --> ?r |- _ =>
               destruct (Hr _ Hs0) as [_ [_ Hf0]]; exact (Hf0 v Hv)
           end.
        -- exfalso.
           match goal with
           | Hn0 : neutral ?q, Hv0 : value ?q |- _ =>
               exact (value_not_neutral q Hv0 Hn0)
           end.
Defined.

Definition cand_base : cand.
Proof.
  refine {| cand_pred := fun t => locally_closed_tm t /\ strongly_normalizing t |}.
  - intros t [Hl Hs]; exact Hl.
  - intros t [Hl Hs]; exact Hs.
  - intros t u Htu [Hl Hs]. split.
    + eapply step_lc; eauto.
    + eapply sn_reduct; eauto.
  - intros t Hl Hn Hr. split; [exact Hl|].
    apply sn_all_reducts. intros u Htu. apply Hr; exact Htu.
Defined.

Definition cand_all (Delta : ty_context) (F : cand -> ty -> cand) : cand.
Proof.
  refine {| cand_pred := fun t =>
    locally_closed_tm t /\ strongly_normalizing t /\
    (forall C U, wf_ty Delta U -> cand_pred (F C U) (tm_tapp t U)) |}.
  - intros t [Hl [Hs HF]]. exact Hl.
  - intros t [Hl [Hs HF]]. exact Hs.
  - intros t u Htu [Hl [Hs HF]].
    split; [eapply step_lc; eauto|].
    split; [eapply sn_reduct; eauto|].
    intros C U HU.
    apply cand_step with (c := F C U) (t := tm_tapp t U) (u := tm_tapp u U).
    + apply ST_TApp.
      * exact Htu.
      * eapply wf_ty_lc; exact HU.
    + apply HF; exact HU.
  - intros t Hl Hn Hr. split; [exact Hl|].
    split.
    + apply sn_all_reducts. intros u Htu.
      destruct (Hr u Htu) as [_ [Hsu _]]. exact Hsu.
    + intros C U HU.
      apply cand_neutral with (t := tm_tapp t U).
      * apply lc_tm_tapp; [exact Hl|].
        eapply wf_ty_lc; exact HU.
      * apply neutral_tapp.
      * intros w Htw.
        inversion Htw; subst.
        -- exfalso.
           match goal with
           | Hn0 : neutral (tm_tabs _) |- _ => inversion Hn0
           end.
        -- match goal with
           | Hs0 : ?q --> ?r |- _ =>
               destruct (Hr _ Hs0) as [_ [_ HF0]]; exact (HF0 C U HU)
           end.
Defined.

Definition ty_env := atom -> cand.
Definition ty_env_update (rho : ty_env) (X : atom) (C : cand) : ty_env :=
  fun Y => if Nat.eqb X Y then C else rho Y.

Fixpoint benv_nth (B : list cand) (i : nat) : cand :=
  match B, i with
  | C :: _, 0 => C
  | _ :: B', S i' => benv_nth B' i'
  | _, _ => cand_base
  end.

Fixpoint ty_interp (Delta : ty_context) (rho : ty_env)
    (B : list cand) (T : ty) : cand :=
  match T with
  | Ty_BVar i => benv_nth B i
  | Ty_FVar X => rho X
  | Ty_Arrow T1 T2 =>
      cand_arrow (ty_interp Delta rho B T1) (ty_interp Delta rho B T2)
  | Ty_All T1 =>
      cand_all Delta (fun C U => ty_interp Delta rho (C :: B) T1)
  end.

Definition ty_interp0 (Delta : ty_context) (rho : ty_env) (T : ty) : cand :=
  ty_interp Delta rho [] T.

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  (* Complete the proof of normalization. *)
Qed.

End SystemFNormalizationNondeterminismHardTask.
