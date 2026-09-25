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

Definition candidate (C : tm -> Prop) : Prop :=
  (forall t, C t -> locally_closed_tm t) /\
  (forall t, C t -> strongly_normalizing t) /\
  (forall t u, C t -> t --> u -> C u) /\
  (forall t, locally_closed_tm t -> ~ value t ->
      (forall u, t --> u -> C u) -> C t).

Definition reducible (V : tm -> Prop) (t : tm) : Prop :=
  locally_closed_tm t /\ strongly_normalizing t /\
  (forall v, t -->* v -> value v -> V v).

Definition empty_candidate : tm -> Prop := reducible (fun _ => False).

Fixpoint logical (T : ty) (bound : list (tm -> Prop))
    (free : atom -> tm -> Prop) : tm -> Prop :=
  match T with
  | Ty_BVar i => nth i bound empty_candidate
  | Ty_FVar X => free X
  | Ty_Arrow A B =>
      reducible (fun v => forall a, logical A bound free a ->
                                  logical B bound free (tm_app v a))
  | Ty_All B =>
      reducible (fun v => forall U, locally_closed_ty U ->
                      forall C, candidate C ->
                      logical B (C :: bound) free (tm_tapp v U))
  end.

Lemma value_no_step : forall v u, value v -> v --> u -> False.
Proof.
  intros v u Hv Hs. inversion Hv; subst; inversion Hs.
Qed.

Lemma value_dec : forall t,
  locally_closed_tm t -> value t \/ ~ value t.
Proof.
  intros t Hlc. destruct t.
  - inversion Hlc; lia.
  - right. intro Hv. inversion Hv.
  - left. constructor. exact Hlc.
  - right. intro Hv. inversion Hv.
  - left. constructor. exact Hlc.
  - right. intro Hv. inversion Hv.
  - right. intro Hv. inversion Hv.
Qed.

Lemma multi_one : forall t u, t --> u -> t -->* u.
Proof. intros; eapply multi_step; eauto using multi_refl. Qed.

Lemma multi_trans : forall t u v, t -->* u -> u -->* v -> t -->* v.
Proof.
  intros t u v H; induction H; intros Hv; eauto using multi_step.
Qed.

Lemma lc_ty_weaken : forall T k j, lc_ty_at k T -> k <= j -> lc_ty_at j T.
Proof.
  intros T k j H; revert j.
  induction H; intros j Hj.
  - apply lc_ty_bvar. lia.
  - constructor.
  - constructor; eauto.
  - constructor. apply IHlc_ty_at. lia.
Qed.

Lemma lc_tm_weaken : forall t K k J j,
  lc_tm_at K k t -> K <= J -> k <= j -> lc_tm_at J j t.
Proof.
  intros t K k J j H; revert J j.
  induction H; intros J j HK Hk.
  - apply lc_tm_bvar. lia.
  - constructor.
  - constructor.
    + eapply lc_ty_weaken; eauto.
    + apply IHlc_tm_at; lia.
  - constructor; eauto.
  - constructor. apply IHlc_tm_at; lia.
  - constructor.
    + apply IHlc_tm_at; lia.
    + eapply lc_ty_weaken; eauto.
  - constructor; eauto.
Qed.

Lemma lc_ty_open_rec : forall T k U,
  lc_ty_at (S k) T -> locally_closed_ty U ->
  lc_ty_at k (open_ty_rec k U T).
Proof.
  intros T; induction T; intros k U Ht Hu; inversion Ht; subst; simpl;
    try (constructor; eauto; fail).
  - destruct (Nat.eqb k n) eqn:E.
    + eapply lc_ty_weaken; eauto; lia.
    + constructor. apply Nat.eqb_neq in E. lia.
Qed.

Lemma lc_tm_open_rec : forall t K k u,
  lc_tm_at K (S k) t -> lc_tm_at K 0 u ->
  lc_tm_at K k (open_tm_rec k u t).
Proof.
  intros t; induction t; intros K k u Ht Hu; inversion Ht; subst; simpl;
    try (constructor; eauto; fail).
  - destruct (Nat.eqb k n) eqn:E.
    + eapply lc_tm_weaken; eauto; lia.
    + constructor. apply Nat.eqb_neq in E. lia.
  - constructor. apply IHt; eauto.
    eapply lc_tm_weaken; eauto; lia.
Qed.

Lemma lc_tm_ty_open_rec : forall t K k U,
  lc_tm_at (S K) k t -> locally_closed_ty U ->
  lc_tm_at K k (open_tm_ty_rec K U t).
Proof.
  intros t; induction t; intros K k U Ht Hu; inversion Ht; subst; simpl;
    try (constructor; eauto using lc_ty_open_rec; fail).
Qed.

Lemma step_lc : forall t u,
  t --> u -> locally_closed_tm t -> locally_closed_tm u.
Proof.
  intros t u H; induction H; intros Hlc; inversion Hlc; subst.
  - match goal with H : lc_tm_at _ _ (tm_abs _ _) |- _ => inversion H; subst end.
    eapply lc_tm_open_rec; eauto.
  - constructor; [apply IHstep |]; assumption.
  - constructor; [|apply IHstep]; assumption.
  - match goal with H : lc_tm_at _ _ (tm_tabs _) |- _ => inversion H; subst end.
    eapply lc_tm_ty_open_rec; eauto.
  - constructor; [apply IHstep |]; assumption.
  - assumption.
  - assumption.
Qed.

Lemma reducible_step : forall V t u,
  reducible V t -> t --> u -> reducible V u.
Proof.
  intros V t u [Hlc [Hsn Hval]] Hstep.
  inversion Hsn as [t0 Hall]; subst.
  split.
  - eapply step_lc; eauto.
  - split; [eauto |].
    intros v Hm Hv. apply (Hval v); auto.
    eapply multi_step; eauto.
Qed.

Lemma reducible_expand : forall V t,
  locally_closed_tm t -> ~ value t ->
  (forall u, t --> u -> reducible V u) -> reducible V t.
Proof.
  intros V t Hlc Hnon Hall. split; [assumption|].
  split.
  - constructor. intros u Hstep. apply (proj1 (proj2 (Hall u Hstep))).
  - intros v Hmulti Hval. inversion Hmulti; subst.
    + contradiction.
    + apply (proj2 (proj2 (Hall y H))) with (v := v); assumption.
Qed.

Lemma reducible_candidate : forall V, candidate (reducible V).
Proof.
  intro V. unfold candidate. split.
  - intros t [Hlc _]. exact Hlc.
  - split.
    + intros t [_ [Hsn _]]. exact Hsn.
    + split.
      * intros t u Hr Hstep. eapply reducible_step; eauto.
      * intros t Hlc Hnon Hall. eapply reducible_expand; eauto.
Qed.

Lemma reducible_value : forall V v,
  locally_closed_tm v -> value v -> V v -> reducible V v.
Proof.
  intros V v Hlc Hv Hsemantic. split; [assumption|]. split.
  - constructor. intros u Hstep. exfalso. eapply value_no_step; eauto.
  - intros w Hmulti Hw. inversion Hmulti; subst; auto.
    exfalso. eapply (value_no_step v y); eauto.
Qed.

Lemma logical_candidate : forall T bound free,
  (forall C, In C bound -> candidate C) ->
  (forall X, candidate (free X)) ->
  candidate (logical T bound free).
Proof.
  induction T; intros bound free Hb Hf; simpl.
  - induction bound as [|C bound IH] in n, Hb |- *.
    + destruct n; apply reducible_candidate.
    + destruct n; simpl.
      * apply Hb. left; reflexivity.
      * apply IH. intros D HD. apply Hb. right; assumption.
  - apply Hf.
  - apply reducible_candidate.
  - apply reducible_candidate.
Qed.

Lemma candidate_app : forall A B f a,
  candidate A -> candidate B ->
  reducible (fun v => forall b, A b -> B (tm_app v b)) f ->
  A a -> B (tm_app f a).
Proof.
  intros A B f a HA HB Hf Ha.
  destruct Hf as [Hlc [Hsn Hvalues]].
  revert a Ha. induction Hsn as [f Hsteps IH]. intros a Ha.
  destruct (value_dec f Hlc) as [Hvalue | Hnon].
  - apply (Hvalues f (multi_refl _) Hvalue); assumption.
  - apply (proj2 (proj2 (proj2 HB))).
    + constructor; [assumption | apply (proj1 HA); assumption].
    + intros Hval. inversion Hval.
    + intros u Hstep. inversion Hstep; subst.
      * exfalso. apply Hnon. constructor; assumption.
      * apply IH; auto.
        -- eapply step_lc; eauto.
        -- intros v Hmulti Hv. apply (Hvalues v); auto.
           eapply multi_step; eauto.
      * exfalso; eauto using value_no_step.
Qed.

Lemma candidate_tapp : forall B f U,
  candidate B -> locally_closed_ty U ->
  reducible (fun v => B (tm_tapp v U)) f -> B (tm_tapp f U).
Proof.
  intros B f U HB HU [Hlc [Hsn Hvalues]].
  induction Hsn as [f Hsteps IH].
  destruct (value_dec f Hlc) as [Hvalue | Hnon].
  - apply (Hvalues f (multi_refl _) Hvalue).
  - apply (proj2 (proj2 (proj2 HB))).
    + constructor; assumption.
    + intros Hval. inversion Hval.
    + intros u Hstep. inversion Hstep; subst.
      * exfalso. apply Hnon. constructor; assumption.
      * apply IH; auto.
        -- eapply step_lc; eauto.
        -- intros v Hmulti Hv. apply Hvalues; auto.
           eapply multi_step; eauto.
Qed.

Lemma candidate_choice : forall C l r,
  candidate C -> C l -> C r -> C (tm_choice l r).
Proof.
  intros C l r HC Hl Hr.
  apply (proj2 (proj2 (proj2 HC))).
  - constructor; apply (proj1 HC); assumption.
  - intros Hv. inversion Hv.
  - intros u Hstep. inversion Hstep; subst; assumption.
Qed.

Fixpoint fresh (L : list atom) : atom :=
  match L with [] => 0 | x :: xs => S (Nat.max x (fresh xs)) end.

Lemma fresh_gt : forall L x, In x L -> x < fresh L.
Proof.
  induction L as [|y L IH]; intros x H; simpl in *.
  - contradiction.
  - destruct H as [H | H]; subst; [lia|].
    specialize (IH x H). lia.
Qed.

Lemma fresh_notin : forall L, ~ In (fresh L) L.
Proof.
  intros L H. pose proof (fresh_gt L (fresh L) H). lia.
Qed.

Fixpoint fv_ty (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow A B => fv_ty A ++ fv_ty B
  | Ty_All B => fv_ty B
  end.

Fixpoint fv_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs _ b => fv_tm b
  | tm_app a b | tm_choice a b => fv_tm a ++ fv_tm b
  | tm_tabs b => fv_tm b
  | tm_tapp a _ => fv_tm a
  end.

Fixpoint ftv_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_fvar _ => []
  | tm_abs T b => fv_ty T ++ ftv_tm b
  | tm_app a b | tm_choice a b => ftv_tm a ++ ftv_tm b
  | tm_tabs b => ftv_tm b
  | tm_tapp a U => ftv_tm a ++ fv_ty U
  end.

Definition set_ty (rho : atom -> ty) (X : atom) (U : ty) : atom -> ty :=
  fun Y => if Nat.eqb X Y then U else rho Y.

Definition set_tm (sigma : atom -> tm) (x : atom) (v : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then v else sigma y.

Fixpoint close_ty (rho : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => rho X
  | Ty_Arrow A B => Ty_Arrow (close_ty rho A) (close_ty rho B)
  | Ty_All B => Ty_All (close_ty rho B)
  end.

Fixpoint close_tm (rho : atom -> ty) (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_abs T b => tm_abs (close_ty rho T) (close_tm rho sigma b)
  | tm_app a b => tm_app (close_tm rho sigma a) (close_tm rho sigma b)
  | tm_tabs b => tm_tabs (close_tm rho sigma b)
  | tm_tapp a U => tm_tapp (close_tm rho sigma a) (close_ty rho U)
  | tm_choice a b => tm_choice (close_tm rho sigma a) (close_tm rho sigma b)
  end.

Lemma close_ty_lc : forall T k rho,
  lc_ty_at k T -> (forall X, locally_closed_ty (rho X)) ->
  lc_ty_at k (close_ty rho T).
Proof.
  intros T; induction T; intros k rho Hlc Hr; inversion Hlc; subst;
    simpl; eauto using lc_ty_weaken.
  eapply lc_ty_weaken with (k := 0); [apply Hr | lia].
Qed.

Lemma close_tm_lc : forall t K k rho sigma,
  lc_tm_at K k t -> (forall X, locally_closed_ty (rho X)) ->
  (forall x, locally_closed_tm (sigma x)) ->
  lc_tm_at K k (close_tm rho sigma t).
Proof.
  intros t; induction t; intros K k rho sigma Hlc Hr Hs;
    inversion Hlc; subst; simpl; eauto using lc_ty_weaken,
      lc_tm_weaken, close_ty_lc.
  eapply lc_tm_weaken with (K := 0) (k := 0); [apply Hs | lia | lia].
Qed.

Lemma lc_ty_open_back : forall T k X,
  lc_ty_at k (open_ty_rec k (Ty_FVar X) T) -> lc_ty_at (S k) T.
Proof.
  intros T; induction T; intros k X H; simpl in H; simpl;
    try (inversion H; subst; constructor; eauto; fail).
  - destruct (Nat.eqb k n) eqn:E.
    + constructor. apply Nat.eqb_eq in E. lia.
    + inversion H; subst. constructor. lia.
Qed.

Lemma lc_tm_open_back : forall t K k x,
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) ->
  lc_tm_at K (S k) t.
Proof.
  intros t; induction t; intros K k x H; simpl in H; simpl;
    try (inversion H; subst; constructor; eauto; fail).
  - destruct (Nat.eqb k n) eqn:E.
    + constructor. apply Nat.eqb_eq in E. lia.
    + inversion H; subst. constructor. lia.
Qed.

Lemma lc_tm_ty_open_back : forall t K k X,
  lc_tm_at K k (open_tm_ty_rec K (Ty_FVar X) t) ->
  lc_tm_at (S K) k t.
Proof.
  intros t; induction t; intros K k X H; simpl in H; simpl;
    try (inversion H; subst; constructor; eauto using lc_ty_open_back; fail).
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H; induction H.
  - constructor.
  - constructor; assumption.
  - constructor. apply lc_ty_open_back with (X := fresh L).
    apply H0. apply fresh_notin.
Qed.

Lemma typed_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T H; induction H.
  - constructor.
  - constructor.
    + eapply wf_ty_lc; eassumption.
    + apply lc_tm_open_back with (x := fresh L).
      apply H1; apply fresh_notin.
  - constructor; assumption.
  - constructor. apply lc_tm_ty_open_back with (X := fresh L).
    apply H0; apply fresh_notin.
  - constructor; auto. eapply wf_ty_lc; eassumption.
  - constructor; assumption.
Qed.

Lemma logical_prefix : forall T k bs bs' fs t,
  lc_ty_at k T ->
  (forall i v, i < k -> nth i bs empty_candidate v <->
                         nth i bs' empty_candidate v) ->
  (logical T bs fs t <-> logical T bs' fs t).
Proof.
  induction T; intros k bs bs' fs t Hlc Hprefix;
    inversion Hlc; subst; simpl.
  - apply Hprefix; assumption.
  - tauto.
  - split; intros [Hl [Hs Hv]];
      (split; [exact Hl | split; [exact Hs |]]);
      intros v Hm Hval a Ha.
    + apply (proj1 (IHT2 _ _ _ _ _ H3 Hprefix)).
      apply (Hv v Hm Hval a).
      apply (proj2 (IHT1 _ _ _ _ _ H2 Hprefix)); assumption.
    + apply (proj2 (IHT2 _ _ _ _ _ H3 Hprefix)).
      apply (Hv v Hm Hval a).
      apply (proj1 (IHT1 _ _ _ _ _ H2 Hprefix)); assumption.
  - split; intros [Hl [Hs Hv]];
      (split; [exact Hl | split; [exact Hs |]]);
      intros v Hm Hval U HU C HC.
    + assert (Hp : forall i w, i < S k ->
                   nth i (C :: bs) empty_candidate w <->
                   nth i (C :: bs') empty_candidate w).
      { intros [|i] w Hi; simpl; [tauto|]. apply Hprefix. lia. }
      apply (proj1 (IHT _ (C :: bs) (C :: bs') _ _ H1 Hp)).
      apply (Hv v Hm Hval U HU C HC).
    + assert (Hp : forall i w, i < S k ->
                   nth i (C :: bs) empty_candidate w <->
                   nth i (C :: bs') empty_candidate w).
      { intros [|i] w Hi; simpl; [tauto|]. apply Hprefix. lia. }
      apply (proj2 (IHT _ (C :: bs) (C :: bs') _ _ H1 Hp)).
      apply (Hv v Hm Hval U HU C HC).
Qed.

Lemma logical_open : forall T k bs fs U t,
  lc_ty_at (S k) T -> length bs = k -> locally_closed_ty U ->
  (logical (open_ty_rec k U T) bs fs t <->
   logical T (bs ++ [logical U [] fs]) fs t).
Proof.
  induction T; intros k bs fs U t Hlc Hlength HU;
    inversion Hlc; subst; simpl.
  - destruct (Nat.eqb (length bs) n) eqn:E.
    + apply Nat.eqb_eq in E; subst n.
      rewrite nth_middle.
      simpl. apply logical_prefix with (k := 0); auto.
      intros i v Hi; lia.
    + apply Nat.eqb_neq in E. assert (n < length bs) by lia.
      rewrite app_nth1 by lia. tauto.
  - tauto.
  - split; intros [Hl [Hs Hv]];
      (split; [exact Hl | split; [exact Hs |]]);
      intros v Hm Hval a Ha.
    + apply (proj1 (IHT2 _ _ _ _ _ H3 eq_refl HU)).
      apply (Hv v Hm Hval a).
      apply (proj2 (IHT1 _ _ _ _ _ H2 eq_refl HU)); assumption.
    + apply (proj2 (IHT2 _ _ _ _ _ H3 eq_refl HU)).
      apply (Hv v Hm Hval a).
      apply (proj1 (IHT1 _ _ _ _ _ H2 eq_refl HU)); assumption.
  - split; intros [Hl [Hs Hv]];
      (split; [exact Hl | split; [exact Hs |]]);
      intros v Hm Hval W HW C HC.
    + apply (proj1 (IHT _ (C :: bs) _ _ _ H1 eq_refl HU)).
      apply (Hv v Hm Hval W HW C HC).
    + apply (proj2 (IHT _ (C :: bs) _ _ _ H1 eq_refl HU)).
      apply (Hv v Hm Hval W HW C HC).
Qed.

Lemma typed_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_ty T.
Proof.
  intros Delta Gamma t T H; induction H.
  - eapply wf_ty_lc; eauto.
  - constructor; [eapply wf_ty_lc; eauto|].
    apply (H1 (fresh L) (fresh_notin L)).
  - inversion IHhas_type1; assumption.
  - constructor. apply lc_ty_open_back with (X := fresh L).
    apply H0. apply fresh_notin.
  - inversion IHhas_type; subst.
    eapply lc_ty_open_rec; eauto using wf_ty_lc.
  - assumption.
Qed.

Lemma logical_free_ext : forall T bs fs gs t,
  (forall X, In X (fv_ty T) -> forall u, fs X u <-> gs X u) ->
  (logical T bs fs t <-> logical T bs gs t).
Proof.
  induction T; intros bs fs gs t He; simpl in *; try tauto.
  - apply He. simpl; auto.
  - split; intros [Hl [Hs Hv]];
      (split; [exact Hl | split; [exact Hs |]]);
      intros v Hm Hval a Ha.
    + apply (proj1 (IHT2 _ _ _ _ (fun X HX => He X (in_or_app _ _ _ (or_intror HX))))).
      apply (Hv v Hm Hval a).
      apply (proj2 (IHT1 _ _ _ _ (fun X HX => He X (in_or_app _ _ _ (or_introl HX))))); assumption.
    + apply (proj2 (IHT2 _ _ _ _ (fun X HX => He X (in_or_app _ _ _ (or_intror HX))))).
      apply (Hv v Hm Hval a).
      apply (proj1 (IHT1 _ _ _ _ (fun X HX => He X (in_or_app _ _ _ (or_introl HX))))); assumption.
  - split; intros [Hl [Hs Hv]];
      (split; [exact Hl | split; [exact Hs |]]);
      intros v Hm Hval U HU C HC.
    + apply (proj1 (IHT (C :: bs) _ _ _ He)).
      apply (Hv v Hm Hval U HU C HC).
    + apply (proj2 (IHT (C :: bs) _ _ _ He)).
      apply (Hv v Hm Hval U HU C HC).
Qed.

Lemma open_ty_lc_id : forall T K k U,
  lc_ty_at K T -> K <= k -> open_ty_rec k U T = T.
Proof.
  intros T; induction T; intros K k U H Hle; inversion H; subst; simpl.
  - destruct (Nat.eqb k n) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - reflexivity.
  - f_equal; eauto.
  - f_equal. apply IHT with (K := S K); auto; lia.
Qed.

Lemma open_tm_lc_id : forall t J j k u,
  lc_tm_at J j t -> j <= k -> open_tm_rec k u t = t.
Proof.
  intros t; induction t; intros J j k u H Hle;
    inversion H; subst; simpl.
  - destruct (Nat.eqb k n) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - reflexivity.
  - f_equal. apply IHt with (J := J) (j := S j); auto; lia.
  - f_equal; eauto.
  - f_equal. apply IHt with (J := S J) (j := j); auto.
  - f_equal; eauto.
  - f_equal; eauto.
Qed.

Lemma open_tm_ty_lc_id : forall t J K k U,
  lc_tm_at J k t -> J <= K -> open_tm_ty_rec K U t = t.
Proof.
  intros t; induction t; intros J K k U H Hle;
    inversion H; subst; simpl; try reflexivity.
  - f_equal.
    + eapply open_ty_lc_id; eauto.
    + apply IHt with (J := J) (k := S k); auto.
  - f_equal; eauto.
  - f_equal. apply IHt with (J := S J) (k := k); auto; lia.
  - f_equal; eauto using open_ty_lc_id.
  - f_equal; eauto.
Qed.

Lemma notin_app : forall (X : atom) A B,
  ~ In X (A ++ B) -> ~ In X A /\ ~ In X B.
Proof.
  intros X A B H. split; intros Hi; apply H; apply in_or_app; auto.
Qed.

Lemma close_open_tm : forall t k x rho sigma v,
  ~ In x (fv_tm t) -> (forall y, locally_closed_tm (sigma y)) ->
  close_tm rho (set_tm sigma x v) (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k v (close_tm rho sigma t).
Proof.
  induction t; intros k x rho sigma v Hfresh Hs; simpl in *.
  - destruct (Nat.eqb k n); simpl; [unfold set_tm; rewrite Nat.eqb_refl|]; reflexivity.
  - assert (x <> a) by (intro E; subst; apply Hfresh; simpl; auto).
    unfold set_tm. destruct (Nat.eqb x a) eqn:E;
      [apply Nat.eqb_eq in E; contradiction|].
    symmetry. apply open_tm_lc_id with (j := 0) (J := 0);
      [apply Hs | lia].
  - f_equal. apply IHt; auto.
  - apply notin_app in Hfresh as [H1 H2].
    f_equal; [apply IHt1 |apply IHt2]; auto.
  - f_equal. apply IHt; auto.
  - f_equal. apply IHt; auto.
  - apply notin_app in Hfresh as [H1 H2].
    f_equal; [apply IHt1 |apply IHt2]; auto.
Qed.

Lemma close_open_ty : forall T k X rho U,
  ~ In X (fv_ty T) -> (forall Y, locally_closed_ty (rho Y)) ->
  close_ty (set_ty rho X U) (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k U (close_ty rho T).
Proof.
  induction T; intros k X rho U Hfresh Hr; simpl in *.
  - destruct (Nat.eqb k n); simpl; [unfold set_ty; rewrite Nat.eqb_refl|]; reflexivity.
  - assert (X <> a) by (intro E; subst; apply Hfresh; simpl; auto).
    unfold set_ty. destruct (Nat.eqb X a) eqn:E;
      [apply Nat.eqb_eq in E; contradiction|].
    symmetry. apply open_ty_lc_id with (K := 0); [apply Hr | lia].
  - apply notin_app in Hfresh as [H1 H2].
    f_equal; [apply IHT1 |apply IHT2]; auto.
  - f_equal. apply IHT; auto.
Qed.

Lemma close_open_tm_ty : forall t k X rho sigma U,
  ~ In X (ftv_tm t) -> (forall Y, locally_closed_ty (rho Y)) ->
  (forall x, locally_closed_tm (sigma x)) ->
  close_tm (set_ty rho X U) sigma (open_tm_ty_rec k (Ty_FVar X) t) =
  open_tm_ty_rec k U (close_tm rho sigma t).
Proof.
  induction t; intros k X rho sigma U Hfresh Hr Hs; simpl in *; auto.
  - symmetry. apply open_tm_ty_lc_id with (J := 0) (k := 0);
      [apply Hs | lia].
  - apply notin_app in Hfresh as [H1 H2]. f_equal.
    + apply close_open_ty; auto.
    + apply IHt; auto.
  - apply notin_app in Hfresh as [H1 H2].
    f_equal; [apply IHt1 |apply IHt2]; auto.
  - f_equal. apply IHt; auto.
  - apply notin_app in Hfresh as [H1 H2]. f_equal.
    + apply IHt; auto.
    + apply close_open_ty; auto.
  - apply notin_app in Hfresh as [H1 H2].
    f_equal; [apply IHt1 |apply IHt2]; auto.
Qed.

Lemma candidate_beta : forall A B T t a,
  candidate A -> candidate B ->
  locally_closed_tm (tm_abs T t) ->
  (forall b, A b -> B (open_tm t b)) ->
  A a -> B (tm_app (tm_abs T t) a).
Proof.
  intros A B T t a HA HB Habs Hbody Ha.
  pose proof (proj1 (proj2 HA) a Ha) as Hsn.
  revert Ha. induction Hsn as [a Hsteps IH]; intros Ha.
  apply (proj2 (proj2 (proj2 HB))).
  - constructor; [assumption|apply (proj1 HA); assumption].
  - intros Hv. inversion Hv.
  - intros u Hstep. inversion Hstep; subst.
    + apply Hbody. assumption.
    + exfalso. eapply value_no_step; eauto.
    + apply IH; auto. eapply (proj1 (proj2 (proj2 HA))); eauto.
Qed.

Lemma candidate_type_beta : forall C t U,
  candidate C -> locally_closed_tm (tm_tabs t) ->
  locally_closed_ty U -> C (open_tm_ty t U) ->
  C (tm_tapp (tm_tabs t) U).
Proof.
  intros C t U HC Htab HU Hbody.
  apply (proj2 (proj2 (proj2 HC))).
  - constructor; assumption.
  - intros Hv. inversion Hv.
  - intros v Hstep. inversion Hstep; subst.
    + assumption.
    + exfalso. eapply value_no_step; eauto.
Qed.

Fixpoint fv_context (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (_, T) :: rest => fv_ty T ++ fv_context rest
  end.

Lemma lookup_fv : forall Gamma x T X,
  lookup_context x Gamma = Some T -> In X (fv_ty T) ->
  In X (fv_context Gamma).
Proof.
  induction Gamma as [|[y U] rest IH]; intros x T X Hlook Hin;
    simpl in *; [discriminate|].
  destruct (Nat.eqb x y) eqn:E.
  - injection Hlook as <-. apply in_or_app; left; assumption.
  - apply in_or_app; right. eapply IH; eauto.
Qed.

Lemma logical_good : forall T eta,
  (forall X, candidate (eta X)) -> candidate (logical T [] eta).
Proof.
  intros T eta Heta. apply logical_candidate; auto.
  intros C HC. contradiction.
Qed.

Lemma logical_fresh : forall T eta X C t,
  ~ In X (fv_ty T) ->
  logical T [] eta t <->
  logical T [] (fun Y => if Nat.eqb X Y then C else eta Y) t.
Proof.
  intros T eta X C t Hfresh. apply logical_free_ext.
  intros Y HY u. destruct (Nat.eqb X Y) eqn:E; [|tauto].
  apply Nat.eqb_eq in E; subst. contradiction.
Qed.

Lemma logical_open_fresh : forall T X eta C t,
  lc_ty_at 1 T -> ~ In X (fv_ty T) ->
  (logical (open_ty T (Ty_FVar X)) []
     (fun Y => if Nat.eqb X Y then C else eta Y) t <->
   logical T [C] eta t).
Proof.
  intros T X eta C t Hlc Hfresh.
  rewrite (logical_open T 0 [] _ (Ty_FVar X) t Hlc eq_refl).
  2: constructor.
  simpl. rewrite Nat.eqb_refl.
  apply logical_free_ext.
  intros Y HY v. destruct (Nat.eqb X Y) eqn:E; [|tauto].
  apply Nat.eqb_eq in E; subst; contradiction.
Qed.

Theorem fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall rho eta sigma,
    (forall X, locally_closed_ty (rho X)) ->
    (forall X, candidate (eta X)) ->
    (forall x, locally_closed_tm (sigma x)) ->
    (forall x U, lookup_context x Gamma = Some U ->
       logical U [] eta (sigma x)) ->
    logical T [] eta (close_tm rho sigma t).
Proof.
  intros Delta Gamma t T Hty.
  induction Hty; intros rho eta sigma Hr He Hs Hg.
  - simpl. eapply Hg; eauto.
  - assert (Hclosed : locally_closed_tm
        (tm_abs (close_ty rho T1) (close_tm rho sigma t2))).
    { change (locally_closed_tm (close_tm rho sigma (tm_abs T1 t2))).
      eapply close_tm_lc; eauto.
      eapply typed_lc. eapply (T_Abs L); eauto. }
    simpl. apply reducible_value.
    + exact Hclosed.
    + constructor. exact Hclosed.
    + intros a Ha.
      eapply candidate_beta with (A := logical T1 [] eta).
      * apply logical_good; assumption.
      * apply logical_good; assumption.
      * exact Hclosed.
      * intros b Hb.
        set (x := fresh (L ++ fv_tm t2)).
        assert (HxL : ~ In x L /\ ~ In x (fv_tm t2)).
        { apply notin_app. unfold x. apply fresh_notin. }
        destruct HxL as [HxL Hxt].
        change (logical T2 [] eta (open_tm_rec 0 b (close_tm rho sigma t2))).
        rewrite <- (close_open_tm t2 0 x rho sigma b Hxt Hs).
        apply (H1 x HxL rho eta (set_tm sigma x b) Hr He).
        -- intros y. unfold set_tm.
           destruct (Nat.eqb x y); [apply (proj1 (logical_good T1 eta He)); assumption |apply Hs].
        -- intros y V Hlook. simpl in Hlook. unfold set_tm.
           destruct (Nat.eqb x y) eqn:E.
           ++ apply Nat.eqb_eq in E; subst y.
              rewrite Nat.eqb_refl in Hlook. injection Hlook as <-. assumption.
           ++ rewrite (Nat.eqb_sym y x), E in Hlook. eapply Hg; eauto.
      * assumption.
  - simpl. eapply candidate_app with
      (A := logical T1 [] eta) (B := logical T2 [] eta).
    + apply logical_good; assumption.
    + apply logical_good; assumption.
    + apply IHHty1; assumption.
    + apply IHHty2; assumption.
  - assert (Hclosed : locally_closed_tm (tm_tabs (close_tm rho sigma t))).
    { change (locally_closed_tm (close_tm rho sigma (tm_tabs t))).
      eapply close_tm_lc; eauto.
      eapply typed_lc. eapply (T_TAbs L); eauto. }
    assert (Hbodylc : lc_ty_at 1 T).
    { pose proof (typed_type_lc _ _ _ _ (T_TAbs L Delta Gamma t T H)) as Hl.
      inversion Hl; assumption. }
    simpl. apply reducible_value.
    + exact Hclosed.
    + constructor. exact Hclosed.
    + intros U HU C HC.
      apply candidate_type_beta.
      * apply logical_candidate.
        -- intros D HD. simpl in HD. destruct HD as [<- | []]. exact HC.
        -- exact He.
      * exact Hclosed.
      * exact HU.
      * set (X := fresh (L ++ ftv_tm t ++ fv_ty T ++ fv_context Gamma)).
        assert (Hfresh : ~ In X L /\ ~ In X (ftv_tm t) /\
                         ~ In X (fv_ty T) /\ ~ In X (fv_context Gamma)).
        { unfold X. pose proof (fresh_notin
            (L ++ ftv_tm t ++ fv_ty T ++ fv_context Gamma)) as Hnot.
          repeat rewrite in_app_iff in Hnot. tauto. }
        destruct Hfresh as [HXL [HXt [HXT HXG]]].
        set (eta' := fun Y => if Nat.eqb X Y then C else eta Y).
        change (logical T [C] eta
          (open_tm_ty_rec 0 U (close_tm rho sigma t))).
        rewrite <- (close_open_tm_ty t 0 X rho sigma U HXt Hr Hs).
        apply (proj1 (logical_open_fresh T X eta C _ Hbodylc HXT)).
        apply (H0 X HXL (set_ty rho X U) eta' sigma).
        -- intros Y. unfold set_ty. destruct (Nat.eqb X Y); auto.
        -- intros Y. unfold eta'. destruct (Nat.eqb X Y); auto.
        -- exact Hs.
        -- intros y V Hlook.
           assert (Hnot : ~ In X (fv_ty V)).
           { intro Hin. apply HXG. eapply lookup_fv; eauto. }
           apply (proj1 (logical_fresh V eta X C _ Hnot)).
           eapply Hg; eauto.
  - simpl.
    assert (HUl : locally_closed_ty (close_ty rho U)).
    { eapply close_ty_lc; [eapply wf_ty_lc; eauto | exact Hr]. }
    assert (HTl : lc_ty_at 1 T).
    { pose proof (typed_type_lc _ _ _ _ Hty) as Hl.
      inversion Hl; assumption. }
    apply (proj2 (logical_open T 0 [] eta U _ HTl eq_refl
      (wf_ty_lc _ _ H))).
    simpl.
    eapply candidate_tapp with (B := logical T [logical U [] eta] eta).
    + apply logical_candidate.
      * intros C HC. simpl in HC. destruct HC as [<- | []].
        apply logical_good; assumption.
      * exact He.
    + exact HUl.
    + destruct (IHHty rho eta sigma Hr He Hs Hg) as [Hl [Hsn Hv]].
      split; [exact Hl|split; [exact Hsn|]].
      intros v Hm Hval.
      apply (Hv v Hm Hval (close_ty rho U) HUl
        (logical U [] eta) (logical_good U eta He)).
  - simpl. eapply candidate_choice with (C := logical T [] eta).
    + apply logical_good; assumption.
    + apply IHHty1; assumption.
    + apply IHHty2; assumption.
Qed.

Lemma close_ty_identity : forall T,
  close_ty (fun X => Ty_FVar X) T = T.
Proof.
  induction T; simpl; f_equal; auto.
Qed.

Lemma close_tm_identity : forall t,
  close_tm (fun X => Ty_FVar X) (fun x => tm_fvar x) t = t.
Proof.
  induction t; simpl; f_equal; auto using close_ty_identity.
Qed.

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  intros t T Hty.
  pose proof (fundamental [] empty t T Hty
    (fun X => Ty_FVar X) (fun X => empty_candidate)
    (fun x => tm_fvar x)) as Hsem.
  assert (Hr : forall X, locally_closed_ty (Ty_FVar X)).
  { intro X. constructor. }
  assert (He : forall X : atom, candidate empty_candidate).
  { intro X. apply reducible_candidate. }
  assert (Hs : forall x : atom, locally_closed_tm (tm_fvar x)).
  { intro x. constructor. }
  specialize (Hsem Hr He Hs).
  assert (Hg : forall x U, lookup_context x empty = Some U ->
      logical U [] (fun _ => empty_candidate) (tm_fvar x)).
  { intros x U Hlookup. discriminate Hlookup. }
  specialize (Hsem Hg).
  rewrite close_tm_identity in Hsem.
  exact ((proj1 (proj2 (logical_good T _ He))) t Hsem).
Qed.

End SystemFNormalizationNondeterminismHardTask.
