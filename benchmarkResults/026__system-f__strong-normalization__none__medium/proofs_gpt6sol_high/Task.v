(** System F CBV strong-normalization benchmark, Medium variant.
    Features: none. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFNormalizationNoneMediumTask.

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

  | tm_tapp : tm -> ty -> tm.

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
  end.

Fixpoint tm_subst (x : atom) (s t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar y => if Nat.eqb x y then s else tm_fvar y
  | tm_abs T t1 => tm_abs T (tm_subst x s t1)
  | tm_app t1 t2 => tm_app (tm_subst x s t1) (tm_subst x s t2)
  | tm_tabs t1 => tm_tabs (tm_subst x s t1)
  | tm_tapp t1 T => tm_tapp (tm_subst x s t1) T
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
      lc_tm_at K k (tm_tapp t T).

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
      has_type Delta Gamma (tm_tapp t U) (open_ty T U).

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
  end.

Definition expression_relation eta rho T t :=
  expression_lifting (value_relation eta rho T) t.

Definition related_substitution (rho : relation_env) (Gamma : context)
    (gamma : term_substitution) : Prop :=
  forall x T, lookup_context x Gamma = Some T -> value_relation [] rho T (gamma x).


Lemma lc_ty_weaken : forall K T, lc_ty_at K T ->
  forall K', K <= K' -> lc_ty_at K' T.
Proof.
  intros K T H. induction H; intros K' Hle.
  - apply lc_ty_bvar. lia.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; eauto.
  - apply lc_ty_all. apply IHlc_ty_at. lia.
Qed.

Lemma lc_tm_weaken : forall K k t, lc_tm_at K k t ->
  forall K' k', K <= K' -> k <= k' -> lc_tm_at K' k' t.
Proof.
  intros K k t H. induction H; intros K' k' HK Hk.
  - apply lc_tm_bvar. lia.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + eapply lc_ty_weaken; eauto.
    + apply IHlc_tm_at; lia.
  - apply lc_tm_app; eauto.
  - apply lc_tm_tabs. apply IHlc_tm_at; lia.
  - apply lc_tm_tapp.
    + apply IHlc_tm_at; lia.
    + eapply lc_ty_weaken; eauto.
Qed.

Lemma lc_ty_open : forall T K U,
  lc_ty_at (S K) T -> locally_closed_ty U ->
  lc_ty_at K (open_ty_rec K U T).
Proof.
  induction T; intros K U HT HU; inversion HT; subst; simpl.
  - destruct (Nat.eqb K n) eqn:E.
    + eapply lc_ty_weaken; eauto. lia.
    + apply Nat.eqb_neq in E. constructor. lia.
  - constructor.
  - constructor; eauto.
  - constructor. eapply IHT; eauto.
Qed.

Lemma lc_tm_open : forall t K k u,
  lc_tm_at K (S k) t -> locally_closed_tm u ->
  lc_tm_at K k (open_tm_rec k u t).
Proof.
  induction t; intros K k u HT HU; inversion HT; subst; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + eapply lc_tm_weaken; eauto; lia.
    + apply Nat.eqb_neq in E. constructor. lia.
  - constructor.
  - constructor; eauto.
  - constructor; eauto.
  - constructor. eapply IHt; eauto.
  - constructor; eauto.
Qed.

Lemma lc_tm_ty_open : forall t K k U,
  lc_tm_at (S K) k t -> locally_closed_ty U ->
  lc_tm_at K k (open_tm_ty_rec K U t).
Proof.
  induction t; intros K k U HT HU; inversion HT; subst; simpl.
  - constructor; assumption.
  - constructor.
  - constructor.
    + eapply lc_ty_open; eauto.
    + eapply IHt; eauto.
  - constructor; eauto.
  - constructor. eapply IHt; eauto.
  - constructor; eauto. eapply lc_ty_open; eauto.
Qed.

Lemma step_lc : forall t u,
  t --> u -> locally_closed_tm u.
Proof.
  intros t u H. induction H.
  - inversion H; subst. eapply lc_tm_open; eauto.
    inversion H0; subst; assumption.
  - constructor; auto.
  - constructor; auto. destruct H; assumption.
  - inversion H; subst. eapply lc_tm_ty_open; eauto.
  - constructor; auto.
Qed.

Lemma value_relation_value : forall eta rho T v,
  value_relation eta rho T v -> value v.
Proof.
  induction T; simpl; intros v H.
  - destruct (nth_error eta n) as [a|] eqn:E; [exact (candidate_values a v H)|contradiction].
  - destruct (rho a) as [c|] eqn:E; [exact (candidate_values c v H)|contradiction].
  - exact (proj1 H).
  - exact (proj1 H).
Qed.

Lemma value_no_step : forall v u, value v -> v --> u -> False.
Proof.
  intros v u Hv Hs. inversion Hv; subst; inversion Hs.
Qed.

Lemma value_sn : forall v, value v -> strongly_normalizing v.
Proof.
  intros v Hv. constructor. intros u Hs. exfalso. eapply value_no_step; [exact Hv | exact Hs].
Qed.

Lemma multi_step_left : forall t u v, t --> u -> u -->* v -> t -->* v.
Proof. intros; econstructor; eauto. Qed.

Lemma expression_value : forall R v, value v -> R v -> expression_lifting R v.
Proof.
  intros R v Hv HR. split; [destruct Hv; assumption|].
  split; [apply value_sn; assumption|].
  intros w Hm Hw. destruct Hm as [|x y z Hstep Hrest].
  - exact HR.
  - exfalso. eapply value_no_step; [exact Hv | exact Hstep].
Qed.

Lemma expression_step : forall R t u,
  expression_lifting R t -> t --> u -> expression_lifting R u.
Proof.
  intros R t u [Hlc [Hsn Hrel]] Hstep.
  split.
  - eapply step_lc; eauto.
  - split.
    + inversion Hsn; subst; eauto.
    + intros v Hm Hv. apply Hrel; auto. econstructor; eauto.
Qed.

Lemma step_deterministic : forall t u v,
  t --> u -> t --> v -> u = v.
Proof.
  intros t u v H. revert v.
  induction H; intros v0 Hv; inversion Hv; subst; eauto;
    try solve [f_equal; eauto];
    try match goal with
      | Hs : tm_abs _ _ --> _ |- _ =>
          exfalso; eapply value_no_step; [constructor; eassumption | exact Hs]
      | Hs : tm_tabs _ --> _ |- _ =>
          exfalso; eapply value_no_step; [constructor; eassumption | exact Hs]
      | Hs : ?w --> _, Hw : value ?w |- _ =>
          exfalso; eapply value_no_step; [exact Hw | exact Hs]
    end.
Qed.

Lemma expression_backward : forall R t u,
  locally_closed_tm t -> t --> u -> expression_lifting R u ->
  expression_lifting R t.
Proof.
  intros R t u Hlc Hstep [Hlu [Hsu Hru]].
  split; [exact Hlc|]. split.
  - constructor. intros w Htw. rewrite <- (step_deterministic _ _ _ Hstep Htw). exact Hsu.
  - intros v Hm Hv. inversion Hm; subst.
    + exfalso. inversion Hstep; subst; inversion Hv.
    + assert (y = u) by (eapply step_deterministic; eauto). subst.
      apply Hru; auto.
Qed.

Lemma lifting_iff : forall R S t,
  (forall v, R v <-> S v) ->
  expression_lifting R t <-> expression_lifting S t.
Proof.
  intros R S t Hiff. unfold expression_lifting. firstorder.
Qed.

Lemma value_relation_eta : forall T k eta eta' rho v,
  lc_ty_at k T ->
  (forall i, i < k -> nth_error eta i = nth_error eta' i) ->
  (value_relation eta rho T v <-> value_relation eta' rho T v).
Proof.
  induction T; intros k eta eta' rho v Hlc Hag; simpl.
  - inversion Hlc; subst. rewrite (Hag n H1). tauto.
  - tauto.
  - inversion Hlc as [| | ? ? ? Hlc1 Hlc2 |]; subst.
    split.
    + intros [Hv [U [body [Heq Hfun]]]].
      split; [exact Hv|]. exists U, body. split; [exact Heq|].
      intros arg Harg.
      apply (proj1 (lifting_iff _ _ _ (fun w => IHT2 _ _ _ _ _ Hlc2 Hag))).
      apply Hfun. apply (proj2 (IHT1 _ _ _ _ _ Hlc1 Hag)); exact Harg.
    + intros [Hv [U [body [Heq Hfun]]]].
      split; [exact Hv|]. exists U, body. split; [exact Heq|].
      intros arg Harg.
      apply (proj2 (lifting_iff _ _ _ (fun w => IHT2 _ _ _ _ _ Hlc2 Hag))).
      apply Hfun. apply (proj1 (IHT1 _ _ _ _ _ Hlc1 Hag)); exact Harg.
  - inversion Hlc as [| | | ? ? Hbody]; subst.
    split.
    + intros [Hv [body [Heq Hfun]]].
      split; [exact Hv|]. exists body. split; [exact Heq|].
      intros U a HU.
      assert (Hag' : forall i, i < S k ->
        nth_error (a :: eta) i = nth_error (a :: eta') i).
      { intros [|j] Hi; simpl; auto. apply Hag. lia. }
      apply (proj1 (lifting_iff _ _ _ (fun w => IHT _ _ _ _ _ Hbody Hag'))).
      apply Hfun; exact HU.
    + intros [Hv [body [Heq Hfun]]].
      split; [exact Hv|]. exists body. split; [exact Heq|].
      intros U a HU.
      assert (Hag' : forall i, i < S k ->
        nth_error (a :: eta) i = nth_error (a :: eta') i).
      { intros [|j] Hi; simpl; auto. apply Hag. lia. }
      apply (proj2 (lifting_iff _ _ _ (fun w => IHT _ _ _ _ _ Hbody Hag'))).
      apply Hfun; exact HU.
Qed.

Definition semantic_candidate eta rho U : value_candidate :=
  {| candidate_relation := value_relation eta rho U;
     candidate_values := value_relation_value eta rho U |}.

Fixpoint insert_candidate (k : nat) (c : value_candidate)
    (eta : list value_candidate) : list value_candidate :=
  match k, eta with
  | 0, _ => c :: eta
  | S j, a :: rest => a :: insert_candidate j c rest
  | S _, [] => [c]
  end.

Lemma nth_insert_lt : forall k eta c i,
  k <= length eta -> i < k ->
  nth_error (insert_candidate k c eta) i = nth_error eta i.
Proof.
  induction k; intros eta c i Hlen Hi; [lia|].
  destruct eta as [|a eta]; [simpl in Hlen; lia|].
  destruct i as [|i]; simpl; auto. apply IHk; simpl in Hlen; lia.
Qed.

Lemma nth_insert_eq : forall k eta c,
  k <= length eta -> nth_error (insert_candidate k c eta) k = Some c.
Proof.
  induction k; intros eta c Hlen; [reflexivity|].
  destruct eta as [|a eta]; [simpl in Hlen; lia|].
  simpl. apply IHk. simpl in Hlen. lia.
Qed.

Lemma value_relation_open : forall T k eta rho U c v,
  lc_ty_at (S k) T -> locally_closed_ty U -> k <= length eta ->
  (forall w, candidate_relation c w <-> value_relation eta rho U w) ->
  (value_relation eta rho (open_ty_rec k U T) v <->
   value_relation (insert_candidate k c eta) rho T v).
Proof.
  induction T; intros k eta rho U c v Hlc HU Hlen Hc; inversion Hlc; subst; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst.
      rewrite nth_insert_eq by exact Hlen. simpl. symmetry. apply Hc.
    + apply Nat.eqb_neq in E. rewrite nth_insert_lt by lia. tauto.
  - tauto.
  - split.
    + intros [Hv [W [body [Heq Hfun]]]].
      split; [exact Hv|]. exists W, body. split; [exact Heq|].
      intros arg Harg.
      apply (proj1 (lifting_iff _ _ _
        (fun w => IHT2 _ _ _ _ _ _ H3 HU Hlen Hc))).
      apply Hfun. apply (proj2 (IHT1 _ _ _ _ _ _ H2 HU Hlen Hc)); exact Harg.
    + intros [Hv [W [body [Heq Hfun]]]].
      split; [exact Hv|]. exists W, body. split; [exact Heq|].
      intros arg Harg.
      apply (proj2 (lifting_iff _ _ _
        (fun w => IHT2 _ _ _ _ _ _ H3 HU Hlen Hc))).
      apply Hfun. apply (proj1 (IHT1 _ _ _ _ _ _ H2 HU Hlen Hc)); exact Harg.
  - split.
    + intros [Hv [body [Heq Hfun]]].
      split; [exact Hv|]. exists body. split; [exact Heq|].
      intros W a HW.
      assert (Hc' : forall w, candidate_relation c w <->
        value_relation (a :: eta) rho U w).
      { intro w. transitivity (value_relation eta rho U w).
        - apply Hc.
        - apply value_relation_eta with (k:=0); auto. intros i Hi; lia. }
      apply (proj1 (lifting_iff _ _ _
        (fun w => IHT (S k) (a :: eta) rho U c w H1 HU (le_n_S _ _ Hlen) Hc'))).
      apply Hfun; exact HW.
    + intros [Hv [body [Heq Hfun]]].
      split; [exact Hv|]. exists body. split; [exact Heq|].
      intros W a HW.
      assert (Hc' : forall w, candidate_relation c w <->
        value_relation (a :: eta) rho U w).
      { intro w. transitivity (value_relation eta rho U w).
        - apply Hc.
        - apply value_relation_eta with (k:=0); auto. intros i Hi; lia. }
      apply (proj2 (lifting_iff _ _ _
        (fun w => IHT (S k) (a :: eta) rho U c w H1 HU (le_n_S _ _ Hlen) Hc'))).
      apply Hfun; exact HW.
Qed.

Lemma expression_app : forall eta rho T1 T2 t1 t2,
  expression_relation eta rho (Ty_Arrow T1 T2) t1 ->
  expression_relation eta rho T1 t2 ->
  expression_relation eta rho T2 (tm_app t1 t2).
Proof.
  intros eta rho T1 T2 t1 t2 H1 H2.
  destruct H1 as [Hlc1 [Hsn1 Hr1]].
  revert Hlc1 Hr1 t2 H2.
  induction Hsn1 as [t1 Hsteps1 IH1]; intros Hlc1 Hr1 t2 H2.
  destruct H2 as [Hlc2 [Hsn2 Hr2]].
  revert Hlc2 Hr2.
  induction Hsn2 as [t2 Hsteps2 IH2]; intros Hlc2 Hr2.
  assert (Hnext : forall w, tm_app t1 t2 --> w ->
      expression_relation eta rho T2 w).
  { intros w Hw. inversion Hw; subst.
    - specialize (Hr1 _ (multi_refl _) (v_abs _ _ Hlc1)).
      destruct Hr1 as [_ [U [body [Heq Hfun]]]].
      inversion Heq; subst.
      apply Hfun. apply Hr2; [constructor|assumption].
    - pose proof (expression_step _ _ _ (conj Hlc1 (conj (SN_intro _ Hsteps1) Hr1)) H1)
        as [Hlc' [Hsn' Hr']].
      apply (IH1 _ H1 Hlc' Hr' t2).
      exact (conj Hlc2 (conj (SN_intro _ Hsteps2) Hr2)).
    - pose proof (expression_step _ _ _ (conj Hlc2 (conj (SN_intro _ Hsteps2) Hr2)) H3)
        as [Hlc' [Hsn' Hr']].
      apply (IH2 _ H3 Hlc' Hr').
  }
  split.
  - constructor; assumption.
  - split.
    + constructor. intros w Hw. destruct (Hnext _ Hw) as [_ [Hsn _]]. exact Hsn.
    + intros v Hm Hv. inversion Hm; subst.
      * inversion Hv.
      * match goal with
        | Hstep : tm_app t1 t2 --> ?w |- _ =>
            destruct (Hnext w Hstep) as [_ [_ Hrel]]; eapply Hrel; eauto
        end.
Qed.

Lemma expression_tapp : forall eta rho T t U W,
  lc_ty_at 1 T -> locally_closed_ty U -> locally_closed_ty W ->
  expression_relation eta rho (Ty_All T) t ->
  expression_relation eta rho (open_ty T U) (tm_tapp t W).
Proof.
  intros eta rho T t U W HT HU HW Hexpr.
  destruct Hexpr as [Hlc [Hsn Hr]].
  revert Hlc Hr.
  induction Hsn as [t Hsteps IH]; intros Hlc Hr.
  assert (Hnext : forall w, tm_tapp t W --> w ->
      expression_relation eta rho (open_ty T U) w).
  { intros w Hw. inversion Hw; subst.
    - specialize (Hr _ (multi_refl _) (v_tabs _ Hlc)).
      destruct Hr as [_ [body [Heq Hfun]]]. inversion Heq; subst.
      pose proof (Hfun W (semantic_candidate eta rho U) HW) as Hbody.
      apply (proj2 (lifting_iff _ _ _
        (fun v => value_relation_open T 0 eta rho U
          (semantic_candidate eta rho U) v HT HU (Nat.le_0_l _)
          (fun z => iff_refl _)))) in Hbody.
      exact Hbody.
    - pose proof (expression_step _ _ _
        (conj Hlc (conj (SN_intro _ Hsteps) Hr)) H1)
        as [Hlc' [Hsn' Hr']].
      apply (IH _ H1 Hlc' Hr').
  }
  split.
  - constructor; assumption.
  - split.
    + constructor. intros w Hw. destruct (Hnext _ Hw) as [_ [Hsn' _]]. exact Hsn'.
    + intros v Hm Hv. inversion Hm; subst.
      * inversion Hv.
      * match goal with
        | Hstep : tm_tapp t W --> ?w |- _ =>
            destruct (Hnext w Hstep) as [_ [_ Hrel]]; eapply Hrel; eauto
        end.
Qed.

Fixpoint fv_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ => [] | tm_fvar x => [x]
  | tm_abs _ t => fv_tm t
  | tm_app t u => fv_tm t ++ fv_tm u
  | tm_tabs t => fv_tm t
  | tm_tapp t _ => fv_tm t
  end.

Fixpoint ftv_ty (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => [] | Ty_FVar X => [X]
  | Ty_Arrow A B => ftv_ty A ++ ftv_ty B
  | Ty_All A => ftv_ty A
  end.

Fixpoint ftv_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_fvar _ => []
  | tm_abs T t => ftv_ty T ++ ftv_tm t
  | tm_app t u => ftv_tm t ++ ftv_tm u
  | tm_tabs t => ftv_tm t
  | tm_tapp t T => ftv_tm t ++ ftv_ty T
  end.

Definition ftv_context (Gamma : context) : list atom :=
  concat (map (fun p => ftv_ty (snd p)) Gamma).

Definition fresh (L : list atom) : atom :=
  S (fold_right Nat.max 0 L).

Lemma in_le_max : forall L x,
  In x L -> x <= fold_right Nat.max 0 L.
Proof.
  induction L as [|y L IH]; simpl; intros x Hin.
  - contradiction.
  - destruct Hin as [->|Hin]; [lia|]. specialize (IH _ Hin). lia.
Qed.

Lemma fresh_notin : forall L, ~ In (fresh L) L.
Proof.
  intros L Hin. unfold fresh in Hin. pose proof (in_le_max _ _ Hin). lia.
Qed.

Lemma lc_ty_open_inverse : forall T K U,
  lc_ty_at K (open_ty_rec K U T) -> lc_ty_at (S K) T.
Proof.
  induction T; intros K U Hlc; simpl in Hlc.
  - destruct (Nat.eqb K n) eqn:E.
    + apply Nat.eqb_eq in E. subst. constructor. lia.
    + inversion Hlc; subst. constructor. lia.
  - constructor.
  - inversion Hlc; subst. constructor; eauto.
  - inversion Hlc; subst. constructor. eapply IHT; eauto.
Qed.

Lemma lc_tm_open_inverse : forall t K k u,
  lc_tm_at K k (open_tm_rec k u t) -> lc_tm_at K (S k) t.
Proof.
  induction t; intros K k u Hlc; simpl in Hlc.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. constructor. lia.
    + inversion Hlc; subst. constructor. lia.
  - constructor.
  - inversion Hlc; subst. constructor; eauto.
  - inversion Hlc; subst. constructor; eauto.
  - inversion Hlc; subst. constructor; eauto.
  - inversion Hlc; subst. constructor; eauto.
Qed.

Lemma lc_tm_ty_open_inverse : forall t K k U,
  lc_tm_at K k (open_tm_ty_rec K U t) -> lc_tm_at (S K) k t.
Proof.
  induction t; intros K k U Hlc; simpl in Hlc.
  - inversion Hlc; subst. constructor; assumption.
  - constructor.
  - inversion Hlc; subst. constructor.
    + eapply lc_ty_open_inverse; eauto.
    + eapply IHt; eauto.
  - inversion Hlc; subst. constructor; eauto.
  - inversion Hlc; subst. constructor; eauto.
  - inversion Hlc; subst. constructor; eauto.
    eapply lc_ty_open_inverse; eauto.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H. induction H.
  - constructor.
  - constructor; assumption.
  - pose (X := fresh L).
    assert (Hfresh : ~ In X L) by (unfold X; apply fresh_notin).
    pose proof (H0 X Hfresh) as Hopened.
    constructor. eapply lc_ty_open_inverse. exact Hopened.
Qed.

Lemma typing_regular : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t /\ locally_closed_ty T.
Proof.
  intros Delta Gamma t T H. induction H.
  - split; [constructor|]. eapply wf_ty_lc; eauto.
  - pose (x := fresh L).
    assert (Hfresh : ~ In x L) by (unfold x; apply fresh_notin).
    destruct (H1 x Hfresh) as [Hbody HT2].
    split.
    + apply lc_tm_abs.
      * eapply wf_ty_lc; eauto.
      * eapply lc_tm_open_inverse. exact Hbody.
    + constructor; [eapply wf_ty_lc; eauto|exact HT2].
  - destruct IHhas_type1 as [Hlc1 Hty1].
    destruct IHhas_type2 as [Hlc2 Hty2].
    split; [constructor; assumption|]. inversion Hty1; subst; assumption.
  - pose (X := fresh L).
    assert (Hfresh : ~ In X L) by (unfold X; apply fresh_notin).
    destruct (H0 X Hfresh) as [Hbody HT].
    split.
    + constructor. eapply lc_tm_ty_open_inverse. exact Hbody.
    + constructor. eapply lc_ty_open_inverse. exact HT.
  - destruct IHhas_type as [Hlc Hty].
    pose proof (wf_ty_lc _ _ H0) as HU.
    inversion Hty; subst.
    split.
    + constructor; assumption.
    + unfold open_ty. eapply lc_ty_open; eauto.
Qed.

Lemma instantiate_ty_lc : forall theta K T,
  type_substitution_closed theta -> lc_ty_at K T ->
  lc_ty_at K (instantiate_ty theta T).
Proof.
  intros theta K T Htheta Hlc. induction Hlc; simpl.
  - constructor; assumption.
  - eapply lc_ty_weaken; [apply Htheta|lia].
  - constructor; assumption.
  - constructor; assumption.
Qed.

Lemma instantiate_lc : forall theta gamma K k t,
  type_substitution_closed theta -> term_substitution_closed gamma ->
  lc_tm_at K k t -> lc_tm_at K k (instantiate theta gamma t).
Proof.
  intros theta gamma K k t Htheta Hgamma Hlc. induction Hlc; simpl.
  - constructor; assumption.
  - eapply lc_tm_weaken; [apply Hgamma|lia|lia].
  - constructor.
    + eapply instantiate_ty_lc; eauto.
    + exact IHHlc.
  - constructor; assumption.
  - constructor; assumption.
  - constructor.
    + exact IHHlc.
    + eapply instantiate_ty_lc; eauto.
Qed.

Lemma value_relation_rho : forall T eta rho rho' v,
  (forall X, In X (ftv_ty T) -> rho X = rho' X) ->
  (value_relation eta rho T v <-> value_relation eta rho' T v).
Proof.
  induction T; intros eta rho rho' v Hag; simpl.
  - tauto.
  - rewrite (Hag a (or_introl eq_refl)). tauto.
  - split.
    + intros [Hv [U [body [Heq Hfun]]]].
      split; [exact Hv|]. exists U, body. split; [exact Heq|].
      intros arg Harg.
      apply (proj1 (lifting_iff _ _ _
        (fun w => IHT2 _ _ _ _ (fun X HX => Hag X (in_or_app _ _ _ (or_intror HX)))))).
      apply Hfun.
      apply (proj2 (IHT1 _ _ _ _
        (fun X HX => Hag X (in_or_app _ _ _ (or_introl HX))))); exact Harg.
    + intros [Hv [U [body [Heq Hfun]]]].
      split; [exact Hv|]. exists U, body. split; [exact Heq|].
      intros arg Harg.
      apply (proj2 (lifting_iff _ _ _
        (fun w => IHT2 _ _ _ _ (fun X HX => Hag X (in_or_app _ _ _ (or_intror HX)))))).
      apply Hfun.
      apply (proj1 (IHT1 _ _ _ _
        (fun X HX => Hag X (in_or_app _ _ _ (or_introl HX))))); exact Harg.
  - split.
    + intros [Hv [body [Heq Hfun]]].
      split; [exact Hv|]. exists body. split; [exact Heq|].
      intros U a HU.
      apply (proj1 (lifting_iff _ _ _
        (fun w => IHT (a :: eta) rho rho' w Hag))).
      apply Hfun; exact HU.
    + intros [Hv [body [Heq Hfun]]].
      split; [exact Hv|]. exists body. split; [exact Heq|].
      intros U a HU.
      apply (proj2 (lifting_iff _ _ _
        (fun w => IHT (a :: eta) rho rho' w Hag))).
      apply Hfun; exact HU.
Qed.

Lemma type_open_relation : forall T eta rho X c v,
  lc_ty_at 1 T -> ~ In X (ftv_ty T) ->
  (value_relation eta (relation_update rho X c)
     (open_ty T (Ty_FVar X)) v <->
   value_relation (c :: eta) rho T v).
Proof.
  intros T eta rho X c v HT Hfresh.
  transitivity (value_relation (c :: eta) (relation_update rho X c) T v).
  - unfold open_ty.
    apply value_relation_open with (k:=0) (U:=Ty_FVar X); auto.
    + constructor.
    + simpl. lia.
    + intro w. unfold relation_update. simpl.
      rewrite Nat.eqb_refl. tauto.
  - apply value_relation_rho. intros Y HY.
    unfold relation_update. destruct (Nat.eqb X Y) eqn:E; auto.
    apply Nat.eqb_eq in E. subst. contradiction.
Qed.

Definition update_gamma (gamma : term_substitution) (x : atom) (v : tm) : term_substitution :=
  fun y => if Nat.eqb x y then v else gamma y.

Definition update_theta (theta : type_substitution) (X : atom) (U : ty) : type_substitution :=
  fun Y => if Nat.eqb X Y then U else theta Y.

Lemma open_ty_above : forall K T U j,
  lc_ty_at K T -> K <= j -> open_ty_rec j U T = T.
Proof.
  intros K T U j Hlc. revert j.
  induction Hlc; intros j Hle; simpl.
  - assert (Hneq : j <> i) by lia. apply Nat.eqb_neq in Hneq.
    rewrite Hneq. reflexivity.
  - reflexivity.
  - rewrite IHHlc1, IHHlc2 by lia. reflexivity.
  - rewrite IHHlc by lia. reflexivity.
Qed.

Lemma open_ty_closed : forall T U k,
  locally_closed_ty T -> open_ty_rec k U T = T.
Proof.
  intros T U k Hlc. eapply open_ty_above; eauto; lia.
Qed.

Lemma open_tm_above : forall K k t u j,
  lc_tm_at K k t -> k <= j -> open_tm_rec j u t = t.
Proof.
  intros K k t u j Hlc. revert j.
  induction Hlc; intros j Hle; simpl.
  - assert (Hneq : j <> i) by lia. apply Nat.eqb_neq in Hneq.
    rewrite Hneq. reflexivity.
  - reflexivity.
  - rewrite IHHlc by lia. reflexivity.
  - rewrite IHHlc1, IHHlc2 by lia. reflexivity.
  - rewrite IHHlc by lia. reflexivity.
  - rewrite IHHlc by lia. reflexivity.
Qed.

Lemma open_tm_closed : forall t u k,
  locally_closed_tm t -> open_tm_rec k u t = t.
Proof.
  intros t u k Hlc. eapply open_tm_above; eauto; lia.
Qed.

Lemma open_tm_ty_above : forall K k t U j,
  lc_tm_at K k t -> K <= j -> open_tm_ty_rec j U t = t.
Proof.
  intros K k t U j Hlc. revert j.
  induction Hlc; intros j Hle; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite (open_ty_above K T U j H Hle). rewrite IHHlc by lia. reflexivity.
  - rewrite IHHlc1, IHHlc2 by lia. reflexivity.
  - rewrite IHHlc by lia. reflexivity.
  - rewrite IHHlc by lia. rewrite (open_ty_above K T U j H Hle). reflexivity.
Qed.

Lemma open_tm_ty_closed : forall t U k,
  locally_closed_tm t -> open_tm_ty_rec k U t = t.
Proof.
  intros t U k Hlc. eapply open_tm_ty_above; eauto; lia.
Qed.

Lemma update_gamma_closed : forall gamma x v,
  term_substitution_closed gamma -> locally_closed_tm v ->
  term_substitution_closed (update_gamma gamma x v).
Proof.
  intros gamma x v Hg Hv y. unfold update_gamma.
  destruct (Nat.eqb x y); auto.
Qed.

Lemma update_theta_closed : forall theta X U,
  type_substitution_closed theta -> locally_closed_ty U ->
  type_substitution_closed (update_theta theta X U).
Proof.
  intros theta X U Ht HU Y. unfold update_theta.
  destruct (Nat.eqb X Y); auto.
Qed.

Lemma not_in_app_split : forall (A : Type) (x : A) l r,
  ~ In x (l ++ r) -> ~ In x l /\ ~ In x r.
Proof.
  intros A x l r H. split; intro Hi; apply H; apply in_or_app; auto.
Qed.

Lemma instantiate_ty_open : forall T theta X U k,
  type_substitution_closed theta -> locally_closed_ty U ->
  ~ In X (ftv_ty T) ->
  instantiate_ty (update_theta theta X U) (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k U (instantiate_ty theta T).
Proof.
  induction T; intros theta X U k Htheta HU Hfresh; simpl in *.
  - destruct (Nat.eqb k n); simpl.
    + unfold update_theta. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - assert (X <> a) by (intro E; subst; apply Hfresh; auto).
    unfold update_theta. apply Nat.eqb_neq in H. rewrite H.
    symmetry. apply open_ty_closed. apply Htheta.
  - apply not_in_app_split in Hfresh as [H1 H2].
    rewrite IHT1, IHT2 by assumption. reflexivity.
  - rewrite IHT by assumption. reflexivity.
Qed.

Lemma instantiate_tm_open : forall t theta gamma x v k,
  term_substitution_closed gamma -> locally_closed_tm v ->
  ~ In x (fv_tm t) ->
  instantiate theta (update_gamma gamma x v)
    (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k v (instantiate theta gamma t).
Proof.
  induction t; intros theta gamma x v k Hgamma Hv Hfresh; simpl in *.
  - destruct (Nat.eqb k n); simpl.
    + unfold update_gamma. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - assert (x <> a) by (intro E; subst; apply Hfresh; auto).
    unfold update_gamma. apply Nat.eqb_neq in H. rewrite H.
    symmetry. apply open_tm_closed. apply Hgamma.
  - rewrite IHt by assumption. reflexivity.
  - apply not_in_app_split in Hfresh as [H1 H2].
    rewrite IHt1, IHt2 by assumption. reflexivity.
  - rewrite IHt by assumption. reflexivity.
  - rewrite IHt by assumption. reflexivity.
Qed.

Lemma instantiate_tm_ty_open : forall t theta gamma X U k,
  type_substitution_closed theta -> term_substitution_closed gamma ->
  locally_closed_ty U -> ~ In X (ftv_tm t) ->
  instantiate (update_theta theta X U) gamma
    (open_tm_ty_rec k (Ty_FVar X) t) =
  open_tm_ty_rec k U (instantiate theta gamma t).
Proof.
  induction t; intros theta gamma X U k Htheta Hgamma HU Hfresh; simpl in *.
  - reflexivity.
  - symmetry. apply open_tm_ty_closed. apply Hgamma.
  - apply not_in_app_split in Hfresh as [H1 H2].
    rewrite instantiate_ty_open by assumption.
    rewrite IHt by assumption. reflexivity.
  - apply not_in_app_split in Hfresh as [H1 H2].
    rewrite IHt1, IHt2 by assumption. reflexivity.
  - rewrite IHt by assumption. reflexivity.
  - apply not_in_app_split in Hfresh as [H1 H2].
    rewrite IHt by assumption.
    rewrite instantiate_ty_open by assumption. reflexivity.
Qed.

Definition related_subst eta rho Gamma gamma : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    value_relation eta rho T (gamma x).

Lemma lookup_ftv_context : forall Gamma x T X,
  lookup_context x Gamma = Some T -> In X (ftv_ty T) ->
  In X (ftv_context Gamma).
Proof.
  induction Gamma as [|[y S] Gamma IH]; intros x T X Hlookup Hin;
    simpl in Hlookup; [discriminate|].
  unfold ftv_context. simpl. apply in_or_app.
  destruct (Nat.eqb x y) eqn:E.
  - inversion Hlookup; subst. left. exact Hin.
  - right. apply IH with (x:=x) (T:=T); assumption.
Qed.

Lemma related_update_gamma : forall eta rho Gamma gamma x T v,
  related_subst eta rho Gamma gamma ->
  value_relation eta rho T v ->
  related_subst eta rho (update Gamma x T) (update_gamma gamma x v).
Proof.
  intros eta rho Gamma gamma x T v Hrel Hv y S Hlookup.
  unfold update in Hlookup. simpl in Hlookup.
  unfold update_gamma.
  replace (Nat.eqb x y) with (Nat.eqb y x) by apply Nat.eqb_sym.
  destruct (Nat.eqb y x) eqn:E.
  - inversion Hlookup; subst. exact Hv.
  - apply Hrel. exact Hlookup.
Qed.

Lemma related_update_rho : forall eta rho Gamma gamma X c,
  ~ In X (ftv_context Gamma) ->
  related_subst eta rho Gamma gamma ->
  related_subst eta (relation_update rho X c) Gamma gamma.
Proof.
  intros eta rho Gamma gamma X c Hfresh Hrel x T Hlookup.
  assert (Hag : forall Y, In Y (ftv_ty T) ->
      rho Y = relation_update rho X c Y).
  { intros Y HY. unfold relation_update.
    destruct (Nat.eqb X Y) eqn:E; auto.
    apply Nat.eqb_eq in E. subst.
    exfalso. apply Hfresh. eapply lookup_ftv_context; eauto. }
  apply (proj1 (value_relation_rho T eta rho
    (relation_update rho X c) (gamma x) Hag)).
  apply Hrel. exact Hlookup.
Qed.

Theorem fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall theta gamma rho eta,
    type_substitution_closed theta ->
    term_substitution_closed gamma ->
    related_subst eta rho Gamma gamma ->
    expression_relation eta rho T (instantiate theta gamma t).
Proof.
  intros Delta Gamma t T Htyping.
  induction Htyping; intros theta gamma rho eta Htheta Hgamma Hrel; simpl.
  - apply expression_value.
    + apply value_relation_value with (eta:=eta) (rho:=rho) (T:=T).
      apply Hrel. exact H.
    + apply Hrel. exact H.
  - assert (Hlc : locally_closed_tm
        (tm_abs (instantiate_ty theta T1) (instantiate theta gamma t2))).
    { change (locally_closed_tm (instantiate theta gamma (tm_abs T1 t2))).
      eapply instantiate_lc; eauto.
      apply (proj1 (typing_regular _ _ _ _
        (T_Abs L Delta Gamma T1 t2 T2 H H0))). }
    assert (Hv : value
        (tm_abs (instantiate_ty theta T1) (instantiate theta gamma t2)))
      by (constructor; exact Hlc).
    apply expression_value; [exact Hv|].
    simpl. split; [exact Hv|].
    exists (instantiate_ty theta T1), (instantiate theta gamma t2).
    split; [reflexivity|].
    intros arg Harg.
    pose (x := fresh (L ++ fv_tm t2)).
    assert (HxL : ~ In x L).
    { unfold x. pose proof (fresh_notin (L ++ fv_tm t2)) as Hf.
      intro Hin. apply Hf. apply in_or_app. left. exact Hin. }
    assert (Hxbody : ~ In x (fv_tm t2)).
    { unfold x. pose proof (fresh_notin (L ++ fv_tm t2)) as Hf.
      intro Hin. apply Hf. apply in_or_app. right. exact Hin. }
    pose proof (value_relation_value eta rho T1 arg Harg) as Hargval.
    assert (Harglc : locally_closed_tm arg) by (destruct Hargval; assumption).
    unfold open_tm.
    rewrite <- (instantiate_tm_open t2 theta gamma x arg 0 Hgamma Harglc Hxbody).
    apply (H1 x HxL theta (update_gamma gamma x arg) rho eta Htheta).
    + apply update_gamma_closed; assumption.
    + apply related_update_gamma; assumption.
  - eapply expression_app; eauto.
  - assert (Hlc : locally_closed_tm (tm_tabs (instantiate theta gamma t))).
    { change (locally_closed_tm (instantiate theta gamma (tm_tabs t))).
      eapply instantiate_lc; eauto.
      apply (proj1 (typing_regular _ _ _ _
        (T_TAbs L Delta Gamma t T H))). }
    assert (Hv : value (tm_tabs (instantiate theta gamma t)))
      by (constructor; exact Hlc).
    apply expression_value; [exact Hv|].
    simpl. split; [exact Hv|].
    exists (instantiate theta gamma t). split; [reflexivity|].
    intros U a HU.
    pose (X := fresh (L ++ ftv_tm t ++ ftv_ty T ++ ftv_context Gamma)).
    assert (HXall : ~ In X (L ++ ftv_tm t ++ ftv_ty T ++ ftv_context Gamma))
      by (unfold X; apply fresh_notin).
    assert (HXL : ~ In X L).
    { intro Hin. apply HXall. apply in_or_app. left. exact Hin. }
    assert (HXtm : ~ In X (ftv_tm t)).
    { intro Hin. apply HXall. apply in_or_app. right.
      apply in_or_app. left. exact Hin. }
    assert (HXty : ~ In X (ftv_ty T)).
    { intro Hin. apply HXall. apply in_or_app. right.
      apply in_or_app. right. apply in_or_app. left. exact Hin. }
    assert (HXgamma : ~ In X (ftv_context Gamma)).
    { intro Hin. apply HXall. apply in_or_app. right.
      apply in_or_app. right. apply in_or_app. right. exact Hin. }
    assert (HT : lc_ty_at 1 T).
    { pose proof (typing_regular _ _ _ _ (T_TAbs L Delta Gamma t T H)) as [_ Hty].
      inversion Hty; subst; assumption. }
    unfold open_tm_ty.
    rewrite <- (instantiate_tm_ty_open t theta gamma X U 0 Htheta Hgamma HU HXtm).
    pose proof (H0 X HXL (update_theta theta X U) gamma
      (relation_update rho X a) eta
      (update_theta_closed _ _ _ Htheta HU) Hgamma
      (related_update_rho _ _ _ _ _ _ HXgamma Hrel)) as Hbody.
    apply (proj1 (lifting_iff _ _ _
      (fun v => type_open_relation T eta rho X a v HT HXty))) in Hbody.
    exact Hbody.
  - eapply expression_tapp.
    + pose proof (typing_regular _ _ _ _ Htyping) as [_ Hty].
      inversion Hty; subst; assumption.
    + exact (wf_ty_lc Delta U H).
    + eapply instantiate_ty_lc; eauto. exact (wf_ty_lc Delta U H).
    + apply IHHtyping; assumption.
Qed.

Lemma instantiate_ty_id : forall T,
  instantiate_ty Ty_FVar T = T.
Proof.
  induction T; simpl; f_equal; assumption.
Qed.

Lemma instantiate_id : forall t,
  instantiate Ty_FVar tm_fvar t = t.
Proof.
  induction t; simpl; try rewrite instantiate_ty_id;
    try rewrite IHt; try rewrite IHt1, IHt2; reflexivity.
Qed.

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  intros t T Htyping.
  assert (Hrel : related_subst [] (fun _ => None) empty tm_fvar).
  { intros x U Hlookup. discriminate. }
  pose proof (fundamental [] empty t T Htyping
    Ty_FVar tm_fvar (fun _ => None) []
    (fun X => lc_ty_fvar 0 X)
    (fun x => lc_tm_fvar 0 0 x) Hrel) as Hexpr.
  rewrite instantiate_id in Hexpr.
  exact (proj1 (proj2 Hexpr)).
Qed.

End SystemFNormalizationNoneMediumTask.
