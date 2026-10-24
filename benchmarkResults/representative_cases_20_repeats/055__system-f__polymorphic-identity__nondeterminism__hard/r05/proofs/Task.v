(** System F parametricity benchmark, Hard variant.
    Features: nondeterminism. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFParametricityNondeterminismHardTask.

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


Hint Constructors lc_ty_at lc_tm_at value : core.

(** ================================================================== *)
(** * Infrastructure for the logical relation                          *)
(** ================================================================== *)

Definition VRel := tm -> tm -> Prop.

Definition DefaultRel : VRel := fun _ _ => False.

Fixpoint fvs_ty (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow T1 T2 => fvs_ty T1 ++ fvs_ty T2
  | Ty_All T1 => fvs_ty T1
  end.

Fixpoint fvs_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs T t1 => fvs_ty T ++ fvs_tm t1
  | tm_app t1 t2 => fvs_tm t1 ++ fvs_tm t2
  | tm_tabs t1 => fvs_tm t1
  | tm_tapp t1 T => fvs_tm t1 ++ fvs_ty T
  | tm_choice t1 t2 => fvs_tm t1 ++ fvs_tm t2
  end.

Definition fresh (L : list atom) : atom := S (fold_right max 0 L).

Lemma in_le_fold_max : forall (x : atom) L, In x L -> x <= fold_right max 0 L.
Proof.
  intros x L. induction L as [|a L IH].
  - intros Hin. simpl in Hin. destruct Hin.
  - intros Hin. simpl. destruct Hin as [-> | Hin].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; auto | apply Nat.le_max_r].
Qed.

Lemma fresh_gt : forall (x : atom) L, In x L -> x < fresh L.
Proof.
  intros x L Hin. unfold fresh. pose proof (in_le_fold_max x L Hin). lia.
Qed.

Lemma fresh_notin : forall L, ~ In (fresh L) L.
Proof.
  intros L Hin. pose proof (fresh_gt _ _ Hin). apply Nat.lt_irrefl in H. exact H.
Qed.

Lemma fresh_notin_1 : forall L1 L2, ~ In (fresh (L1 ++ L2)) L1.
Proof.
  intros L1 L2 Hin. apply (fresh_notin (L1 ++ L2)). apply in_or_app. left. exact Hin.
Qed.

Lemma fresh_notin_2 : forall L1 L2, ~ In (fresh (L1 ++ L2)) L2.
Proof.
  intros L1 L2 Hin. apply (fresh_notin (L1 ++ L2)). apply in_or_app. right. exact Hin.
Qed.

(** ** Monotonicity of the locally closed judgements *)

Lemma lc_ty_at_mono : forall T k k', k <= k' -> lc_ty_at k T -> lc_ty_at k' T.
Proof.
  induction T; intros k k' Hle H.
  - inversion H; subst. constructor. lia.
  - constructor.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor.
    eapply IHT with (k := S k); [lia | eassumption].
Qed.

Lemma lc_tm_at_mono_K : forall t K K' k, K <= K' -> lc_tm_at K k t -> lc_tm_at K' k t.
Proof.
  induction t; intros K K' k Hle H.
  - inversion H; subst. constructor. lia.
  - constructor.
  - inversion H; subst. constructor.
    + eapply lc_ty_at_mono; eauto.
    + eapply IHt; eauto.
  - inversion H; subst. constructor; eauto.
  - (* tabs *) inversion H; subst. constructor.
    eapply IHt with (K := S K) (K' := S K'); [lia | eassumption].
  - (* tapp *) inversion H; subst. constructor.
    + eapply IHt with (K := K) (K' := K'); [lia | eassumption].
    + eapply lc_ty_at_mono; eauto.
  - (* choice *) inversion H; subst. constructor; eauto.
Qed.

Lemma lc_tm_at_mono_k : forall t K k k', k <= k' -> lc_tm_at K k t -> lc_tm_at K k' t.
Proof.
  induction t; intros K k k' Hle H.
  - inversion H; subst. constructor. lia.
  - constructor.
  - inversion H; subst. constructor.
    + eauto.
    + eapply IHt with (k := S k) (k' := S k'); [lia | eassumption].
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor.
    eapply IHt with (k := k) (k' := k'); [lia | eassumption].
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor; eauto.
Qed.

(** ** Inversion of local closedness through opening *)

Lemma open_ty_rec_lc_inv : forall T k U,
  lc_ty_at 0 U -> lc_ty_at k (open_ty_rec k U T) -> lc_ty_at (S k) T.
Proof.
  induction T; intros k U HU H.
  - simpl in H. destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. constructor. lia.
    + inversion H; subst. constructor. lia.
  - simpl in H. inversion H. constructor.
  - simpl in H. inversion H; subst. constructor; eauto.
  - simpl in H. inversion H; subst. constructor. eapply IHT; eauto.
Qed.

Lemma open_ty_rec_lc_fwd : forall T k U,
  lc_ty_at 0 U -> lc_ty_at (S k) T -> lc_ty_at k (open_ty_rec k U T).
Proof.
  induction T; intros k U HU H.
  - simpl. destruct (Nat.eqb k n) eqn:E.
    + apply lc_ty_at_mono with (k := 0); auto. lia.
    + apply Nat.eqb_neq in E. inversion H; subst. constructor. lia.
  - simpl. constructor.
  - simpl. inversion H; subst. constructor; eauto.
  - simpl. inversion H; subst. constructor. eapply IHT; eauto.
Qed.

Lemma open_tm_rec_lc_inv : forall t K k s,
  lc_tm_at K 0 s -> lc_tm_at K k (open_tm_rec k s t) -> lc_tm_at K (S k) t.
Proof.
  induction t; intros K k s Hs H.
  - simpl in H. destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. constructor. lia.
    + inversion H; subst. constructor. lia.
  - simpl in H. inversion H. constructor.
  - simpl in H. inversion H; subst. constructor.
    + assumption.
    + eapply IHt; eauto.
  - simpl in H. inversion H; subst. constructor; eauto.
  - (* tabs *) simpl in H. inversion H; subst. constructor.
    assert (Hs' : lc_tm_at (S K) 0 s).
    { apply lc_tm_at_mono_K with (K := K); auto. }
    eapply IHt with (K := S K) (k := k) (s := s).
    + exact Hs'.
    + assumption.
  - simpl in H. inversion H; subst. constructor; eauto.
  - simpl in H. inversion H; subst. constructor; eauto.
Qed.

Lemma open_tm_ty_rec_lc_inv : forall t K k U,
  lc_ty_at 0 U -> lc_tm_at K k (open_tm_ty_rec K U t) -> lc_tm_at (S K) k t.
Proof.
  induction t; intros K k U HU H.
  - simpl in H. inversion H; subst. constructor. lia.
  - simpl in H. inversion H; subst. constructor.
  - simpl in H. inversion H; subst. constructor.
    + eapply open_ty_rec_lc_inv; eauto.
    + eapply IHt; eauto.
  - simpl in H. inversion H; subst. constructor; eauto.
  - simpl in H. inversion H; subst. constructor. eapply IHt; eauto.
  - simpl in H. inversion H; subst. constructor.
    + eapply IHt; eauto.
    + eapply open_ty_rec_lc_inv; eauto.
  - simpl in H. inversion H; subst. constructor; eauto.
Qed.

(** ** Well-formed types are locally closed *)

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> lc_ty_at 0 T.
Proof.
  intros Delta T H.
  induction H as [Delta X Hin | Delta T1 T2 H1 IH1 H2 IH2 | L Delta T Hbody IHbody].
  - constructor.
  - constructor; auto.
  - constructor.
    eapply open_ty_rec_lc_inv with (k := 0) (U := Ty_FVar (fresh (L ++ fvs_ty T))).
    + constructor.
    + apply IHbody. apply fresh_notin_1.
Qed.

(** ** The typing judgement produces locally closed types and terms *)

Lemma has_type_lc_ty : forall Delta Gamma t T,
  has_type Delta Gamma t T -> lc_ty_at 0 T.
Proof.
  intros Delta Gamma t T H.
  induction H as
    [ Delta Gamma x T Hlook Hwf
    | L Delta Gamma T1 t2 T2 Hwf Hbody IHbody
    | Delta Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
    | L Delta Gamma t T Hbody IHbody
    | Delta Gamma t T U H1 IH1 Hwf
    | Delta Gamma t1 t2 T H1 IH1 H2 IH2 ].
  - eapply wf_ty_lc; eauto.
  - simpl. constructor.
    + eapply wf_ty_lc; eauto.
    + apply (IHbody (fresh (L ++ fvs_ty T2))). apply fresh_notin_1.
  - inversion IH1; subst; assumption.
  - (* T_TAbs *) simpl. constructor.
    apply open_ty_rec_lc_inv with (k := 0) (U := Ty_FVar (fresh (L ++ fvs_ty T))).
    + constructor.
    + apply (IHbody (fresh (L ++ fvs_ty T))). apply fresh_notin_1.
  - (* T_TApp *) simpl. apply open_ty_rec_lc_fwd with (k := 0).
    + eapply wf_ty_lc; eauto.
    + inversion IH1; subst; assumption.
  - (* T_Choice *) assumption.
Qed.

Lemma has_type_lc_tm : forall Delta Gamma t T,
  has_type Delta Gamma t T -> lc_tm_at 0 0 t.
Proof.
  intros Delta Gamma t T H.
  induction H as
    [ Delta Gamma x T Hlook Hwf
    | L Delta Gamma T1 t2 T2 Hwf Hbody IHbody
    | Delta Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
    | L Delta Gamma t T Hbody IHbody
    | Delta Gamma t T U H1 IH1 Hwf
    | Delta Gamma t1 t2 T H1 IH1 H2 IH2 ].
  - constructor.
  - simpl. constructor.
    + eapply wf_ty_lc; eauto.
    + apply open_tm_rec_lc_inv with
        (k := 0) (s := tm_fvar (fresh (L ++ fvs_tm t2))).
      * constructor.
      * apply (IHbody (fresh (L ++ fvs_tm t2))). apply fresh_notin_1.
  - simpl. constructor; assumption.
  - (* T_TAbs *) simpl. constructor.
    apply open_tm_ty_rec_lc_inv with (K := 0)
      (U := Ty_FVar (fresh (L ++ fvs_tm t))).
    + constructor.
    + apply (IHbody (fresh (L ++ fvs_tm t))). apply fresh_notin_1.
  - (* T_TApp *) simpl. constructor.
    + assumption.
    + eapply wf_ty_lc; eauto.
  - (* T_Choice *) simpl. constructor; assumption.
Qed.

(** ** Term substitution infrastructure *)

Fixpoint subst_map (σ : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => σ x
  | tm_abs T t1 => tm_abs T (subst_map σ t1)
  | tm_app t1 t2 => tm_app (subst_map σ t1) (subst_map σ t2)
  | tm_tabs t1 => tm_tabs (subst_map σ t1)
  | tm_tapp t1 T => tm_tapp (subst_map σ t1) T
  | tm_choice t1 t2 => tm_choice (subst_map σ t1) (subst_map σ t2)
  end.

Lemma open_ty_rec_lc_id : forall T k j U,
  lc_ty_at k T -> k <= j -> open_ty_rec j U T = T.
Proof.
  induction T as [ n | a | T1 IH1 T2 IH2 | T1 IH1 ];
    intros k j U H Hle.
  - simpl. inversion H; subst. destruct (Nat.eqb j n) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + reflexivity.
  - simpl. reflexivity.
  - simpl. inversion H; subst.
    assert (E1 : open_ty_rec j U T1 = T1) by (apply IH1 with (k := k); auto).
    assert (E2 : open_ty_rec j U T2 = T2) by (apply IH2 with (k := k); auto).
    rewrite E1, E2. reflexivity.
  - simpl. inversion H; subst.
    assert (E1 : open_ty_rec (S j) U T1 = T1)
      by (apply IH1 with (k := S k); auto; lia).
    rewrite E1. reflexivity.
Qed.

Lemma open_tm_rec_lc_id : forall t K k j u,
  lc_tm_at K k t -> k <= j -> open_tm_rec j u t = t.
Proof.
  induction t as [ n | a | T t0 IH0 | t1 IH1 t2 IH2 | t0 IH0 | t0 IH0 T | t1 IH1 t2 IH2 ];
    intros K k j u H Hle.
  - simpl. inversion H; subst. destruct (Nat.eqb j n) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + reflexivity.
  - simpl. reflexivity.
  - simpl. inversion H; subst.
    assert (E1 : open_tm_rec (S j) u t0 = t0)
      by (apply IH0 with (K := K) (k := S k); auto; lia).
    rewrite E1. reflexivity.
  - simpl. inversion H; subst.
    assert (E1 : open_tm_rec j u t1 = t1) by (apply IH1 with (K := K) (k := k); auto).
    assert (E2 : open_tm_rec j u t2 = t2) by (apply IH2 with (K := K) (k := k); auto).
    rewrite E1, E2. reflexivity.
  - simpl. inversion H; subst.
    assert (E1 : open_tm_rec j u t0 = t0) by (apply IH0 with (K := S K) (k := k); auto).
    rewrite E1. reflexivity.
  - simpl. inversion H; subst.
    assert (E1 : open_tm_rec j u t0 = t0) by (apply IH0 with (K := K) (k := k); auto).
    rewrite E1. reflexivity.
  - simpl. inversion H; subst.
    assert (E1 : open_tm_rec j u t1 = t1) by (apply IH1 with (K := K) (k := k); auto).
    assert (E2 : open_tm_rec j u t2 = t2) by (apply IH2 with (K := K) (k := k); auto).
    rewrite E1, E2. reflexivity.
Qed.

Lemma open_tm_ty_rec_lc_id : forall t K k j U,
  lc_tm_at K k t -> K <= j -> open_tm_ty_rec j U t = t.
Proof.
  induction t as [ n | a | T t0 IH0 | t1 IH1 t2 IH2 | t0 IH0 | t0 IH0 T | t1 IH1 t2 IH2 ];
    intros K k j U H Hle.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. inversion H; subst.
    assert (ET : open_ty_rec j U T = T) by (apply open_ty_rec_lc_id with (k := K); auto).
    assert (Et : open_tm_ty_rec j U t0 = t0) by (apply IH0 with (K := K) (k := S k); auto).
    rewrite ET, Et. reflexivity.
  - simpl. inversion H; subst.
    assert (E1 : open_tm_ty_rec j U t1 = t1) by (apply IH1 with (K := K) (k := k); auto).
    assert (E2 : open_tm_ty_rec j U t2 = t2) by (apply IH2 with (K := K) (k := k); auto).
    rewrite E1, E2. reflexivity.
  - simpl. inversion H; subst.
    assert (E1 : open_tm_ty_rec (S j) U t0 = t0)
      by (apply IH0 with (K := S K) (k := k); auto; lia).
    rewrite E1. reflexivity.
  - simpl. inversion H; subst.
    assert (ET : open_ty_rec j U T = T) by (apply open_ty_rec_lc_id with (k := K); auto).
    assert (Et : open_tm_ty_rec j U t0 = t0) by (apply IH0 with (K := K) (k := k); auto).
    rewrite ET, Et. reflexivity.
  - simpl. inversion H; subst.
    assert (E1 : open_tm_ty_rec j U t1 = t1) by (apply IH1 with (K := K) (k := k); auto).
    assert (E2 : open_tm_ty_rec j U t2 = t2) by (apply IH2 with (K := K) (k := k); auto).
    rewrite E1, E2. reflexivity.
Qed.

Lemma subst_map_open_tm_rec : forall σ t j s,
  (forall x, lc_tm_at 0 0 (σ x)) ->
  subst_map σ (open_tm_rec j s t) = open_tm_rec j (subst_map σ s) (subst_map σ t).
Proof.
  intros σ t.
  induction t as [ n | a | T t0 IH0 | t1 IH1 t2 IH2 | t0 IH0 | t0 IH0 T | t1 IH1 t2 IH2 ];
    intros j s Hσ; simpl.
  - destruct (Nat.eqb j n); reflexivity.
  - assert (E : open_tm_rec j (subst_map σ s) (σ a) = σ a).
    { apply open_tm_rec_lc_id with (K := 0) (k := 0).
      - apply Hσ.
      - lia. }
    rewrite E. reflexivity.
  - assert (E : subst_map σ (open_tm_rec (S j) s t0) =
                open_tm_rec (S j) (subst_map σ s) (subst_map σ t0))
      by (apply IH0; auto).
    rewrite E. reflexivity.
  - assert (E1 : subst_map σ (open_tm_rec j s t1) =
                 open_tm_rec j (subst_map σ s) (subst_map σ t1)) by (apply IH1; auto).
    assert (E2 : subst_map σ (open_tm_rec j s t2) =
                 open_tm_rec j (subst_map σ s) (subst_map σ t2)) by (apply IH2; auto).
    rewrite E1, E2. reflexivity.
  - assert (E : subst_map σ (open_tm_rec j s t0) =
                open_tm_rec j (subst_map σ s) (subst_map σ t0))
      by (apply IH0; auto).
    rewrite E. reflexivity.
  - assert (E : subst_map σ (open_tm_rec j s t0) =
                open_tm_rec j (subst_map σ s) (subst_map σ t0))
      by (apply IH0; auto).
    rewrite E. reflexivity.
  - assert (E1 : subst_map σ (open_tm_rec j s t1) =
                 open_tm_rec j (subst_map σ s) (subst_map σ t1)) by (apply IH1; auto).
    assert (E2 : subst_map σ (open_tm_rec j s t2) =
                 open_tm_rec j (subst_map σ s) (subst_map σ t2)) by (apply IH2; auto).
    rewrite E1, E2. reflexivity.
Qed.

Lemma subst_map_open_tm_ty_rec : forall σ t j U,
  (forall x, lc_tm_at 0 0 (σ x)) ->
  subst_map σ (open_tm_ty_rec j U t) = open_tm_ty_rec j U (subst_map σ t).
Proof.
  intros σ t.
  induction t as [ n | a | T t0 IH0 | t1 IH1 t2 IH2 | t0 IH0 | t0 IH0 T | t1 IH1 t2 IH2 ];
    intros j U Hσ; simpl.
  - reflexivity.
  - assert (E : open_tm_ty_rec j U (σ a) = σ a).
    { apply open_tm_ty_rec_lc_id with (K := 0) (k := 0).
      - apply Hσ.
      - lia. }
    rewrite E. reflexivity.
  - assert (E : subst_map σ (open_tm_ty_rec j U t0) =
                open_tm_ty_rec j U (subst_map σ t0))
      by (apply IH0; auto).
    rewrite E. reflexivity.
  - assert (E1 : subst_map σ (open_tm_ty_rec j U t1) =
                 open_tm_ty_rec j U (subst_map σ t1)) by (apply IH1; auto).
    assert (E2 : subst_map σ (open_tm_ty_rec j U t2) =
                 open_tm_ty_rec j U (subst_map σ t2)) by (apply IH2; auto).
    rewrite E1, E2. reflexivity.
  - assert (E : subst_map σ (open_tm_ty_rec (S j) U t0) =
                open_tm_ty_rec (S j) U (subst_map σ t0))
      by (apply IH0; auto).
    rewrite E. reflexivity.
  - assert (E : subst_map σ (open_tm_ty_rec j U t0) =
                open_tm_ty_rec j U (subst_map σ t0))
      by (apply IH0; auto).
    rewrite E. reflexivity.
  - assert (E1 : subst_map σ (open_tm_ty_rec j U t1) =
                 open_tm_ty_rec j U (subst_map σ t1)) by (apply IH1; auto).
    assert (E2 : subst_map σ (open_tm_ty_rec j U t2) =
                 open_tm_ty_rec j U (subst_map σ t2)) by (apply IH2; auto).
    rewrite E1, E2. reflexivity.
Qed.

Lemma subst_map_id : forall t, subst_map (fun x => tm_fvar x) t = t.
Proof.
  intros t. induction t; simpl; congruence.
Qed.

Lemma lc_ty_ty_subst : forall T X U K,
  lc_ty_at K T -> lc_ty_at 0 U -> lc_ty_at K (ty_subst X U T).
Proof.
  induction T; intros X U K H HU.
  - simpl. assumption.
  - simpl. destruct (Nat.eqb X a) eqn:E.
    + apply lc_ty_at_mono with (k := 0); auto. lia.
    + assumption.
  - simpl in H |-. inversion H; subst. simpl. constructor; eauto.
  - simpl in H |-. inversion H; subst. simpl. constructor. eapply IHT; eauto.
Qed.

Lemma lc_tm_tm_ty_subst : forall t X U K k,
  lc_tm_at K k t -> lc_ty_at 0 U -> lc_tm_at K k (tm_ty_subst X U t).
Proof.
  induction t; intros X U K k H HU.
  - simpl. assumption.
  - simpl. assumption.
  - simpl. simpl in H. inversion H; subst. constructor.
    + eapply lc_ty_ty_subst; eauto.
    + eapply IHt; eauto.
  - simpl. simpl in H. inversion H; subst. constructor; eauto.
  - simpl. simpl in H. inversion H; subst. constructor. eapply IHt; eauto.
  - simpl. simpl in H. inversion H; subst. constructor.
    + eapply IHt; eauto.
    + eapply lc_ty_ty_subst; eauto.
  - simpl. simpl in H. inversion H; subst. constructor; eauto.
Qed.

Lemma lc_tm_subst_map : forall t σ K k,
  lc_tm_at K k t ->
  (forall x, lc_tm_at K 0 (σ x)) ->
  lc_tm_at K k (subst_map σ t).
Proof.
  induction t as [ n | a | T t0 IH0 | t1 IH1 t2 IH2 | t0 IH0 | t0 IH0 T | t1 IH1 t2 IH2 ];
    intros σ K k H Hσ.
  - simpl. assumption.
  - simpl. apply lc_tm_at_mono_k with (k := 0); [lia | apply Hσ].
  - simpl. simpl in H. inversion H; subst. constructor.
    + assumption.
    + eapply IH0; eauto.
  - simpl. simpl in H. inversion H; subst. constructor.
    + eapply IH1; eauto.
    + eapply IH2; eauto.
  - simpl. simpl in H. inversion H; subst. constructor.
    eapply IH0 with (K := S K).
    + eassumption.
    + intros x. apply lc_tm_at_mono_K with (K := K); [lia | apply Hσ].
  - simpl. simpl in H. inversion H; subst. constructor.
    + eapply IH0; eauto.
    + assumption.
  - simpl. simpl in H. inversion H; subst. constructor.
    + eapply IH1; eauto.
    + eapply IH2; eauto.
Qed.

Lemma value_tm_ty_subst : forall X U t,
  lc_ty_at 0 U -> value t -> value (tm_ty_subst X U t).
Proof.
  intros X U t HU Hv. destruct Hv as [T t0 Hlc | t0 Hlc].
  - simpl. constructor. constructor.
    + simpl in Hlc. inversion Hlc; subst. eapply lc_ty_ty_subst; eauto.
    + simpl in Hlc. inversion Hlc; subst. eapply lc_tm_tm_ty_subst; eauto.
  - simpl. constructor. constructor. simpl in Hlc. inversion Hlc; subst.
    eapply lc_tm_tm_ty_subst; eauto.
Qed.

Lemma lc_abs_tm_ty_subst : forall X U T t,
  lc_ty_at 0 U -> locally_closed_tm (tm_abs T t) ->
  locally_closed_tm (tm_abs (ty_subst X U T) (tm_ty_subst X U t)).
Proof.
  intros X U T t HU Hlc. simpl in *. inversion Hlc; subst. simpl. constructor.
  - eapply lc_ty_ty_subst; eauto.
  - eapply lc_tm_tm_ty_subst; eauto.
Qed.

Lemma lc_tabs_tm_ty_subst : forall X U t,
  lc_ty_at 0 U -> locally_closed_tm (tm_tabs t) ->
  locally_closed_tm (tm_tabs (tm_ty_subst X U t)).
Proof.
  intros X U t HU Hlc. simpl in *. inversion Hlc; subst. simpl. constructor.
  eapply lc_tm_tm_ty_subst; eauto.
Qed.

(** ** Commutation of type substitution with opening *)

Lemma ty_subst_open_ty_rec : forall T X U j V,
  lc_ty_at 0 U ->
  ty_subst X U (open_ty_rec j V T) = open_ty_rec j (ty_subst X U V) (ty_subst X U T).
Proof.
  induction T as [ n | a | T1 IH1 T2 IH2 | T1 IH1 ]; intros X U j V HU.
  - simpl. destruct (Nat.eqb j n); reflexivity.
  - simpl. destruct (Nat.eqb X a) eqn:E.
    + symmetry. apply open_ty_rec_lc_id with (k := 0); [assumption | lia].
    + reflexivity.
  - assert (E1 : ty_subst X U (open_ty_rec j V T1) =
                 open_ty_rec j (ty_subst X U V) (ty_subst X U T1))
      by (apply IH1; auto).
    assert (E2 : ty_subst X U (open_ty_rec j V T2) =
                 open_ty_rec j (ty_subst X U V) (ty_subst X U T2))
      by (apply IH2; auto).
    simpl. rewrite E1, E2. reflexivity.
  - assert (E : ty_subst X U (open_ty_rec (S j) V T1) =
               open_ty_rec (S j) (ty_subst X U V) (ty_subst X U T1))
      by (apply IH1; auto).
    simpl. rewrite E. reflexivity.
Qed.

Lemma tm_ty_subst_open_tm_rec : forall t X U j s,
  tm_ty_subst X U (open_tm_rec j s t) =
  open_tm_rec j (tm_ty_subst X U s) (tm_ty_subst X U t).
Proof.
  induction t as [ n | a | T t0 IH0 | t1 IH1 t2 IH2 | t0 IH0 | t0 IH0 T | t1 IH1 t2 IH2 ];
    intros X U j s; simpl.
  - destruct (Nat.eqb j n); reflexivity.
  - reflexivity.
  - rewrite IH0. reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH0. reflexivity.
  - rewrite IH0. reflexivity.
  - rewrite IH1, IH2. reflexivity.
Qed.

Lemma tm_ty_subst_open_tm_ty_rec : forall t X U j V,
  lc_ty_at 0 U ->
  tm_ty_subst X U (open_tm_ty_rec j V t) =
  open_tm_ty_rec j (ty_subst X U V) (tm_ty_subst X U t).
Proof.
  induction t as [ n | a | T t0 IH0 | t1 IH1 t2 IH2 | t0 IH0 | t0 IH0 T | t1 IH1 t2 IH2 ];
    intros X U j V HU; simpl.
  - reflexivity.
  - reflexivity.
  - assert (E1 : ty_subst X U (open_ty_rec j V T) =
                 open_ty_rec j (ty_subst X U V) (ty_subst X U T))
      by (apply ty_subst_open_ty_rec; auto).
    assert (E2 : tm_ty_subst X U (open_tm_ty_rec j V t0) =
                 open_tm_ty_rec j (ty_subst X U V) (tm_ty_subst X U t0))
      by (apply IH0; auto).
    rewrite E1, E2. reflexivity.
  - assert (E1 : tm_ty_subst X U (open_tm_ty_rec j V t1) =
                 open_tm_ty_rec j (ty_subst X U V) (tm_ty_subst X U t1))
      by (apply IH1; auto).
    assert (E2 : tm_ty_subst X U (open_tm_ty_rec j V t2) =
                 open_tm_ty_rec j (ty_subst X U V) (tm_ty_subst X U t2))
      by (apply IH2; auto).
    rewrite E1, E2. reflexivity.
  - assert (E : tm_ty_subst X U (open_tm_ty_rec (S j) V t0) =
               open_tm_ty_rec (S j) (ty_subst X U V) (tm_ty_subst X U t0))
      by (apply IH0; auto).
    rewrite E. reflexivity.
  - assert (E1 : ty_subst X U (open_ty_rec j V T) =
                 open_ty_rec j (ty_subst X U V) (ty_subst X U T))
      by (apply ty_subst_open_ty_rec; auto).
    assert (E2 : tm_ty_subst X U (open_tm_ty_rec j V t0) =
                 open_tm_ty_rec j (ty_subst X U V) (tm_ty_subst X U t0))
      by (apply IH0; auto).
    rewrite E1, E2. reflexivity.
  - assert (E1 : tm_ty_subst X U (open_tm_ty_rec j V t1) =
                 open_tm_ty_rec j (ty_subst X U V) (tm_ty_subst X U t1))
      by (apply IH1; auto).
    assert (E2 : tm_ty_subst X U (open_tm_ty_rec j V t2) =
                 open_tm_ty_rec j (ty_subst X U V) (tm_ty_subst X U t2))
      by (apply IH2; auto).
    rewrite E1, E2. reflexivity.
Qed.

Lemma tm_ty_subst_open_tm : forall t X U s,
  tm_ty_subst X U (open_tm t s) =
  open_tm (tm_ty_subst X U t) (tm_ty_subst X U s).
Proof. intros. unfold open_tm. apply tm_ty_subst_open_tm_rec. Qed.

Lemma tm_ty_subst_open_tm_ty : forall t X U V,
  lc_ty_at 0 U ->
  tm_ty_subst X U (open_tm_ty t V) =
  open_tm_ty (tm_ty_subst X U t) (ty_subst X U V).
Proof. intros. unfold open_tm_ty. apply tm_ty_subst_open_tm_ty_rec; auto. Qed.

(** ** Multi-step reduction infrastructure *)

Lemma multi_trans : forall a b c, multi a b -> multi b c -> multi a c.
Proof.
  intros a b c H. induction H; intros Hbc.
  - assumption.
  - apply multi_step with y; auto.
Qed.

Lemma multi_app_left : forall A A' B,
  multi A A' -> locally_closed_tm B -> multi (tm_app A B) (tm_app A' B).
Proof.
  intros A A' B H. induction H; intros Hlc.
  - apply multi_refl.
  - apply multi_step with (tm_app y B).
    + apply ST_App1; auto.
    + apply IHmulti; auto.
Qed.

Lemma multi_app_right : forall A B B',
  multi B B' -> value A -> multi (tm_app A B) (tm_app A B').
Proof.
  intros A B B' H. induction H; intros Hv.
  - apply multi_refl.
  - apply multi_step with (tm_app A y).
    + apply ST_App2; auto.
    + apply IHmulti; auto.
Qed.

Lemma multi_app_cong : forall A A' B B',
  multi A A' -> multi B B' -> locally_closed_tm B -> value A' ->
  multi (tm_app A B) (tm_app A' B').
Proof.
  intros A A' B B' HA HB Hlc Hv.
  apply multi_trans with (b := tm_app A' B).
  - apply multi_app_left; auto.
  - apply multi_app_right; auto.
Qed.

Lemma multi_tapp_cong : forall A A' T,
  multi A A' -> locally_closed_ty T -> multi (tm_tapp A T) (tm_tapp A' T).
Proof.
  intros A A' T H. induction H; intros Hlc.
  - apply multi_refl.
  - apply multi_step with (tm_tapp y T).
    + apply ST_TApp; auto.
    + apply IHmulti; auto.
Qed.

Lemma step_tm_ty_subst : forall X U a b,
  lc_ty_at 0 U -> step a b -> step (tm_ty_subst X U a) (tm_ty_subst X U b).
Proof.
  intros X U a b HU H.
  induction H as
    [ T t v Hlc Hv
    | t1 t1' t2 Hstep IHstep Hlc
    | v1 t2 t2' Hv Hstep IHstep
    | t T Hlc Hlcty
    | t t' T Hstep IHstep Hlcty
    | t1 t2 Hlc1 Hlc2
    | t1 t2 Hlc1 Hlc2 ].
  - (* ST_AppAbs *) simpl. rewrite tm_ty_subst_open_tm. simpl.
    apply ST_AppAbs.
    + eapply lc_abs_tm_ty_subst; eauto.
    + apply value_tm_ty_subst; auto.
  - (* ST_App1 *) simpl. eapply ST_App1.
    + apply IHstep.
    + eapply lc_tm_tm_ty_subst; eauto.
  - (* ST_App2 *) simpl. eapply ST_App2.
    + apply value_tm_ty_subst; auto.
    + apply IHstep.
  - (* ST_TAppTabs *) simpl. rewrite tm_ty_subst_open_tm_ty; auto.
    apply ST_TAppTabs.
    + eapply lc_tabs_tm_ty_subst; eauto.
    + eapply lc_ty_ty_subst; eauto.
  - (* ST_TApp *) simpl. eapply ST_TApp.
    + apply IHstep.
    + eapply lc_ty_ty_subst; eauto.
  - (* ST_ChoiceLeft *) simpl. apply ST_ChoiceLeft; eapply lc_tm_tm_ty_subst; eauto.
  - (* ST_ChoiceRight *) simpl. apply ST_ChoiceRight; eapply lc_tm_tm_ty_subst; eauto.
Qed.

Lemma multi_tm_ty_subst : forall X U a b,
  lc_ty_at 0 U -> multi a b -> multi (tm_ty_subst X U a) (tm_ty_subst X U b).
Proof.
  intros X U a b HU H.
  induction H as [ x | x y z Hstep Hmulti IHmulti ].
  - apply multi_refl.
  - apply multi_step with (tm_ty_subst X U y).
    + apply step_tm_ty_subst; auto.
    + apply IHmulti; auto.
Qed.

(** ** END STAGE 1 **)


(** ================================================================== *)
(** * Stage 2: the logical relation                                    *)
(** ================================================================== *)

(** Type substitution relation: [tsub P T T'] holds when [T'] is obtained
    from [T] by replacing type variables not in [P] with locally closed
    types. *)

Inductive tsub (P : list atom) : ty -> ty -> Prop :=
  | tsub_refl : forall T, tsub P T T
  | tsub_var : forall X U, ~ In X P -> lc_ty_at 0 U -> tsub P (Ty_FVar X) U
  | tsub_arrow : forall T1 T1' T2 T2',
      tsub P T1 T1' -> tsub P T2 T2' ->
      tsub P (Ty_Arrow T1 T2) (Ty_Arrow T1' T2')
  | tsub_all : forall T T', tsub P T T' -> tsub P (Ty_All T) (Ty_All T').

(** The corresponding relation on terms. *)

Inductive trel (P : list atom) : tm -> tm -> Prop :=
  | trel_bvar : forall i, trel P (tm_bvar i) (tm_bvar i)
  | trel_fvar : forall x, trel P (tm_fvar x) (tm_fvar x)
  | trel_abs : forall T T' t t',
      tsub P T T' -> trel P t t' -> trel P (tm_abs T t) (tm_abs T' t')
  | trel_app : forall t1 t1' t2 t2',
      trel P t1 t1' -> trel P t2 t2' -> trel P (tm_app t1 t2) (tm_app t1' t2')
  | trel_tabs : forall t t', trel P t t' -> trel P (tm_tabs t) (tm_tabs t')
  | trel_tapp : forall t t' T T',
      trel P t t' -> tsub P T T' -> trel P (tm_tapp t T) (tm_tapp t' T')
  | trel_choice : forall t1 t1' t2 t2',
      trel P t1 t1' -> trel P t2 t2' -> trel P (tm_choice t1 t2) (tm_choice t1' t2').

(** A relation is admissible when it is invariant under type changes. *)

Definition Adm (P : list atom) (R : VRel) : Prop :=
  forall a a' b b', trel P a a' -> trel P b b' -> R a b -> R a' b'.

(** The value interpretation of types. *)

Fixpoint V (P : list atom) (S : ty) (η : atom -> VRel) (benv : list VRel)
         (a b : tm) {struct S} : Prop :=
  match S with
  | Ty_BVar i => value a /\ value b /\ nth i benv DefaultRel a b
  | Ty_FVar X => value a /\ value b /\ η X a b
  | Ty_Arrow S1 S2 =>
      value a /\ value b /\
      forall a1 a2, V P S1 η benv a1 a2 ->
        exists v1 v2, multi (tm_app a a1) v1 /\ multi (tm_app b a2) v2 /\
                      V P S2 η benv v1 v2
  | Ty_All S0 =>
      value a /\ value b /\
      forall U R, lc_ty_at 0 U -> Adm P R ->
        exists v1 v2, multi (tm_tapp a U) v1 /\ multi (tm_tapp b U) v2 /\
                      V P S0 η (R :: benv) v1 v2
  end.

(** The expression interpretation. *)

Definition E (P : list atom) (S : ty) (η : atom -> VRel) (benv : list VRel)
           (a b : tm) : Prop :=
  exists v1 v2, multi a v1 /\ multi b v2 /\ V P S η benv v1 v2.

Definition upd (η : atom -> VRel) (X : atom) (R : VRel) : atom -> VRel :=
  fun Z => if Nat.eqb X Z then R else η Z.

Lemma upd_eq : forall η X R, upd η X R X = R.
Proof. intros. unfold upd. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma upd_neq : forall η X R Z, X <> Z -> upd η X R Z = η Z.
Proof.
  intros. unfold upd. apply Nat.eqb_neq in H. rewrite H. reflexivity.
Qed.

(** ** Elementary properties of the semantics *)

Lemma V_value_l : forall P S η benv a b, V P S η benv a b -> value a.
Proof.
  intros P S. destruct S; intros η benv x y H; simpl in H;
    destruct H as [H1 _]; exact H1.
Qed.

Lemma V_value_r : forall P S η benv a b, V P S η benv a b -> value b.
Proof.
  intros P S. destruct S; intros η benv x y H; simpl in H;
    destruct H as [_ [H1 _]]; exact H1.
Qed.

Lemma V_to_E : forall P S η benv a b, V P S η benv a b -> E P S η benv a b.
Proof.
  intros. exists a, b. split; [apply multi_refl | split; [apply multi_refl | exact H]].
Qed.

Lemma E_multi_left : forall P S η benv a a' b,
  multi a a' -> E P S η benv a' b -> E P S η benv a b.
Proof.
  intros P S η benv a a' b Hm [v1 [v2 [H1 [H2 H3]]]].
  exists v1, v2. split; [| split; [exact H2 | exact H3]].
  eapply multi_trans; eauto.
Qed.

Lemma E_multi_right : forall P S η benv a b b',
  multi b b' -> E P S η benv a b' -> E P S η benv a b.
Proof.
  intros P S η benv a b b' Hm [v1 [v2 [H1 [H2 H3]]]].
  exists v1, v2. split; [| split; [| exact H3]].
  - exact H1.
  - eapply multi_trans; eauto.
Qed.

Lemma E_multi : forall P S η benv a a' b b',
  multi a a' -> multi b b' -> E P S η benv a' b' -> E P S η benv a b.
Proof.
  intros. eapply E_multi_left; [eauto | eapply E_multi_right; eauto].
Qed.

(** ** Preservation of locally closed types under [tsub] *)

Lemma tsub_lc : forall P T T', tsub P T T' -> forall K, lc_ty_at K T -> lc_ty_at K T'.
Proof.
  intros P T T' H. induction H; intros K Hlc.
  - assumption.
  - apply lc_ty_at_mono with (k := 0); auto. lia.
  - inversion Hlc; subst. constructor; auto.
  - inversion Hlc; subst. constructor. apply IHtsub. assumption.
Qed.

(** ** Basic properties of [trel] *)

Lemma trel_refl : forall P t, trel P t t.
Proof.
  intros P t.
  induction t as [ n | x | T t0 IH0 | t1 IH1 t2 IH2 | t0 IH0 | t0 IH0 T | t1 IH1 t2 IH2 ].
  - apply trel_bvar.
  - apply trel_fvar.
  - apply trel_abs; [apply tsub_refl | assumption].
  - apply trel_app; assumption.
  - apply trel_tabs; assumption.
  - apply trel_tapp; [assumption | apply tsub_refl].
  - apply trel_choice; assumption.
Qed.

Lemma trel_lc : forall P a a', trel P a a' -> forall K k,
  lc_tm_at K k a -> lc_tm_at K k a'.
Proof.
  intros P a a' H. induction H as
    [ i | x
    | T T' t t' Htsub Htrel IHtrel
    | t1 t1' t2 t2' H1 IH1 H2 IH2
    | t t' Htrel IHtrel
    | t t' T T' Htrel IHtrel Htsub
    | t1 t1' t2 t2' H1 IH1 H2 IH2 ];
    intros K k Hlc.
  - assumption.
  - assumption.
  - simpl in Hlc. inversion Hlc; subst. simpl. constructor.
    + eapply tsub_lc; eauto.
    + apply IHtrel. assumption.
  - simpl in Hlc. inversion Hlc; subst. simpl. constructor; auto.
  - simpl in Hlc. inversion Hlc; subst. simpl. constructor.
    apply IHtrel. assumption.
  - simpl in Hlc. inversion Hlc; subst. simpl. constructor.
    + apply IHtrel. assumption.
    + eapply tsub_lc; eauto.
  - simpl in Hlc. inversion Hlc; subst. simpl. constructor; auto.
Qed.

Lemma trel_value : forall P a a', trel P a a' -> value a -> value a'.
Proof.
  intros P a a' Htr Hv. destruct Hv as [T t Hlc | t Hlc].
  - inversion Htr; subst. simpl in Hlc. inversion Hlc; subst.
    simpl. constructor. eapply trel_lc; eauto.
  - inversion Htr; subst. simpl in Hlc. inversion Hlc; subst.
    simpl. constructor. eapply trel_lc; eauto.
Qed.

(** ** Opening lemmas for [trel] *)

Lemma trel_abs_inv : forall P T t a',
  trel P (tm_abs T t) a' ->
  exists T' t', a' = tm_abs T' t' /\ tsub P T T' /\ trel P t t'.
Proof. intros. inversion H; subst. eauto. Qed.

Lemma trel_tabs_inv : forall P t a',
  trel P (tm_tabs t) a' -> exists t', a' = tm_tabs t' /\ trel P t t'.
Proof. intros. inversion H; subst. eauto. Qed.

Lemma trel_app_inv : forall P t1 t2 a',
  trel P (tm_app t1 t2) a' ->
  exists t1' t2', a' = tm_app t1' t2' /\ trel P t1 t1' /\ trel P t2 t2'.
Proof. intros. inversion H; subst. eauto. Qed.

Lemma trel_tapp_inv : forall P t T a',
  trel P (tm_tapp t T) a' ->
  exists t' T', a' = tm_tapp t' T' /\ trel P t t' /\ tsub P T T'.
Proof. intros. inversion H; subst. eauto. Qed.

Lemma trel_choice_inv : forall P t1 t2 a',
  trel P (tm_choice t1 t2) a' ->
  exists t1' t2', a' = tm_choice t1' t2' /\ trel P t1 t1' /\ trel P t2 t2'.
Proof. intros. inversion H; subst. eauto. Qed.

(** ** Opening lemmas for [trel] *)

Lemma trel_open_tm_rec : forall P t t',
  trel P t t' -> forall j s s', trel P s s' ->
  trel P (open_tm_rec j s t) (open_tm_rec j s' t').
Proof.
  intros P t t' H. induction H as
    [ i | x
    | T T' u u' Htsub Hu IH
    | t1 t1' t2 t2' H1 IH1 H2 IH2
    | u u' Hu IH
    | u u' T T' Hu IH Htsub
    | t1 t1' t2 t2' H1 IH1 H2 IH2 ];
    intros j s s' Hs.
  - simpl. destruct (Nat.eqb j i); [assumption | apply trel_bvar].
  - simpl. apply trel_fvar.
  - simpl. apply trel_abs; [assumption | apply IH; assumption].
  - simpl. apply trel_app; [apply IH1; assumption | apply IH2; assumption].
  - simpl. apply trel_tabs. apply IH; assumption.
  - simpl. apply trel_tapp; [apply IH; assumption | exact Htsub].
  - simpl. apply trel_choice; [apply IH1; assumption | apply IH2; assumption].
Qed.

Lemma tsub_open_ty_refl : forall P T,
  forall U U' j, tsub P U U' ->
  tsub P (open_ty_rec j U T) (open_ty_rec j U' T).
Proof.
  intros P T. induction T as [ n | x | T1 IH1 T2 IH2 | T1 IH1 ];
    intros U U' j H.
  - simpl. destruct (Nat.eqb j n); [assumption | apply tsub_refl].
  - simpl. apply tsub_refl.
  - simpl. apply tsub_arrow; auto.
  - simpl. apply tsub_all. apply IH1; auto.
Qed.

Lemma tsub_open_ty : forall P T T',
  tsub P T T' -> forall U U' j, tsub P U U' ->
  tsub P (open_ty_rec j U T) (open_ty_rec j U' T').
Proof.
  intros P T T' H.
  induction H as
    [ T0
    | X U0 hf hlc
    | T1 T1' T2 T2' H1 IH1 H2 IH2
    | T0 T0' H0 IH0 ];
    intros V V' j HV.
  - apply tsub_open_ty_refl; auto.
  - simpl. rewrite open_ty_rec_lc_id with (k := 0) (j := j); [| assumption | lia].
    apply tsub_var; auto.
  - simpl. apply tsub_arrow.
    + apply IH1. assumption.
    + apply IH2. assumption.
  - simpl. apply tsub_all. apply IH0. assumption.
Qed.

Lemma trel_open_ty_rec : forall P t t',
  trel P t t' -> forall j T T', tsub P T T' ->
  trel P (open_tm_ty_rec j T t) (open_tm_ty_rec j T' t').
Proof.
  intros P t t' H. induction H as
    [ i | x
    | Ta Ta' u u' Htsub Hu IH
    | t1 t1' t2 t2' H1 IH1 H2 IH2
    | u u' Hu IH
    | u u' Ta Ta' Hu IH Htsub
    | t1 t1' t2 t2' H1 IH1 H2 IH2 ];
    intros j T T' HT.
  - simpl. apply trel_bvar.
  - simpl. apply trel_fvar.
  - simpl. apply trel_abs.
    + apply tsub_open_ty; assumption.
    + apply IH; assumption.
  - simpl. apply trel_app; [apply IH1; assumption | apply IH2; assumption].
  - simpl. apply trel_tabs. apply IH; assumption.
  - simpl. apply trel_tapp.
    + apply IH; assumption.
    + apply tsub_open_ty; assumption.
  - simpl. apply trel_choice; [apply IH1; assumption | apply IH2; assumption].
Qed.

(** ** One step of [trel] simulates one step of reduction *)

Lemma trel_step : forall a b, step a b ->
  forall P a', trel P a a' -> exists b', step a' b' /\ trel P b b'.
Proof.
  intros a b Hstep.
  induction Hstep as
    [ T t v Hlc Hv
    | t1 t1' t2 Hsub IHsub Hlc
    | v1 t2 t2' Hv Hsub IHsub
    | t T Hlc Hlcty
    | t t' T Hsub IHsub Hlcty
    | t1 t2 Hlc1 Hlc2
    | t1 t2 Hlc1 Hlc2 ];
    intros P a' Htr.
  - (* ST_AppAbs *)
    destruct (trel_app_inv P (tm_abs T t) v a' Htr)
      as [t1' [v' [Ha' [H1 H2]]]]; subst.
    destruct (trel_abs_inv P T t t1' H1) as [T' [t' [Ht1' [Htsub Ht]]]]; subst.
    exists (open_tm t' v'); split.
    + apply ST_AppAbs.
      * eapply trel_lc; eauto.
      * eapply trel_value; eauto.
    + eapply trel_open_tm_rec with (j := 0); [exact Ht | exact H2].
  - (* ST_App1 *)
    destruct (trel_app_inv P t1 t2 a' Htr) as [t1'' [t2'' [Ha' [H1 H2]]]]; subst.
    destruct (IHsub P t1'' H1) as [b' [Hb' Htre]].
    exists (tm_app b' t2''); split.
    + apply ST_App1; [exact Hb' | eapply trel_lc; eauto].
    + apply trel_app; assumption.
  - (* ST_App2 *)
    destruct (trel_app_inv P v1 t2 a' Htr) as [v1' [t2'' [Ha' [H1 H2]]]]; subst.
    destruct (IHsub P t2'' H2) as [b' [Hb' Htre]].
    exists (tm_app v1' b'); split.
    + apply ST_App2; [eapply trel_value; eauto | exact Hb'].
    + apply trel_app; assumption.
  - (* ST_TAppTabs *)
    destruct (trel_tapp_inv P (tm_tabs t) T a' Htr) as [t' [T' [Ha' [Ht Htsub]]]]; subst.
    destruct (trel_tabs_inv P t t' Ht) as [t'' [Ha' Ht']]; subst.
    exists (open_tm_ty t'' T'); split.
    + apply ST_TAppTabs.
      * eapply trel_lc; eauto.
      * eapply tsub_lc; eauto.
    + eapply trel_open_ty_rec; [exact Ht' | exact Htsub].
  - (* ST_TApp *)
    destruct (trel_tapp_inv P t T a' Htr) as [t'' [T' [Ha' [Ht Htsub]]]]; subst.
    destruct (IHsub P t'' Ht) as [b' [Hb' Htre]].
    exists (tm_tapp b' T'); split.
    + apply ST_TApp; [exact Hb' | eapply tsub_lc; eauto].
    + apply trel_tapp; assumption.
  - (* ST_ChoiceLeft *)
    destruct (trel_choice_inv P t1 t2 a' Htr) as [t1' [t2' [Ha' [H1 H2]]]]; subst.
    exists t1'; split.
    + apply ST_ChoiceLeft; eapply trel_lc; eauto.
    + exact H1.
  - (* ST_ChoiceRight *)
    destruct (trel_choice_inv P t1 t2 a' Htr) as [t1' [t2' [Ha' [H1 H2]]]]; subst.
    exists t2'; split.
    + apply ST_ChoiceRight; eapply trel_lc; eauto.
    + exact H2.
Qed.

Lemma trel_multi : forall P a a' b,
  trel P a a' -> multi a b -> exists b', multi a' b' /\ trel P b b'.
Proof.
  intros P a a' b Htr Hm. revert a' Htr.
  induction Hm as [ x | x y z Hstep Hmulti IH ]; intros a' Htr.
  - exists a'; split; [apply multi_refl | exact Htr].
  - destruct (trel_step x y Hstep P a' Htr) as [y' [Hy' Htrely]].
    destruct (IH y' Htrely) as [z' [Hz' Htrelyz]].
    exists z'; split; [| exact Htrelyz].
    eapply multi_step; eauto.
Qed.


(** ** Injectivity of type substitution for fresh variables *)

Lemma ty_subst_id : forall T X U, ~ In X (fvs_ty T) -> ty_subst X U T = T.
Proof.
  intros T. induction T as [ n | x | T1 IH1 T2 IH2 | T1 IH1 ];
    intros X U H.
  - simpl. reflexivity.
  - simpl. destruct (Nat.eqb X x) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply H. simpl. left. reflexivity.
    + reflexivity.
  - simpl. assert (H1 : ~ In X (fvs_ty T1))
      by (intro Hin; apply H; apply in_or_app; left; exact Hin).
    assert (H2 : ~ In X (fvs_ty T2))
      by (intro Hin; apply H; apply in_or_app; right; exact Hin).
    rewrite IH1; auto. rewrite IH2; auto.
  - simpl. rewrite IH1; auto.
Qed.

Lemma tm_ty_subst_id : forall t X U, ~ In X (fvs_tm t) -> tm_ty_subst X U t = t.
Proof.
  intros t.
  induction t as [ n | x | T t0 IH0 | t1 IH1 t2 IH2 | t0 IH0 | t0 IH0 T | t1 IH1 t2 IH2 ];
    intros X U H; simpl.
  - reflexivity.
  - reflexivity.
  - assert (HT : ty_subst X U T = T)
      by (apply ty_subst_id; intro Hin; apply H; apply in_or_app; left; exact Hin).
    assert (Ht : tm_ty_subst X U t0 = t0)
      by (apply IH0; intro Hin; apply H; apply in_or_app; right; exact Hin).
    rewrite HT, Ht. reflexivity.
  - assert (H1 : tm_ty_subst X U t1 = t1)
      by (apply IH1; intro Hin; apply H; apply in_or_app; left; exact Hin).
    assert (H2 : tm_ty_subst X U t2 = t2)
      by (apply IH2; intro Hin; apply H; apply in_or_app; right; exact Hin).
    rewrite H1, H2. reflexivity.
  - rewrite IH0; auto.
  - assert (H1 : tm_ty_subst X U t0 = t0)
      by (apply IH0; intro Hin; apply H; apply in_or_app; left; exact Hin).
    assert (H2 : ty_subst X U T = T)
      by (apply ty_subst_id; intro Hin; apply H; apply in_or_app; right; exact Hin).
    rewrite H1, H2. reflexivity.
  - assert (H1 : tm_ty_subst X U t1 = t1)
      by (apply IH1; intro Hin; apply H; apply in_or_app; left; exact Hin).
    assert (H2 : tm_ty_subst X U t2 = t2)
      by (apply IH2; intro Hin; apply H; apply in_or_app; right; exact Hin).
    rewrite H1, H2. reflexivity.
Qed.

Lemma tsub_ty_subst : forall P X U T,
  ~ In X P -> lc_ty_at 0 U -> tsub P T (ty_subst X U T).
Proof.
  intros P X U T. induction T as [ n | x | T1 IH1 T2 IH2 | T1 IH1 ];
    intros Hf HU.
  - simpl. apply tsub_refl.
  - simpl. destruct (Nat.eqb X x) eqn:E.
    + apply Nat.eqb_eq in E. subst. apply tsub_var; auto.
    + apply tsub_refl.
  - simpl. apply tsub_arrow; auto.
  - simpl. apply tsub_all; auto.
Qed.

Lemma trel_ty_subst : forall P X U t,
  ~ In X P -> lc_ty_at 0 U -> trel P t (tm_ty_subst X U t).
Proof.
  intros P X U t.
  induction t as [ n | x | T t0 IH0 | t1 IH1 t2 IH2 | t0 IH0 | t0 IH0 T | t1 IH1 t2 IH2 ];
    intros Hf HU.
  - simpl. apply trel_bvar.
  - simpl. apply trel_fvar.
  - simpl. apply trel_abs.
    + apply tsub_ty_subst; auto.
    + apply IH0; auto.
  - simpl. apply trel_app; auto.
  - simpl. apply trel_tabs; auto.
  - simpl. apply trel_tapp.
    + apply IH0; auto.
    + apply tsub_ty_subst; auto.
  - simpl. apply trel_choice; auto.
Qed.

(** ** Terms whose atoms are all protected are unchanged *)

Lemma tsub_same_of_atoms : forall P T T',
  (forall x, In x (fvs_ty T) -> In x P) -> tsub P T T' -> T' = T.
Proof.
  intros P T T' Hall H.
  induction H as
    [ T0 | X U0 hf hlc | T1 T1' T2 T2' H1 IH1 H2 IH2 | T0 T0' H0 IH0 ].
  - reflexivity.
  - exfalso. apply hf. apply Hall. simpl. left. reflexivity.
  - assert (E1 : T1' = T1)
      by (apply IH1; intros x Hin; apply Hall; apply in_or_app; left; exact Hin).
    assert (E2 : T2' = T2)
      by (apply IH2; intros x Hin; apply Hall; apply in_or_app; right; exact Hin).
    simpl. rewrite E1, E2. reflexivity.
  - assert (E : T0' = T0) by (apply IH0; intros x Hin; apply Hall; exact Hin).
    simpl. rewrite E. reflexivity.
Qed.

Lemma trel_same_of_atoms : forall P t t',
  (forall x, In x (fvs_tm t) -> In x P) -> trel P t t' -> t' = t.
Proof.
  intros P t t' Hall H.
  induction H as
    [ i | x
    | T T' u u' Htsub Hu IH
    | t1 t1' t2 t2' H1 IH1 H2 IH2
    | u u' Hu IH
    | u u' T T' Hu IH Htsub
    | t1 t1' t2 t2' H1 IH1 H2 IH2 ].
  - reflexivity.
  - reflexivity.
  - assert (E1 : T' = T)
      by (apply tsub_same_of_atoms with (P := P); [ intros x Hin; apply Hall; apply in_or_app; left; exact Hin | exact Htsub ]).
    assert (E2 : u' = u)
      by (apply IH; intros x Hin; apply Hall; apply in_or_app; right; exact Hin).
    simpl. rewrite E1, E2. reflexivity.
  - assert (E1 : t1' = t1)
      by (apply IH1; intros x Hin; apply Hall; apply in_or_app; left; exact Hin).
    assert (E2 : t2' = t2)
      by (apply IH2; intros x Hin; apply Hall; apply in_or_app; right; exact Hin).
    simpl. rewrite E1, E2. reflexivity.
  - assert (E : u' = u) by (apply IH; intros x Hin; apply Hall; exact Hin).
    simpl. rewrite E. reflexivity.
  - assert (E1 : u' = u)
      by (apply IH; intros x Hin; apply Hall; apply in_or_app; left; exact Hin).
    assert (E2 : T' = T)
      by (apply tsub_same_of_atoms with (P := P); [ intros x Hin; apply Hall; apply in_or_app; right; exact Hin | exact Htsub ]).
    simpl. rewrite E1, E2. reflexivity.
  - assert (E1 : t1' = t1)
      by (apply IH1; intros x Hin; apply Hall; apply in_or_app; left; exact Hin).
    assert (E2 : t2' = t2)
      by (apply IH2; intros x Hin; apply Hall; apply in_or_app; right; exact Hin).
    simpl. rewrite E1, E2. reflexivity.
Qed.

(** ** Admissibility of the default relation and of list members *)

Lemma Adm_default : forall P, Adm P DefaultRel.
Proof. intros P a a' b b' H1 H2 H3. exact H3. Qed.

Lemma Adm_nth : forall P (benv : list VRel) i,
  (forall R, In R benv -> Adm P R) -> Adm P (nth i benv DefaultRel).
Proof.
  intros P benv. induction benv as [| R0 benv IH]; intros i Hall.
  - destruct i; simpl; apply Adm_default.
  - destruct i as [| i]; simpl.
    + apply Hall. left. reflexivity.
    + apply IH. intros R Hin. apply Hall. right. exact Hin.
Qed.

(** ** The semantics only depends on the first [k] entries of [benv] *)

Lemma V_benv_irrel : forall P S,
  forall k η benv1 benv2,
  lc_ty_at k S ->
  (forall i, i < k -> forall a b,
      nth i benv1 DefaultRel a b <-> nth i benv2 DefaultRel a b) ->
  forall a b, V P S η benv1 a b <-> V P S η benv2 a b.
Proof.
  intros P S. induction S as [ n | Z | S1 IH1 S2 IH2 | S0 IH0 ];
    intros k η benv1 benv2 Hlc Hagree a b.
  - simpl. inversion Hlc; subst.
    match goal with
    | Hn : n < k |- _ => rewrite (Hagree n Hn a b); tauto
    end.
  - simpl. tauto.
  - simpl. inversion Hlc; subst.
    assert (IH1' : forall a b, V P S1 η benv1 a b <-> V P S1 η benv2 a b).
    { apply IH1 with (k := k); auto. }
    assert (IH2' : forall a b, V P S2 η benv1 a b <-> V P S2 η benv2 a b).
    { apply IH2 with (k := k); auto. }
    split.
    + intros [Ha [Hb H]]. repeat split; auto. intros a1 a2 Harg.
      apply (proj2 (IH1' a1 a2)) in Harg.
      destruct (H a1 a2 Harg) as [v1 [v2 [M1 [M2 Hv]]]].
      exists v1, v2. split; [exact M1 | split; [exact M2 |]].
      apply (proj1 (IH2' v1 v2)); exact Hv.
    + intros [Ha [Hb H]]. repeat split; auto. intros a1 a2 Harg.
      apply (proj1 (IH1' a1 a2)) in Harg.
      destruct (H a1 a2 Harg) as [v1 [v2 [M1 [M2 Hv]]]].
      exists v1, v2. split; [exact M1 | split; [exact M2 |]].
      apply (proj2 (IH2' v1 v2)); exact Hv.
  - simpl. inversion Hlc; subst.
    assert (IH0' : forall R a0 b0,
      V P S0 η (R :: benv1) a0 b0 <-> V P S0 η (R :: benv2) a0 b0).
    { intros R a0 b0. apply IH0 with (k := S k); auto.
      intros i Hi a1 b1. destruct i as [| i]; simpl.
      - tauto.
      - apply Hagree. lia. }
    split.
    + intros [Ha [Hb H]]. repeat split; auto. intros U R HlcU HAdm.
      destruct (H U R HlcU HAdm) as [v1 [v2 [M1 [M2 Hv]]]].
      exists v1, v2. split; [exact M1 | split; [exact M2 |]].
      apply (proj1 (IH0' R v1 v2)); exact Hv.
    + intros [Ha [Hb H]]. repeat split; auto. intros U R HlcU HAdm.
      destruct (H U R HlcU HAdm) as [v1 [v2 [M1 [M2 Hv]]]].
      exists v1, v2. split; [exact M1 | split; [exact M2 |]].
      apply (proj2 (IH0' R v1 v2)); exact Hv.
Qed.



(** ** Inversion lemmas for locally closed types *)

Lemma lc_ty_at_bvar_inv : forall k n, lc_ty_at k (Ty_BVar n) -> n < k.
Proof. intros. inversion H. assumption. Qed.

Lemma lc_ty_at_arrow_inv : forall k S1 S2,
  lc_ty_at k (Ty_Arrow S1 S2) -> lc_ty_at k S1 /\ lc_ty_at k S2.
Proof. intros. inversion H. split; assumption. Qed.

Lemma lc_ty_at_all_inv : forall k S0,
  lc_ty_at k (Ty_All S0) -> lc_ty_at (S k) S0.
Proof. intros. inversion H. assumption. Qed.

(** ** Reading a bound type variable back as a free one *)

Lemma sem_open_gen : forall P S,
  forall j X R η (Λs : list VRel) benv,
  length Λs = j ->
  ~ In X (fvs_ty S) ->
  lc_ty_at (j + 1) S ->
  forall a b,
    V P (open_ty_rec j (Ty_FVar X) S) (upd η X R) (Λs ++ benv) a b <->
    V P S η (Λs ++ R :: benv) a b.
Proof.
  intros P S. induction S as [ n | Z | S1 IH1 S2 IH2 | S0 IH0 ];
    intros j X R η Λs benv Hlen Hfresh Hlc a b.
  - (* bound variable *) simpl.
    pose proof (lc_ty_at_bvar_inv _ _ Hlc) as Hn.
    destruct (Nat.eqb j n) eqn:E; simpl.
    + apply Nat.eqb_eq in E.
      assert (E1 : nth n (Λs ++ R :: benv) DefaultRel = R).
      { rewrite app_nth2; [| lia]. replace (n - length Λs) with 0 by lia.
        simpl. reflexivity. }
      rewrite E1, upd_eq. tauto.
    + apply Nat.eqb_neq in E.
      assert (Hlt : n < j) by lia.
      assert (E1 : nth n (Λs ++ benv) DefaultRel = nth n Λs DefaultRel).
      { rewrite app_nth1; [reflexivity | lia]. }
      assert (E2 : nth n (Λs ++ R :: benv) DefaultRel = nth n Λs DefaultRel).
      { rewrite app_nth1; [reflexivity | lia]. }
      rewrite E1, E2. tauto.
  - (* free variable *) simpl. assert (HXZ : X <> Z).
    { intro Heq. subst. apply Hfresh. simpl. left. reflexivity. }
    rewrite upd_neq; [| exact HXZ]. tauto.
  - (* arrow *) simpl.
    destruct (lc_ty_at_arrow_inv _ _ _ Hlc) as [Hlc1 Hlc2].
    assert (Hf1 : ~ In X (fvs_ty S1))
      by (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (Hf2 : ~ In X (fvs_ty S2))
      by (intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
    assert (IH1' : forall a0 b0,
      V P (open_ty_rec j (Ty_FVar X) S1) (upd η X R) (Λs ++ benv) a0 b0 <->
      V P S1 η (Λs ++ R :: benv) a0 b0).
    { intros. apply IH1; auto. }
    assert (IH2' : forall a0 b0,
      V P (open_ty_rec j (Ty_FVar X) S2) (upd η X R) (Λs ++ benv) a0 b0 <->
      V P S2 η (Λs ++ R :: benv) a0 b0).
    { intros. apply IH2; auto. }
    split.
    + intros [Ha [Hb H]]. repeat split; auto. intros a1 a2 Harg.
      apply (proj2 (IH1' a1 a2)) in Harg.
      destruct (H a1 a2 Harg) as [v1 [v2 [M1 [M2 Hv]]]].
      exists v1, v2. split; [exact M1 | split; [exact M2 |]].
      apply (proj1 (IH2' v1 v2)); exact Hv.
    + intros [Ha [Hb H]]. repeat split; auto. intros a1 a2 Harg.
      apply (proj1 (IH1' a1 a2)) in Harg.
      destruct (H a1 a2 Harg) as [v1 [v2 [M1 [M2 Hv]]]].
      exists v1, v2. split; [exact M1 | split; [exact M2 |]].
      apply (proj2 (IH2' v1 v2)); exact Hv.
  - (* universal type *) simpl.
    pose proof (lc_ty_at_all_inv _ _ Hlc) as Hlc0.
    assert (IH0' : forall R0 a0 b0,
      V P (open_ty_rec (S j) (Ty_FVar X) S0) (upd η X R) ((R0 :: Λs) ++ benv) a0 b0 <->
      V P S0 η ((R0 :: Λs) ++ R :: benv) a0 b0).
    { intros R0 a0 b0. apply IH0 with (j := S j).
      - simpl. rewrite Hlen. reflexivity.
      - exact Hfresh.
      - replace (S j + 1) with (S (j + 1)) by lia. exact Hlc0. }
    split.
    + intros [Ha [Hb H]]. repeat split; auto. intros U R0 HlcU HAdm.
      destruct (H U R0 HlcU HAdm) as [v1 [v2 [M1 [M2 Hv]]]].
      exists v1, v2. split; [exact M1 | split; [exact M2 |]].
      apply (proj1 (IH0' R0 v1 v2)); exact Hv.
    + intros [Ha [Hb H]]. repeat split; auto. intros U R0 HlcU HAdm.
      destruct (H U R0 HlcU HAdm) as [v1 [v2 [M1 [M2 Hv]]]].
      exists v1, v2. split; [exact M1 | split; [exact M2 |]].
      apply (proj2 (IH0' R0 v1 v2)); exact Hv.
Qed.

(** ** Substituting a closed type for a type variable *)

Lemma sem_subst_gen : forall P S,
  forall j U η (Λs : list VRel) benv,
  length Λs = j ->
  lc_ty_at 0 U ->
  lc_ty_at (j + 1) S ->
  forall a b,
    V P (open_ty_rec j U S) η (Λs ++ benv) a b <->
    V P S η (Λs ++ V P U η benv :: benv) a b.
Proof.
  intros P S. induction S as [ n | Z | S1 IH1 S2 IH2 | S0 IH0 ];
    intros j U η Λs benv Hlen HU Hlc a b.
  - (* bound variable *) simpl.
    pose proof (lc_ty_at_bvar_inv _ _ Hlc) as Hn.
    destruct (Nat.eqb j n) eqn:E; simpl.
    + apply Nat.eqb_eq in E.
      assert (E1 : nth n (Λs ++ V P U η benv :: benv) DefaultRel = V P U η benv).
      { rewrite app_nth2; [| lia]. replace (n - length Λs) with 0 by lia.
        simpl. reflexivity. }
      rewrite E1.
      assert (Eir : forall a0 b0, V P U η (Λs ++ benv) a0 b0 <-> V P U η benv a0 b0).
      { intros a0 b0. apply V_benv_irrel with (k := 0); auto. intros i Hi; lia. }
      split.
      * intro Hv. split.
        -- apply V_value_l with (P := P) (S := U) (η := η) (benv := Λs ++ benv) (b := b); exact Hv.
        -- split.
           ++ apply V_value_r with (P := P) (S := U) (η := η) (benv := Λs ++ benv) (a := a); exact Hv.
           ++ apply (proj1 (Eir a b)); exact Hv.
      * intros [Ha [Hb Hv]]. apply (proj2 (Eir a b)); exact Hv.
    + apply Nat.eqb_neq in E.
      assert (Hlt : n < j) by lia.
      assert (E1 : nth n (Λs ++ benv) DefaultRel = nth n Λs DefaultRel).
      { rewrite app_nth1; [reflexivity | lia]. }
      assert (E2 : nth n (Λs ++ V P U η benv :: benv) DefaultRel = nth n Λs DefaultRel).
      { rewrite app_nth1; [reflexivity | lia]. }
      rewrite E1, E2. tauto.
  - (* free variable *) simpl. tauto.
  - (* arrow *) simpl.
    destruct (lc_ty_at_arrow_inv _ _ _ Hlc) as [Hlc1 Hlc2].
    assert (IH1' : forall a0 b0,
      V P (open_ty_rec j U S1) η (Λs ++ benv) a0 b0 <->
      V P S1 η (Λs ++ V P U η benv :: benv) a0 b0).
    { intros. apply IH1; auto. }
    assert (IH2' : forall a0 b0,
      V P (open_ty_rec j U S2) η (Λs ++ benv) a0 b0 <->
      V P S2 η (Λs ++ V P U η benv :: benv) a0 b0).
    { intros. apply IH2; auto. }
    split.
    + intros [Ha [Hb H]]. repeat split; auto. intros a1 a2 Harg.
      apply (proj2 (IH1' a1 a2)) in Harg.
      destruct (H a1 a2 Harg) as [v1 [v2 [M1 [M2 Hv]]]].
      exists v1, v2. split; [exact M1 | split; [exact M2 |]].
      apply (proj1 (IH2' v1 v2)); exact Hv.
    + intros [Ha [Hb H]]. repeat split; auto. intros a1 a2 Harg.
      apply (proj1 (IH1' a1 a2)) in Harg.
      destruct (H a1 a2 Harg) as [v1 [v2 [M1 [M2 Hv]]]].
      exists v1, v2. split; [exact M1 | split; [exact M2 |]].
      apply (proj2 (IH2' v1 v2)); exact Hv.
  - (* universal type *) simpl.
    pose proof (lc_ty_at_all_inv _ _ Hlc) as Hlc0.
    assert (IH0' : forall R0 a0 b0,
      V P (open_ty_rec (S j) U S0) η ((R0 :: Λs) ++ benv) a0 b0 <->
      V P S0 η ((R0 :: Λs) ++ V P U η benv :: benv) a0 b0).
    { intros R0 a0 b0. apply IH0 with (j := S j).
      - simpl. rewrite Hlen. reflexivity.
      - exact HU.
      - replace (S j + 1) with (S (j + 1)) by lia. exact Hlc0. }
    split.
    + intros [Ha [Hb H]]. repeat split; auto. intros U0 R0 HlcU HAdm.
      destruct (H U0 R0 HlcU HAdm) as [v1 [v2 [M1 [M2 Hv]]]].
      exists v1, v2. split; [exact M1 | split; [exact M2 |]].
      apply (proj1 (IH0' R0 v1 v2)); exact Hv.
    + intros [Ha [Hb H]]. repeat split; auto. intros U0 R0 HlcU HAdm.
      destruct (H U0 R0 HlcU HAdm) as [v1 [v2 [M1 [M2 Hv]]]].
      exists v1, v2. split; [exact M1 | split; [exact M2 |]].
      apply (proj2 (IH0' R0 v1 v2)); exact Hv.
Qed.


(** ** The semantics is invariant under type changes *)

Lemma V_E_trel_same : forall P S,
  (forall η benv,
     (forall X, Adm P (η X)) ->
     (forall R, In R benv -> Adm P R) ->
     forall a a' b b', trel P a a' -> trel P b b' ->
       V P S η benv a b -> V P S η benv a' b')
  /\
  (forall η benv,
     (forall X, Adm P (η X)) ->
     (forall R, In R benv -> Adm P R) ->
     forall a a' b b', trel P a a' -> trel P b b' ->
       E P S η benv a b -> E P S η benv a' b').
Proof.
  intros P S. induction S as [ n | Z | S1 IH1 S2 IH2 | S0 IH0 ].
  - (* bound variable *)
    assert (HV : forall η benv,
      (forall X, Adm P (η X)) -> (forall R, In R benv -> Adm P R) ->
      forall a a' b b', trel P a a' -> trel P b b' ->
        V P (Ty_BVar n) η benv a b -> V P (Ty_BVar n) η benv a' b').
    { intros η benv Hη Hbenv a a' b b' Ha Hb Hv.
      simpl in Hv. destruct Hv as [Hva [Hvb Hrel]].
      simpl. split.
      - apply trel_value with (P := P) (a := a); auto.
      - split.
        + apply trel_value with (P := P) (a := b); auto.
        + apply (Adm_nth P benv n Hbenv a a' b b' Ha Hb Hrel). }
    split.
    + exact HV.
    + intros η benv Hη Hbenv a a' b b' Ha Hb Hv.
      destruct Hv as [v1 [v2 [M1 [M2 Hv]]]].
      destruct (trel_multi P a a' v1 Ha M1) as [v1' [M1' Hv1]].
      destruct (trel_multi P b b' v2 Hb M2) as [v2' [M2' Hv2]].
      exists v1', v2'. split; [exact M1' | split; [exact M2' |]].
      apply (HV η benv Hη Hbenv v1 v1' v2 v2' Hv1 Hv2 Hv).
  - (* free type variable *)
    assert (HV : forall η benv,
      (forall X, Adm P (η X)) -> (forall R, In R benv -> Adm P R) ->
      forall a a' b b', trel P a a' -> trel P b b' ->
        V P (Ty_FVar Z) η benv a b -> V P (Ty_FVar Z) η benv a' b').
    { intros η benv Hη Hbenv a a' b b' Ha Hb Hv.
      simpl in Hv. destruct Hv as [Hva [Hvb Hrel]].
      simpl. split.
      - apply trel_value with (P := P) (a := a); auto.
      - split.
        + apply trel_value with (P := P) (a := b); auto.
        + apply (Hη Z a a' b b' Ha Hb Hrel). }
    split.
    + exact HV.
    + intros η benv Hη Hbenv a a' b b' Ha Hb Hv.
      destruct Hv as [v1 [v2 [M1 [M2 Hv]]]].
      destruct (trel_multi P a a' v1 Ha M1) as [v1' [M1' Hv1]].
      destruct (trel_multi P b b' v2 Hb M2) as [v2' [M2' Hv2]].
      exists v1', v2'. split; [exact M1' | split; [exact M2' |]].
      apply (HV η benv Hη Hbenv v1 v1' v2 v2' Hv1 Hv2 Hv).
  - (* arrow *)
    assert (HV : forall η benv,
      (forall X, Adm P (η X)) -> (forall R, In R benv -> Adm P R) ->
      forall a a' b b', trel P a a' -> trel P b b' ->
        V P (Ty_Arrow S1 S2) η benv a b -> V P (Ty_Arrow S1 S2) η benv a' b').
    { intros η benv Hη Hbenv a a' b b' Ha Hb Hv.
      simpl in Hv. destruct Hv as [Hva [Hvb H]].
      simpl. split.
      - apply trel_value with (P := P) (a := a); auto.
      - split.
        + apply trel_value with (P := P) (a := b); auto.
        + intros a1 a2 Harg.
          assert (Ht1 : trel P (tm_app a a1) (tm_app a' a1)).
          { apply trel_app; [exact Ha | apply trel_refl]. }
          assert (Ht2 : trel P (tm_app b a2) (tm_app b' a2)).
          { apply trel_app; [exact Hb | apply trel_refl]. }
          exact (proj2 IH2 η benv Hη Hbenv
                   (tm_app a a1) (tm_app a' a1) (tm_app b a2) (tm_app b' a2)
                   Ht1 Ht2 (H a1 a2 Harg)). }
    split.
    + exact HV.
    + intros η benv Hη Hbenv a a' b b' Ha Hb Hv.
      destruct Hv as [v1 [v2 [M1 [M2 Hv]]]].
      destruct (trel_multi P a a' v1 Ha M1) as [v1' [M1' Hv1]].
      destruct (trel_multi P b b' v2 Hb M2) as [v2' [M2' Hv2]].
      exists v1', v2'. split; [exact M1' | split; [exact M2' |]].
      apply (HV η benv Hη Hbenv v1 v1' v2 v2' Hv1 Hv2 Hv).
  - (* universal type *)
    assert (HV : forall η benv,
      (forall X, Adm P (η X)) -> (forall R, In R benv -> Adm P R) ->
      forall a a' b b', trel P a a' -> trel P b b' ->
        V P (Ty_All S0) η benv a b -> V P (Ty_All S0) η benv a' b').
    { intros η benv Hη Hbenv a a' b b' Ha Hb Hv.
      simpl in Hv. destruct Hv as [Hva [Hvb H]].
      simpl. split.
      - apply trel_value with (P := P) (a := a); auto.
      - split.
        + apply trel_value with (P := P) (a := b); auto.
        + intros U R HlcU HAdm.
          assert (HbenvR : forall R0, In R0 (R :: benv) -> Adm P R0).
          { intros R0 [Heq | Hin].
            - subst. exact HAdm.
            - apply Hbenv. exact Hin. }
          assert (Ht1 : trel P (tm_tapp a U) (tm_tapp a' U)).
          { apply trel_tapp; [exact Ha | apply tsub_refl]. }
          assert (Ht2 : trel P (tm_tapp b U) (tm_tapp b' U)).
          { apply trel_tapp; [exact Hb | apply tsub_refl]. }
          exact (proj2 IH0 η (R :: benv) Hη HbenvR
                   (tm_tapp a U) (tm_tapp a' U) (tm_tapp b U) (tm_tapp b' U)
                   Ht1 Ht2 (H U R HlcU HAdm)). }
    split.
    + exact HV.
    + intros η benv Hη Hbenv a a' b b' Ha Hb Hv.
      destruct Hv as [v1 [v2 [M1 [M2 Hv]]]].
      destruct (trel_multi P a a' v1 Ha M1) as [v1' [M1' Hv1]].
      destruct (trel_multi P b b' v2 Hb M2) as [v2' [M2' Hv2]].
      exists v1', v2'. split; [exact M1' | split; [exact M2' |]].
      apply (HV η benv Hη Hbenv v1 v1' v2 v2' Hv1 Hv2 Hv).
Qed.

Lemma Adm_V : forall P T η benv,
  (forall X, Adm P (η X)) ->
  (forall R, In R benv -> Adm P R) ->
  Adm P (V P T η benv).
Proof.
  intros P T η benv Hη Hbenv a a' b b' Ha Hb Hv.
  exact (proj1 (V_E_trel_same P T) η benv Hη Hbenv a a' b b' Ha Hb Hv).
Qed.


(** ================================================================== *)
(** * Stage 3: environments and the fundamental theorem                *)
(** ================================================================== *)

Lemma value_lc : forall t, value t -> locally_closed_tm t.
Proof. intros t H. destruct H; assumption. Qed.

Lemma wf_ty_weaken : forall Delta T, wf_ty Delta T ->
  forall Delta', (forall Z, In Z Delta -> In Z Delta') -> wf_ty Delta' T.
Proof.
  intros Delta T H.
  induction H as
    [ Delta X Hin | Delta T1 T2 H1 IH1 H2 IH2 | L Delta T Hbody IHbody ];
    intros Delta' Hsub.
  - apply WF_Var. apply Hsub. exact Hin.
  - apply WF_Arrow; auto.
  - apply WF_All with (L := L). intros Y HY.
    apply (IHbody Y HY (Y :: Delta')).
    intros Z [-> | Hin].
    + left. reflexivity.
    + right. apply Hsub. exact Hin.
Qed.

Lemma fvs_ty_open_rec_incl : forall T j V,
  incl (fvs_ty T) (fvs_ty (open_ty_rec j V T)).
Proof.
  induction T as [ n | x | T1 IH1 T2 IH2 | T1 IH1 ]; intros j V.
  - simpl. apply incl_nil_l.
  - simpl. apply incl_refl.
  - simpl. intros x Hx. destruct (in_app_or _ _ _ Hx) as [H1 | H2].
    + apply in_or_app. left. apply (IH1 j V). exact H1.
    + apply in_or_app. right. apply (IH2 j V). exact H2.
  - simpl. apply IH1.
Qed.

Lemma wf_ty_fvs : forall Delta T, wf_ty Delta T ->
  forall Z, In Z (fvs_ty T) -> In Z Delta.
Proof.
  intros Delta T H.
  induction H as
    [ Delta X Hin | Delta T1 T2 H1 IH1 H2 IH2 | L Delta T Hbody IHbody ].
  - intros Z HinZ. simpl in HinZ. destruct HinZ as [-> | []]. exact Hin.
  - intros Z HinZ. simpl in HinZ.
    destruct (in_app_or _ _ _ HinZ) as [Hin | Hin]; auto.
  - intros Z HinZ. simpl in HinZ.
    set (X0 := fresh (L ++ fvs_ty T)).
    assert (HX0L : ~ In X0 L) by (apply fresh_notin_1).
    assert (HX0T : ~ In X0 (fvs_ty T)).
    { unfold X0. intro Hin. apply (fresh_notin (L ++ fvs_ty T)).
      apply in_or_app. right. exact Hin. }
    pose proof (IHbody X0 HX0L Z) as Hsub.
    assert (Hin' : In Z (fvs_ty (open_ty T (Ty_FVar X0)))).
    { apply (fvs_ty_open_rec_incl T 0 (Ty_FVar X0)). exact HinZ. }
    apply Hsub in Hin'.
    destruct Hin' as [Heq | HinDelta].
    + subst. exfalso. apply HX0T. exact HinZ.
    + exact HinDelta.
Qed.

Definition ctx_wf (Delta : ty_context) (Gamma : context) : Prop :=
  forall x T, lookup_context x Gamma = Some T -> wf_ty Delta T.

Definition env_rel (P : list atom) (η : atom -> VRel) (benv : list VRel)
    (Gamma : context) (σ1 σ2 : atom -> tm) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    E P T η benv (σ1 x) (σ2 x).

Definition upd_tm (σ : atom -> tm) (x : atom) (s : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then s else σ y.

Lemma upd_tm_eq : forall σ x s, upd_tm σ x s x = s.
Proof. intros. unfold upd_tm. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma upd_tm_neq : forall σ x s y, x <> y -> upd_tm σ x s y = σ y.
Proof.
  intros. unfold upd_tm. apply Nat.eqb_neq in H. rewrite H. reflexivity.
Qed.

Lemma subst_map_upd : forall t σ x s,
  ~ In x (fvs_tm t) -> subst_map (upd_tm σ x s) t = subst_map σ t.
Proof.
  intros t.
  induction t as [ n | a | T t0 IH0 | t1 IH1 t2 IH2 | t0 IH0 | t0 IH0 T | t1 IH1 t2 IH2 ];
    intros σ x s Hfresh; simpl.
  - reflexivity.
  - unfold upd_tm. destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply Hfresh. simpl. left. reflexivity.
    + reflexivity.
  - rewrite IH0; auto. intros Hin. apply Hfresh. simpl. apply in_or_app. right. exact Hin.
  - rewrite IH1; auto. rewrite IH2; auto.
    + intros Hin. apply Hfresh. simpl. apply in_or_app. right. exact Hin.
    + intros Hin. apply Hfresh. simpl. apply in_or_app. left. exact Hin.
  - rewrite IH0; auto.
  - rewrite IH0; auto. intros Hin. apply Hfresh. simpl. apply in_or_app. left. exact Hin.
  - rewrite IH1; auto. rewrite IH2; auto.
    + intros Hin. apply Hfresh. simpl. apply in_or_app. right. exact Hin.
    + intros Hin. apply Hfresh. simpl. apply in_or_app. left. exact Hin.
Qed.

Lemma V_env_irrel : forall P S,
  forall η η' benv,
  (forall Z, In Z (fvs_ty S) -> η Z = η' Z) ->
  forall a b, V P S η benv a b <-> V P S η' benv a b.
Proof.
  intros P S. induction S as [ n | Z | S1 IH1 S2 IH2 | S0 IH0 ];
    intros η η' benv Hagree a b.
  - simpl. tauto.
  - simpl. rewrite (Hagree Z (or_introl eq_refl)). tauto.
  - simpl.
    assert (IH1' : forall a0 b0, V P S1 η benv a0 b0 <-> V P S1 η' benv a0 b0).
    { intros. apply IH1. intros Z0 Hin. apply Hagree. apply in_or_app. left. exact Hin. }
    assert (IH2' : forall a0 b0, V P S2 η benv a0 b0 <-> V P S2 η' benv a0 b0).
    { intros. apply IH2. intros Z0 Hin. apply Hagree. apply in_or_app. right. exact Hin. }
    split.
    + intros [Ha [Hb H]]. repeat split; auto. intros a1 a2 Harg.
      apply (proj2 (IH1' a1 a2)) in Harg.
      destruct (H a1 a2 Harg) as [v1 [v2 [M1 [M2 Hv]]]].
      exists v1, v2. split; [exact M1 | split; [exact M2 |]].
      apply (proj1 (IH2' v1 v2)); exact Hv.
    + intros [Ha [Hb H]]. repeat split; auto. intros a1 a2 Harg.
      apply (proj1 (IH1' a1 a2)) in Harg.
      destruct (H a1 a2 Harg) as [v1 [v2 [M1 [M2 Hv]]]].
      exists v1, v2. split; [exact M1 | split; [exact M2 |]].
      apply (proj2 (IH2' v1 v2)); exact Hv.
  - simpl.
    assert (IH0' : forall R a0 b0,
      V P S0 η (R :: benv) a0 b0 <-> V P S0 η' (R :: benv) a0 b0).
    { intros. apply IH0. intros Z0 Hin. apply Hagree. exact Hin. }
    split.
    + intros [Ha [Hb H]]. repeat split; auto. intros U R HlcU HAdm.
      destruct (H U R HlcU HAdm) as [v1 [v2 [M1 [M2 Hv]]]].
      exists v1, v2. split; [exact M1 | split; [exact M2 |]].
      apply (proj1 (IH0' R v1 v2)); exact Hv.
    + intros [Ha [Hb H]]. repeat split; auto. intros U R HlcU HAdm.
      destruct (H U R HlcU HAdm) as [v1 [v2 [M1 [M2 Hv]]]].
      exists v1, v2. split; [exact M1 | split; [exact M2 |]].
      apply (proj2 (IH0' R v1 v2)); exact Hv.
Qed.

Lemma E_env_irrel : forall P S,
  forall η η' benv,
  (forall Z, In Z (fvs_ty S) -> η Z = η' Z) ->
  forall a b, E P S η benv a b <-> E P S η' benv a b.
Proof.
  intros P S η η' benv Hagree a b.
  assert (HV : forall a0 b0, V P S η benv a0 b0 <-> V P S η' benv a0 b0)
    by (intros; apply V_env_irrel; auto).
  unfold E. split.
  - intros [v1 [v2 [M1 [M2 Hv]]]]. exists v1, v2.
    split; [exact M1 | split; [exact M2 |]].
    apply (proj1 (HV v1 v2)); exact Hv.
  - intros [v1 [v2 [M1 [M2 Hv]]]]. exists v1, v2.
    split; [exact M1 | split; [exact M2 |]].
    apply (proj2 (HV v1 v2)); exact Hv.
Qed.


Lemma ty_subst_same_var : forall X U, ty_subst X U (Ty_FVar X) = U.
Proof. intros. simpl. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma fresh_notin_comp : forall (L0 L : list atom),
  (forall x, In x L -> In x L0) -> ~ In (fresh L0) L.
Proof.
  intros L0 L H Hin. apply (fresh_notin L0). apply H. exact Hin.
Qed.

(** ** The fundamental theorem *)

Theorem fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T -> ctx_wf Delta Gamma ->
  forall P η benv σ1 σ2,
    (forall X, Adm P (η X)) ->
    (forall R, In R benv -> Adm P R) ->
    (forall x, lc_tm_at 0 0 (σ1 x)) ->
    (forall x, lc_tm_at 0 0 (σ2 x)) ->
    env_rel P η benv Gamma σ1 σ2 ->
    E P T η benv (subst_map σ1 t) (subst_map σ2 t).
Proof.
  intros Delta Gamma t T H.
  induction H as
    [ Delta Gamma x T Hlook Hwf
    | L Delta Gamma T1 t2 T2 Hwf Hbody IHbody
    | Delta Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
    | L Delta Gamma t0 T0 Hbody IHbody
    | Delta Gamma t0 T0 U H1 IH1 Hwf
    | Delta Gamma t1 t2 T H1 IH1 H2 IH2 ];
    intros Hctx P η benv σ1 σ2 Hη Hbenv Hlc1 Hlc2 Henv;
      unfold ctx_wf in Hctx; unfold env_rel in Henv.
  - (* T_Var *) apply Henv. exact Hlook.
  - (* T_Abs *)
    apply V_to_E.
    assert (HlcT1 : lc_ty_at 0 T1) by (eapply wf_ty_lc; eauto).
    assert (Hlcbody : lc_tm_at 0 1 t2).
    { eapply open_tm_rec_lc_inv with (k := 0) (s := tm_fvar (fresh (L ++ fvs_tm t2))).
      - constructor.
      - exact (has_type_lc_tm Delta (update Gamma (fresh (L ++ fvs_tm t2)) T1)
                 (open_tm t2 (tm_fvar (fresh (L ++ fvs_tm t2)))) T2
                 (Hbody (fresh (L ++ fvs_tm t2)) (fresh_notin_1 _ _))). }
    assert (Hlu1 : lc_tm_at 0 1 (subst_map σ1 t2))
      by (apply lc_tm_subst_map with (K := 0) (k := 1); auto).
    assert (Hlu2 : lc_tm_at 0 1 (subst_map σ2 t2))
      by (apply lc_tm_subst_map with (K := 0) (k := 1); auto).
    simpl. split.
    + apply v_abs. simpl. constructor; auto.
    + split.
      * apply v_abs. simpl. constructor; auto.
      * intros a1 a2 Harg.
        assert (Hval1 : value a1) by (eapply V_value_l; eauto).
        assert (Hval2 : value a2) by (eapply V_value_r; eauto).
        set (x := fresh (L ++ fvs_tm t2)).
        assert (HxL : ~ In x L) by (apply fresh_notin_1).
        assert (Hxt2 : ~ In x (fvs_tm t2)) by (apply fresh_notin_2).
        assert (Hctx' : ctx_wf Delta (update Gamma x T1)).
        { intros y Ty Hlook. unfold update in Hlook. simpl in Hlook.
          destruct (Nat.eqb y x) eqn:E.
          - apply Nat.eqb_eq in E. subst y. injection Hlook as ->. exact Hwf.
          - apply (Hctx y Ty). exact Hlook. }
        assert (Henv' : env_rel P η benv (update Gamma x T1)
                                  (upd_tm σ1 x a1) (upd_tm σ2 x a2)).
        { intros y Ty Hlook. unfold update in Hlook. simpl in Hlook.
          destruct (Nat.eqb y x) eqn:E.
          - apply Nat.eqb_eq in E. subst y. injection Hlook as ->.
            rewrite upd_tm_eq, upd_tm_eq. apply V_to_E. exact Harg.
          - apply Nat.eqb_neq in E.
            rewrite upd_tm_neq; [| intro Hc; apply E; symmetry; exact Hc].
            rewrite upd_tm_neq; [| intro Hc; apply E; symmetry; exact Hc].
            apply Henv. exact Hlook. }
        assert (Hlc1' : forall y, lc_tm_at 0 0 (upd_tm σ1 x a1 y)).
        { intros y. unfold upd_tm. destruct (Nat.eqb x y).
          - apply value_lc. exact Hval1.
          - apply Hlc1. }
        assert (Hlc2' : forall y, lc_tm_at 0 0 (upd_tm σ2 x a2 y)).
        { intros y. unfold upd_tm. destruct (Nat.eqb x y).
          - apply value_lc. exact Hval2.
          - apply Hlc2. }
        pose proof (IHbody x HxL Hctx' P η benv
                      (upd_tm σ1 x a1) (upd_tm σ2 x a2)
                      Hη Hbenv Hlc1' Hlc2' Henv') as Hih.
        assert (Hsub1 : subst_map (upd_tm σ1 x a1) (open_tm t2 (tm_fvar x))
                        = open_tm (subst_map σ1 t2) a1).
        { change (subst_map (upd_tm σ1 x a1) (open_tm_rec 0 (tm_fvar x) t2)
                  = open_tm_rec 0 a1 (subst_map σ1 t2)).
          rewrite (subst_map_open_tm_rec (upd_tm σ1 x a1) t2 0 (tm_fvar x) Hlc1').
          simpl. rewrite upd_tm_eq. rewrite subst_map_upd; auto. }
        assert (Hsub2 : subst_map (upd_tm σ2 x a2) (open_tm t2 (tm_fvar x))
                        = open_tm (subst_map σ2 t2) a2).
        { change (subst_map (upd_tm σ2 x a2) (open_tm_rec 0 (tm_fvar x) t2)
                  = open_tm_rec 0 a2 (subst_map σ2 t2)).
          rewrite (subst_map_open_tm_rec (upd_tm σ2 x a2) t2 0 (tm_fvar x) Hlc2').
          simpl. rewrite upd_tm_eq. rewrite subst_map_upd; auto. }
        assert (Hih' : E P T2 η benv (open_tm (subst_map σ1 t2) a1)
                                     (open_tm (subst_map σ2 t2) a2)).
        { rewrite <- Hsub1, <- Hsub2. exact Hih. }
        destruct Hih' as [w1 [w2 [Mw1 [Mw2 HVw]]]].
        exists w1, w2. split.
        { apply multi_trans with (b := open_tm (subst_map σ1 t2) a1).
          { apply multi_step with (y := open_tm (subst_map σ1 t2) a1).
            { apply ST_AppAbs; [simpl; constructor; auto | exact Hval1]. }
            { apply multi_refl. } }
          { exact Mw1. } }
        { split.
          { apply multi_trans with (b := open_tm (subst_map σ2 t2) a2).
            { apply multi_step with (y := open_tm (subst_map σ2 t2) a2).
              { apply ST_AppAbs; [simpl; constructor; auto | exact Hval2]. }
              { apply multi_refl. } }
            { exact Mw2. } }
          { exact HVw. } }
  - (* T_App *)
    destruct (IH1 Hctx P η benv σ1 σ2 Hη Hbenv Hlc1 Hlc2 Henv)
      as [f1 [f2 [Mf1 [Mf2 HVf]]]].
    destruct (IH2 Hctx P η benv σ1 σ2 Hη Hbenv Hlc1 Hlc2 Henv)
      as [a1 [a2 [Ma1 [Ma2 HVa]]]].
    assert (HlcArg1 : locally_closed_tm (subst_map σ1 t2))
      by (apply lc_tm_subst_map; [exact (has_type_lc_tm Delta Gamma t2 T1 H2) | exact Hlc1]).
    assert (HlcArg2 : locally_closed_tm (subst_map σ2 t2))
      by (apply lc_tm_subst_map; [exact (has_type_lc_tm Delta Gamma t2 T1 H2) | exact Hlc2]).
    simpl in HVf. destruct HVf as [Hvf1 [Hvf2 HVf]].
    destruct (HVf a1 a2 HVa) as [w1 [w2 [Mw1 [Mw2 HVw]]]].
    exists w1, w2. split.
    + apply multi_trans with (b := tm_app f1 a1).
      * apply multi_app_cong.
        -- exact Mf1.
        -- exact Ma1.
        -- exact HlcArg1.
        -- exact Hvf1.
      * exact Mw1.
    + split.
      * apply multi_trans with (b := tm_app f2 a2).
        -- apply multi_app_cong.
           ++ exact Mf2.
           ++ exact Ma2.
           ++ exact HlcArg2.
           ++ exact Hvf2.
        -- exact Mw2.
      * exact HVw.
  - (* T_TAbs *)
    apply V_to_E.
    assert (Hlcbody : lc_tm_at 1 0 t0).
    { eapply open_tm_ty_rec_lc_inv with (K := 0) (U := Ty_FVar (fresh (L ++ fvs_tm t0))).
      - constructor.
      - exact (has_type_lc_tm (fresh (L ++ fvs_tm t0) :: Delta) Gamma
                 (open_tm_ty t0 (Ty_FVar (fresh (L ++ fvs_tm t0))))
                 (open_ty T0 (Ty_FVar (fresh (L ++ fvs_tm t0))))
                 (Hbody (fresh (L ++ fvs_tm t0)) (fresh_notin_1 _ _))). }
    assert (Hlc1_1 : forall y, lc_tm_at 1 0 (σ1 y)).
    { intros y. apply lc_tm_at_mono_K with (K := 0); auto. }
    assert (Hlc2_1 : forall y, lc_tm_at 1 0 (σ2 y)).
    { intros y. apply lc_tm_at_mono_K with (K := 0); auto. }
    assert (Hlu1 : lc_tm_at 1 0 (subst_map σ1 t0))
      by (apply lc_tm_subst_map with (K := 1) (k := 0); auto).
    assert (Hlu2 : lc_tm_at 1 0 (subst_map σ2 t0))
      by (apply lc_tm_subst_map with (K := 1) (k := 0); auto).
    simpl. split.
    + apply v_tabs. simpl. constructor. exact Hlu1.
    + split.
      * apply v_tabs. simpl. constructor. exact Hlu2.
      * intros U R HlcU HAdm.
        set (Lall := L ++ Delta ++ fvs_ty T0
                     ++ fvs_tm (subst_map σ1 t0) ++ fvs_tm (subst_map σ2 t0) ++ P).
        set (X := fresh Lall).
        assert (HXL : ~ In X L).
        { unfold X. apply fresh_notin_comp with (L0 := Lall).
          intros y Hy. unfold Lall. repeat rewrite in_app_iff. tauto. }
        assert (HXDelta : ~ In X Delta).
        { unfold X. apply fresh_notin_comp with (L0 := Lall).
          intros y Hy. unfold Lall. repeat rewrite in_app_iff. tauto. }
        assert (HXfvs : ~ In X (fvs_ty T0)).
        { unfold X. apply fresh_notin_comp with (L0 := Lall).
          intros y Hy. unfold Lall. repeat rewrite in_app_iff. tauto. }
        assert (HXu1 : ~ In X (fvs_tm (subst_map σ1 t0))).
        { unfold X. apply fresh_notin_comp with (L0 := Lall).
          intros y Hy. unfold Lall. repeat rewrite in_app_iff. tauto. }
        assert (HXu2 : ~ In X (fvs_tm (subst_map σ2 t0))).
        { unfold X. apply fresh_notin_comp with (L0 := Lall).
          intros y Hy. unfold Lall. repeat rewrite in_app_iff. tauto. }
        assert (HXP : ~ In X P).
        { unfold X. apply fresh_notin_comp with (L0 := Lall).
          intros y Hy. unfold Lall. repeat rewrite in_app_iff. tauto. }
        assert (Hctx' : ctx_wf (X :: Delta) Gamma).
        { intros y Ty Hlook.
          apply wf_ty_weaken with (Delta := Delta).
          - apply (Hctx y Ty). exact Hlook.
          - intros Z Hin. right. exact Hin. }
        assert (Hη' : forall Z, Adm P (upd η X R Z)).
        { intros Z. unfold upd. destruct (Nat.eqb X Z) eqn:E.
          - exact HAdm.
          - apply Nat.eqb_neq in E. apply Hη. }
        assert (Hbenv' : forall R0, In R0 (R :: benv) -> Adm P R0).
        { intros R0 [Heq | Hin]. subst. exact HAdm. apply Hbenv. exact Hin. }
        assert (Henv' : env_rel P (upd η X R) benv Gamma σ1 σ2).
        { intros y Ty Hlook.
          assert (HAgree : forall Z, In Z (fvs_ty Ty) -> η Z = upd η X R Z).
          { intros Z Hin.
            assert (HZDelta : In Z Delta)
              by (eapply wf_ty_fvs; [apply (Hctx y Ty); exact Hlook | exact Hin]).
            assert (HZX : Z <> X) by (intro Heq; subst Z; apply HXDelta; exact HZDelta).
            unfold upd.
            assert (HXZ : (X =? Z) = false)
              by (apply Nat.eqb_neq; intro Heq; apply HZX; symmetry; exact Heq).
            rewrite HXZ. reflexivity. }
          apply (proj1 (E_env_irrel P Ty η (upd η X R) benv HAgree (σ1 y) (σ2 y))).
          apply Henv. exact Hlook. }
        pose proof (IHbody X HXL Hctx' P (upd η X R) benv σ1 σ2
                      Hη' Hbenv Hlc1 Hlc2 Henv') as Hih.
        assert (Hopen1 : subst_map σ1 (open_tm_ty t0 (Ty_FVar X))
                         = open_tm_ty (subst_map σ1 t0) (Ty_FVar X)).
        { change (subst_map σ1 (open_tm_ty_rec 0 (Ty_FVar X) t0)
                  = open_tm_ty_rec 0 (Ty_FVar X) (subst_map σ1 t0)).
          rewrite (subst_map_open_tm_ty_rec σ1 t0 0 (Ty_FVar X) Hlc1). reflexivity. }
        assert (Hopen2 : subst_map σ2 (open_tm_ty t0 (Ty_FVar X))
                         = open_tm_ty (subst_map σ2 t0) (Ty_FVar X)).
        { change (subst_map σ2 (open_tm_ty_rec 0 (Ty_FVar X) t0)
                  = open_tm_ty_rec 0 (Ty_FVar X) (subst_map σ2 t0)).
          rewrite (subst_map_open_tm_ty_rec σ2 t0 0 (Ty_FVar X) Hlc2). reflexivity. }
        rewrite Hopen1, Hopen2 in Hih.
        destruct Hih as [v1 [v2 [Mv1 [Mv2 HVv]]]].
        assert (HlcT0 : lc_ty_at 1 T0).
        { eapply open_ty_rec_lc_inv with (k := 0) (U := Ty_FVar X).
          - constructor.
          - exact (has_type_lc_ty (X :: Delta) Gamma (open_tm_ty t0 (Ty_FVar X))
                     (open_ty T0 (Ty_FVar X)) (Hbody X HXL)). }
        assert (HVso : V P T0 η (R :: benv) v1 v2).
        { apply (proj1 (sem_open_gen P T0 0 X R η [] benv eq_refl HXfvs HlcT0 v1 v2)).
          exact HVv. }
        assert (HVtr : V P T0 η (R :: benv)
                         (tm_ty_subst X U v1) (tm_ty_subst X U v2)).
        { apply (proj1 (V_E_trel_same P T0) η (R :: benv) Hη Hbenv'
                 v1 (tm_ty_subst X U v1) v2 (tm_ty_subst X U v2)).
          - apply trel_ty_subst; auto.
          - apply trel_ty_subst; auto.
          - exact HVso. }
        assert (Hid1 : tm_ty_subst X U (open_tm_ty (subst_map σ1 t0) (Ty_FVar X))
                       = open_tm_ty (subst_map σ1 t0) U).
        { change (tm_ty_subst X U (open_tm_ty_rec 0 (Ty_FVar X) (subst_map σ1 t0))
                  = open_tm_ty_rec 0 U (subst_map σ1 t0)).
          rewrite (tm_ty_subst_open_tm_ty_rec (subst_map σ1 t0) X U 0 (Ty_FVar X) HlcU).
          rewrite ty_subst_same_var. rewrite tm_ty_subst_id; auto. }
        assert (Hid2 : tm_ty_subst X U (open_tm_ty (subst_map σ2 t0) (Ty_FVar X))
                       = open_tm_ty (subst_map σ2 t0) U).
        { change (tm_ty_subst X U (open_tm_ty_rec 0 (Ty_FVar X) (subst_map σ2 t0))
                  = open_tm_ty_rec 0 U (subst_map σ2 t0)).
          rewrite (tm_ty_subst_open_tm_ty_rec (subst_map σ2 t0) X U 0 (Ty_FVar X) HlcU).
          rewrite ty_subst_same_var. rewrite tm_ty_subst_id; auto. }
        assert (Hmu1 : multi (open_tm_ty (subst_map σ1 t0) U)
                             (tm_ty_subst X U v1)).
        { rewrite <- Hid1. apply multi_tm_ty_subst with (X := X); auto. }
        assert (Hmu2 : multi (open_tm_ty (subst_map σ2 t0) U)
                             (tm_ty_subst X U v2)).
        { rewrite <- Hid2. apply multi_tm_ty_subst with (X := X); auto. }
        exists (tm_ty_subst X U v1), (tm_ty_subst X U v2). split.
        { apply multi_trans with (b := open_tm_ty (subst_map σ1 t0) U).
          { apply multi_step with (y := open_tm_ty (subst_map σ1 t0) U).
            { apply ST_TAppTabs; [simpl; constructor; exact Hlu1 | exact HlcU]. }
            { apply multi_refl. } }
          { exact Hmu1. } }
        { split.
          { apply multi_trans with (b := open_tm_ty (subst_map σ2 t0) U).
            { apply multi_step with (y := open_tm_ty (subst_map σ2 t0) U).
              { apply ST_TAppTabs; [simpl; constructor; exact Hlu2 | exact HlcU]. }
              { apply multi_refl. } }
            { exact Hmu2. } }
          { exact HVtr. } }
  - (* T_TApp *)
    destruct (IH1 Hctx P η benv σ1 σ2 Hη Hbenv Hlc1 Hlc2 Henv)
      as [f1 [f2 [Mf1 [Mf2 HVf]]]].
    assert (HlcU : lc_ty_at 0 U) by (eapply wf_ty_lc; eauto).
    assert (HAdmU : Adm P (V P U η benv)) by (apply Adm_V; auto).
    simpl in HVf. destruct HVf as [Hvf1 [Hvf2 HVf]].
    destruct (HVf U (V P U η benv) HlcU HAdmU)
      as [w1 [w2 [Mw1 [Mw2 HVw]]]].
    assert (Htmp : lc_ty_at 0 (Ty_All T0))
      by (apply (has_type_lc_ty Delta Gamma t0 (Ty_All T0) H1)).
    assert (HlcT0 : lc_ty_at 1 T0) by (apply lc_ty_at_all_inv; exact Htmp).
    assert (HVsub : V P (open_ty T0 U) η benv w1 w2).
    { apply (proj2 (sem_subst_gen P T0 0 U η [] benv eq_refl HlcU HlcT0 w1 w2)).
      exact HVw. }
    exists w1, w2. split.
    + apply multi_trans with (b := tm_tapp f1 U).
      * apply multi_tapp_cong; [exact Mf1 | exact HlcU].
      * exact Mw1.
    + split.
      * apply multi_trans with (b := tm_tapp f2 U).
        -- apply multi_tapp_cong; [exact Mf2 | exact HlcU].
        -- exact Mw2.
      * exact HVsub.
  - (* T_Choice *)
    destruct (IH1 Hctx P η benv σ1 σ2 Hη Hbenv Hlc1 Hlc2 Henv)
      as [v1 [v2 [Mv1 [Mv2 HVv]]]].
    assert (Hlc11 : locally_closed_tm (subst_map σ1 t1))
      by (apply lc_tm_subst_map; [exact (has_type_lc_tm Delta Gamma t1 T H1) | exact Hlc1]).
    assert (Hlc12 : locally_closed_tm (subst_map σ1 t2))
      by (apply lc_tm_subst_map; [exact (has_type_lc_tm Delta Gamma t2 T H2) | exact Hlc1]).
    assert (Hlc21 : locally_closed_tm (subst_map σ2 t1))
      by (apply lc_tm_subst_map; [exact (has_type_lc_tm Delta Gamma t1 T H1) | exact Hlc2]).
    assert (Hlc22 : locally_closed_tm (subst_map σ2 t2))
      by (apply lc_tm_subst_map; [exact (has_type_lc_tm Delta Gamma t2 T H2) | exact Hlc2]).
    exists v1, v2. split.
    + apply multi_trans with (b := subst_map σ1 t1).
      * apply multi_step with (y := subst_map σ1 t1);
          [apply ST_ChoiceLeft; auto | apply multi_refl].
      * exact Mv1.
    + split.
      * apply multi_trans with (b := subst_map σ2 t1).
        -- apply multi_step with (y := subst_map σ2 t1);
           [apply ST_ChoiceLeft; auto | apply multi_refl].
        -- exact Mv2.
      * exact HVv.
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
  intros t Ht U v HwfU Hv HvU.
  set (P := fvs_tm v).
  set (R := fun a b : tm => a -->* v /\ b -->* v).
  set (η0 := fun (_ : atom) (_ : tm) (_ : tm) => False).
  assert (Hη0 : forall X, Adm P (η0 X)).
  { intros X. apply Adm_default. }
  assert (HAdmR : Adm P R).
  { intros a a' b b' Ha Hb [Hva Hvb]. split.
    - destruct (trel_multi P a a' v Ha Hva) as [v' [Hv' Htrel]].
      assert (Hveq : v' = v)
        by (apply (trel_same_of_atoms P v v');
            [intros x Hin; unfold P; exact Hin | exact Htrel]).
      subst. exact Hv'.
    - destruct (trel_multi P b b' v Hb Hvb) as [v' [Hv' Htrel]].
      assert (Hveq : v' = v)
        by (apply (trel_same_of_atoms P v v');
            [intros x Hin; unfold P; exact Hin | exact Htrel]).
      subst. exact Hv'. }
  assert (Hctx : ctx_wf [] empty).
  { intros x T Hlook. unfold empty in Hlook. simpl in Hlook. discriminate. }
  assert (Henv : env_rel P η0 [] empty (fun x => tm_fvar x) (fun x => tm_fvar x)).
  { intros x T Hlook. unfold empty in Hlook. simpl in Hlook. discriminate. }
  assert (Hbenv : forall R0, In R0 [] -> Adm P R0).
  { intros R0 Hin. destruct Hin. }
  pose proof (fundamental [] empty t (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0)))
                Ht Hctx P η0 [] (fun x => tm_fvar x) (fun x => tm_fvar x)
                Hη0 Hbenv (fun x => lc_tm_fvar 0 0 x) (fun x => lc_tm_fvar 0 0 x)
                Henv) as Hfund.
  destruct Hfund as [f1 [f2 [Mf1 [Mf2 HVf]]]].
  simpl in HVf. destruct HVf as [Hvf1 [Hvf2 HVf]].
  destruct (HVf U R (wf_ty_lc [] U HwfU) HAdmR) as [w1 [w2 [Mw1 [Mw2 HVw]]]].
  simpl in HVw. destruct HVw as [Hvw1 [Hvw2 HVw]].
  assert (HVvv : V P (Ty_BVar 0) η0 [R] v v).
  { simpl. split; [exact Hv | split; [exact Hv | split; apply multi_refl]]. }
  destruct (HVw v v HVvv) as [z1 [z2 [Mz1 [Mz2 HVz]]]].
  simpl in HVz. destruct HVz as [Hz1 [Hz2 [Hz1v Hz2v]]].
  assert (Mtw : multi (tm_tapp t U) w1).
  { apply multi_trans with (b := tm_tapp f1 U).
    - apply multi_tapp_cong.
      + rewrite <- (subst_map_id t). exact Mf1.
      + eapply wf_ty_lc; eauto.
    - exact Mw1. }
  assert (Mav : multi (tm_app (tm_tapp t U) v) (tm_app w1 v)).
  { apply multi_app_cong.
    - exact Mtw.
    - apply multi_refl.
    - apply value_lc. exact Hv.
    - exact Hvw1. }
  assert (Mwv : multi (tm_app w1 v) v).
  { apply multi_trans with (b := z1).
    - exact Mz1.
    - exact Hz1v. }
  apply multi_trans with (b := tm_app w1 v).
  - exact Mav.
  - exact Mwv.
Qed.

End SystemFParametricityNondeterminismHardTask.
