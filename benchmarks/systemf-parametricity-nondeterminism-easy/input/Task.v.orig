(** System F parametricity benchmark, Easy variant.
    Features: nondeterminism. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFParametricityNondeterminismEasyTask.

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

Fixpoint max_atom (L : list atom) : atom :=
  match L with
  | [] => 0
  | x :: L' => Nat.max x (max_atom L')
  end.

Definition fresh (L : list atom) : atom := S (max_atom L).

Lemma in_le_max_atom : forall x L,
  In x L -> x <= max_atom L.
Proof.
  induction L; simpl; intros.
  - contradiction.
  - destruct H as [H | H].
    + subst. lia.
    + specialize (IHL H). lia.
Qed.

Lemma fresh_notin : forall L,
  ~ In (fresh L) L.
Proof.
  unfold fresh. intros L H.
  pose proof (in_le_max_atom _ _ H). lia.
Qed.

Inductive multi : tm -> tm -> Prop :=
  | multi_refl : forall x, multi x x
  | multi_step : forall x y z, x --> y -> multi y z -> multi x z.
Notation "t '-->*' u" := (multi t u) (at level 40).


Hint Constructors lc_ty_at lc_tm_at value : core.

Fixpoint fv_ty (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow T1 T2 => fv_ty T1 ++ fv_ty T2
  | Ty_All T1 => fv_ty T1
  end.

Fixpoint fv_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs _ t1 => fv_tm t1
  | tm_app t1 t2 => fv_tm t1 ++ fv_tm t2
  | tm_tabs t1 => fv_tm t1
  | tm_tapp t1 _ => fv_tm t1
  | tm_choice t1 t2 => fv_tm t1 ++ fv_tm t2
  end.

Fixpoint ftv_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_fvar _ => []
  | tm_abs T t1 => fv_ty T ++ ftv_tm t1
  | tm_app t1 t2 => ftv_tm t1 ++ ftv_tm t2
  | tm_tabs t1 => ftv_tm t1
  | tm_tapp t1 T => ftv_tm t1 ++ fv_ty T
  | tm_choice t1 t2 => ftv_tm t1 ++ ftv_tm t2
  end.

Fixpoint ftv_context (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (_, T) :: Gamma' => fv_ty T ++ ftv_context Gamma'
  end.

Fixpoint dom_context (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (x, _) :: Gamma' => x :: dom_context Gamma'
  end.

Lemma lookup_context_update_eq : forall Gamma x T,
  lookup_context x <{ x |-> $(T); Gamma }> = Some T.
Proof.
  intros. unfold update. simpl. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma lookup_context_update_neq : forall Gamma x y T,
  x <> y ->
  lookup_context y <{ x |-> $(T); Gamma }> = lookup_context y Gamma.
Proof.
  intros. unfold update. simpl.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. exfalso. apply H. symmetry. exact E.
  - reflexivity.
Qed.

Lemma lc_ty_at_monotone : forall k k' T,
  lc_ty_at k T ->
  k <= k' ->
  lc_ty_at k' T.
Proof.
  intros k k' T Hlc. generalize dependent k'.
  induction Hlc; intros k' Hle.
  - apply lc_ty_bvar. lia.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; eauto.
  - apply lc_ty_all. apply IHHlc. lia.

Qed.

Lemma lc_tm_at_monotone : forall K k K' k' t,
  lc_tm_at K k t ->
  K <= K' ->
  k <= k' ->
  lc_tm_at K' k' t.
Proof.
  intros K k K' k' t Hlc. generalize dependent K'. generalize dependent k'.
  induction Hlc; intros k' Hk K' HK.
  - apply lc_tm_bvar. lia.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + eapply lc_ty_at_monotone; eauto.
    + apply IHHlc; lia.
  - apply lc_tm_app; eauto.
  - apply lc_tm_tabs. apply IHHlc; lia.
  - apply lc_tm_tapp.
    + apply IHHlc; assumption.
    + eapply lc_ty_at_monotone; eauto.
  - eauto using lc_tm_at.
Qed.

Lemma open_ty_rec_lc_at : forall T k U,
  lc_ty_at k T ->
  open_ty_rec k U T = T.
Proof.
  intros T k U Hlc. induction Hlc; simpl; try rewrite ?IHHlc1, ?IHHlc2;
    try reflexivity.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + reflexivity.
  - rewrite IHHlc. reflexivity.
Qed.

Lemma open_tm_rec_lc_at : forall t K k u,
  lc_tm_at K k t ->
  open_tm_rec k u t = t.
Proof.
  intros t K k u Hlc. induction Hlc; simpl;
    try rewrite ?IHHlc, ?IHHlc1, ?IHHlc2, ?IHHlc3; try reflexivity.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + reflexivity.
Qed.

Lemma open_tm_ty_rec_lc_at : forall t K k U,
  lc_tm_at K k t ->
  open_tm_ty_rec K U t = t.
Proof.
  intros t K k U Hlc. induction Hlc; simpl;
    try rewrite ?IHHlc1, ?IHHlc2, ?IHHlc3; try reflexivity.
  - erewrite open_ty_rec_lc_at; eauto. rewrite IHHlc. reflexivity.
  - rewrite IHHlc. reflexivity.
  - rewrite IHHlc. erewrite open_ty_rec_lc_at; eauto.

Qed.

Lemma lc_ty_at_open_inv : forall T k X,
  lc_ty_at k (open_ty_rec k (Ty_FVar X) T) ->
  lc_ty_at (S k) T.
Proof.
  induction T; intros k X Hlc; simpl in Hlc.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. apply lc_ty_bvar. lia.
    + inversion Hlc; subst. apply lc_ty_bvar. lia.
  - apply lc_ty_fvar.
  - inversion Hlc; subst. apply lc_ty_arrow; eauto.
  - inversion Hlc; subst. apply lc_ty_all. eapply IHT; eauto.

Qed.

Lemma lc_ty_at_open : forall T k U,
  lc_ty_at (S k) T ->
  lc_ty_at k U ->
  lc_ty_at k (open_ty_rec k U T).
Proof.
  induction T; intros k U HT HU; simpl.
  - inversion HT; subst.
    destruct (Nat.eqb k n) eqn:E.
    + exact HU.
    + apply lc_ty_bvar. apply Nat.eqb_neq in E. lia.
  - apply lc_ty_fvar.
  - inversion HT; subst. apply lc_ty_arrow; eauto.
  - inversion HT; subst. apply lc_ty_all.
    apply IHT.
    + assumption.
    + eapply lc_ty_at_monotone.
      * exact HU.
      * lia.

Qed.

Lemma lc_tm_at_open_tm_inv : forall t K k x,
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) ->
  lc_tm_at K (S k) t.
Proof.
  induction t; intros K k x Hlc; simpl in Hlc.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. apply lc_tm_bvar. lia.
    + inversion Hlc; subst. apply lc_tm_bvar. lia.
  - apply lc_tm_fvar.
  - inversion Hlc; subst. apply lc_tm_abs; eauto.
  - inversion Hlc; subst. apply lc_tm_app; eauto.
  - inversion Hlc; subst. apply lc_tm_tabs; eauto.
  - inversion Hlc; subst. apply lc_tm_tapp; eauto.
  - inversion Hlc; subst; eauto using lc_tm_at.
Qed.

Lemma lc_tm_at_open_ty_inv : forall t K k X,
  lc_tm_at K k (open_tm_ty_rec K (Ty_FVar X) t) ->
  lc_tm_at (S K) k t.
Proof.
  induction t; intros K k X Hlc; simpl in Hlc.
  - inversion Hlc; subst. apply lc_tm_bvar. assumption.
  - apply lc_tm_fvar.
  - inversion Hlc; subst. apply lc_tm_abs.
    + eapply lc_ty_at_open_inv; eauto.
    + eapply IHt; eauto.
  - inversion Hlc; subst. apply lc_tm_app; eauto.
  - inversion Hlc; subst. apply lc_tm_tabs. eapply IHt; eauto.
  - inversion Hlc; subst. apply lc_tm_tapp.
    + eapply IHt; eauto.
    + eapply lc_ty_at_open_inv; eauto.
  - inversion Hlc; subst; eauto using lc_tm_at.
Qed.

Lemma wf_ty_lc : forall Delta T,
  wf_ty Delta T ->
  locally_closed_ty T.
Proof.
  intros Delta T Hwf. induction Hwf.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; assumption.
  - unfold locally_closed_ty in *.
    apply lc_ty_all.
    set (X := fresh L).
    apply (lc_ty_at_open_inv T 0 X).
    apply H0. subst X. apply fresh_notin.

Qed.

Lemma typing_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  locally_closed_tm t.
Proof.
  intros Delta Gamma t T Hty. induction Hty.
  - apply lc_tm_fvar.
  - unfold locally_closed_tm in *.
    apply lc_tm_abs.
    + apply wf_ty_lc with Delta. assumption.
    + set (x := fresh L).
      apply (lc_tm_at_open_tm_inv t2 0 0 x).
      apply H1. subst x. apply fresh_notin.
  - apply lc_tm_app; assumption.
  - unfold locally_closed_tm in *.
    apply lc_tm_tabs.
    set (X := fresh L).
    apply (lc_tm_at_open_ty_inv t 0 0 X).
    apply H0. subst X. apply fresh_notin.
  - apply lc_tm_tapp.
    + assumption.
    + apply wf_ty_lc with Delta. assumption.
  - apply lc_tm_choice; assumption.
Qed.

Lemma typing_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  locally_closed_ty T.
Proof.
  intros Delta Gamma t T Hty. induction Hty.
  - apply wf_ty_lc with Delta. assumption.
  - apply lc_ty_arrow.
    + apply wf_ty_lc with Delta. assumption.
    + set (x := fresh L). apply H1 with x.
      subst x. apply fresh_notin.
  - inversion IHHty1; assumption.
  - unfold locally_closed_ty in *.
    apply lc_ty_all.
    set (X := fresh L).
    apply (lc_ty_at_open_inv T 0 X).
    apply H0. subst X. apply fresh_notin.
  - unfold locally_closed_ty in *.
    inversion IHHty; subst.
    apply lc_ty_at_open.
    + assumption.
    + apply wf_ty_lc with Delta. assumption.
  - exact IHHty1.
Qed.

Definition type_substitution := atom -> ty.

Definition term_substitution := atom -> tm.

Definition type_subst_update
    (theta : type_substitution) (X : atom) (U : ty) : type_substitution :=
  fun Y => if Nat.eqb X Y then U else theta Y.

Definition term_subst_update
    (gamma : term_substitution) (x : atom) (u : tm) : term_substitution :=
  fun y => if Nat.eqb x y then u else gamma y.

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
  | tm_choice t1 t2 => tm_choice (instantiate theta gamma t1) (instantiate theta gamma t2)
  end.

Definition type_substitution_closed (theta : type_substitution) : Prop :=
  forall X : atom, locally_closed_ty (theta X).

Definition term_substitution_closed (gamma : term_substitution) : Prop :=
  forall x : atom, locally_closed_tm (gamma x).

Lemma instantiate_ty_lc_at : forall T k theta,
  lc_ty_at k T ->
  type_substitution_closed theta ->
  lc_ty_at k (instantiate_ty theta T).
Proof.
  intros T k theta Hlc. induction Hlc; intros Htheta; simpl.
  - apply lc_ty_bvar. assumption.
  - eapply lc_ty_at_monotone.
    + apply Htheta.
    + lia.
  - apply lc_ty_arrow; auto.
  - apply lc_ty_all. auto.

Qed.

Lemma instantiate_lc_at : forall t K k theta gamma,
  lc_tm_at K k t ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  lc_tm_at K k (instantiate theta gamma t).
Proof.
  intros t K k theta gamma Hlc. induction Hlc; intros Htheta Hgamma; simpl.
  - apply lc_tm_bvar. assumption.
  - eapply lc_tm_at_monotone.
    + apply Hgamma.
    + lia.
    + lia.
  - apply lc_tm_abs.
    + apply instantiate_ty_lc_at; assumption.
    + auto.
  - apply lc_tm_app; auto.
  - apply lc_tm_tabs. auto.
  - apply lc_tm_tapp.
    + auto.
    + apply instantiate_ty_lc_at; assumption.
  - eauto using lc_tm_at.
Qed.

Lemma instantiate_ty_closed : forall theta T,
  locally_closed_ty T ->
  type_substitution_closed theta ->
  locally_closed_ty (instantiate_ty theta T).
Proof.
  intros. apply instantiate_ty_lc_at; assumption.
Qed.

Lemma instantiate_closed : forall theta gamma t,
  locally_closed_tm t ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm (instantiate theta gamma t).
Proof.
  intros. apply instantiate_lc_at; assumption.
Qed.

Lemma type_subst_update_closed : forall theta X U,
  type_substitution_closed theta ->
  locally_closed_ty U ->
  type_substitution_closed (type_subst_update theta X U).
Proof.
  intros theta X U Htheta HU Y. unfold type_subst_update.
  destruct (Nat.eqb X Y); auto.
Qed.

Lemma term_subst_update_closed : forall gamma x u,
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  term_substitution_closed (term_subst_update gamma x u).
Proof.
  intros gamma x u Hgamma Hu y. unfold term_subst_update.
  destruct (Nat.eqb x y); auto.
Qed.

Lemma instantiate_open_tm_rec : forall t k theta gamma x u,
  ~ In x (fv_tm t) ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate theta (term_subst_update gamma x u)
    (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k u (instantiate theta gamma t).
Proof.
  induction t; intros k theta gamma x u Hfresh Htheta Hgamma Hu; simpl in *.
  - destruct (Nat.eqb k n); simpl.
    + unfold term_subst_update. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - assert (x <> a) by (intro; subst; apply Hfresh; auto).
    unfold term_subst_update.
    assert (E : Nat.eqb x a = false) by (apply Nat.eqb_neq; assumption).
    rewrite E.
    symmetry. apply open_tm_rec_lc_at with (K := 0).
    eapply lc_tm_at_monotone.
    + apply Hgamma.
    + lia.
    + lia.
  - rewrite (IHt (S k) theta gamma x u Hfresh Htheta Hgamma Hu).
    reflexivity.
  - rewrite in_app_iff in Hfresh.
    assert (H1 : ~ In x (fv_tm t1)) by intuition.
    assert (H2 : ~ In x (fv_tm t2)) by intuition.
    rewrite (IHt1 k theta gamma x u H1 Htheta Hgamma Hu).
    rewrite (IHt2 k theta gamma x u H2 Htheta Hgamma Hu).
    reflexivity.
  - rewrite (IHt k theta gamma x u Hfresh Htheta Hgamma Hu).
    reflexivity.
  - rewrite (IHt k theta gamma x u Hfresh Htheta Hgamma Hu).
    reflexivity.
  - repeat rewrite in_app_iff in Hfresh.
    rewrite IHt1, IHt2 by (try assumption; intuition). reflexivity.
Qed.

Lemma instantiate_open_tm : forall t theta gamma x u,
  ~ In x (fv_tm t) ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate theta (term_subst_update gamma x u)
    (open_tm t (tm_fvar x)) =
  open_tm (instantiate theta gamma t) u.
Proof.
  intros. unfold open_tm.
  apply instantiate_open_tm_rec; assumption.
Qed.

Lemma instantiate_ty_open_rec : forall T k theta X U,
  ~ In X (fv_ty T) ->
  type_substitution_closed theta ->
  locally_closed_ty U ->
  instantiate_ty (type_subst_update theta X U)
    (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k U (instantiate_ty theta T).
Proof.
  induction T; intros k theta X U Hfresh Htheta HU; simpl in *.
  - destruct (Nat.eqb k n); simpl.
    + unfold type_subst_update. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - assert (X <> a) by (intro; subst; apply Hfresh; auto).
    unfold type_subst_update.
    assert (E : Nat.eqb X a = false) by (apply Nat.eqb_neq; assumption).
    rewrite E.
    symmetry. apply open_ty_rec_lc_at.
    eapply lc_ty_at_monotone.
    + apply Htheta.
    + lia.
  - rewrite in_app_iff in Hfresh.
    assert (H1 : ~ In X (fv_ty T1)) by intuition.
    assert (H2 : ~ In X (fv_ty T2)) by intuition.
    rewrite (IHT1 k theta X U H1 Htheta HU).
    rewrite (IHT2 k theta X U H2 Htheta HU).
    reflexivity.
  - rewrite (IHT (S k) theta X U Hfresh Htheta HU). reflexivity.

Qed.

Lemma instantiate_ty_open : forall T theta X U,
  ~ In X (fv_ty T) ->
  type_substitution_closed theta ->
  locally_closed_ty U ->
  instantiate_ty (type_subst_update theta X U)
    (open_ty T (Ty_FVar X)) =
  open_ty (instantiate_ty theta T) U.
Proof.
  intros. unfold open_ty.
  apply instantiate_ty_open_rec; assumption.
Qed.

Lemma instantiate_open_ty_rec : forall t K theta gamma X U,
  ~ In X (ftv_tm t) ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_ty U ->
  instantiate (type_subst_update theta X U) gamma
    (open_tm_ty_rec K (Ty_FVar X) t) =
  open_tm_ty_rec K U (instantiate theta gamma t).
Proof.
  induction t as
      [i | x | T body IHbody | t1 IH1 t2 IH2 | body IHbody | body IHbody T
      | a IHa b IHb];
    intros K theta gamma X U Hfresh Htheta Hgamma HU; simpl in *.
  - reflexivity.
  - symmetry. apply open_tm_ty_rec_lc_at with (k := 0).
    eapply lc_tm_at_monotone.
    + apply Hgamma.
    + lia.
    + lia.
  - rewrite in_app_iff in Hfresh.
    assert (HT : ~ In X (fv_ty T)) by intuition.
    assert (Hbody : ~ In X (ftv_tm body)) by intuition.
    rewrite (instantiate_ty_open_rec T K theta X U HT Htheta HU).
    rewrite (IHbody K theta gamma X U Hbody Htheta Hgamma HU).
    reflexivity.
  - rewrite in_app_iff in Hfresh.
    assert (H1 : ~ In X (ftv_tm t1)) by intuition.
    assert (H2 : ~ In X (ftv_tm t2)) by intuition.
    rewrite (IH1 K theta gamma X U H1 Htheta Hgamma HU).
    rewrite (IH2 K theta gamma X U H2 Htheta Hgamma HU).
    reflexivity.
  - rewrite (IHbody (S K) theta gamma X U Hfresh Htheta Hgamma HU).
    reflexivity.
  - rewrite in_app_iff in Hfresh.
    assert (Hbody : ~ In X (ftv_tm body)) by intuition.
    assert (HT : ~ In X (fv_ty T)) by intuition.
    rewrite (IHbody K theta gamma X U Hbody Htheta Hgamma HU).
    rewrite (instantiate_ty_open_rec T K theta X U HT Htheta HU).
    reflexivity.
  - rewrite in_app_iff in Hfresh.
    rewrite IHa, IHb by (try assumption; intuition). reflexivity.
Qed.

Lemma instantiate_open_ty : forall t theta gamma X U,
  ~ In X (ftv_tm t) ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_ty U ->
  instantiate (type_subst_update theta X U) gamma
    (open_tm_ty t (Ty_FVar X)) =
  open_tm_ty (instantiate theta gamma t) U.
Proof.
  intros. unfold open_tm_ty.
  apply instantiate_open_ty_rec; assumption.
Qed.

Definition identity_type_substitution : type_substitution :=
  fun X : atom => Ty_FVar X.

Definition identity_term_substitution : term_substitution :=
  fun x : atom => tm_fvar x.

Lemma identity_type_substitution_closed :
  type_substitution_closed identity_type_substitution.
Proof.
  intros X. apply lc_ty_fvar.
Qed.

Lemma identity_term_substitution_closed :
  term_substitution_closed identity_term_substitution.
Proof.
  intros x. apply lc_tm_fvar.
Qed.

Lemma instantiate_ty_identity : forall T,
  instantiate_ty identity_type_substitution T = T.
Proof.
  induction T; simpl; try rewrite ?IHT1, ?IHT2, ?IHT; reflexivity.
Qed.

Lemma instantiate_identity : forall t,
  instantiate identity_type_substitution identity_term_substitution t = t.
Proof.
  induction t; simpl; try rewrite ?IHt1, ?IHt2, ?IHt3, ?IHt;
    try rewrite instantiate_ty_identity; reflexivity.
Qed.

Lemma open_tm_preserves_lc_at : forall t K k u,
  lc_tm_at K (S k) t -> locally_closed_tm u ->
  lc_tm_at K k (open_tm_rec k u t).
Proof.
  induction t; intros K k u Hlc Hu; simpl; inversion Hlc; subst;
    eauto 8 using lc_tm_at.
  destruct (Nat.eqb k n) eqn:E.
  - eapply lc_tm_at_monotone; [exact Hu|lia|lia].
  - apply Nat.eqb_neq in E. apply lc_tm_bvar. lia.
Qed.

Lemma open_tm_ty_preserves_lc_at : forall t K k U,
  lc_tm_at (S K) k t -> locally_closed_ty U ->
  lc_tm_at K k (open_tm_ty_rec K U t).
Proof.
  induction t; intros K k U Hlc HU; simpl; inversion Hlc; subst;
    eauto 8 using lc_tm_at.
  - apply lc_tm_abs.
    + apply lc_ty_at_open; [assumption|].
      eapply lc_ty_at_monotone; [exact HU|lia].
    + eapply IHt; eauto.
  - apply lc_tm_tapp.
    + eapply IHt; eauto.
    + apply lc_ty_at_open; [assumption|].
      eapply lc_ty_at_monotone; [exact HU|lia].
Qed.

Lemma value_regular : forall v, value v -> locally_closed_tm v.
Proof. intros v H. destruct H; try assumption; constructor. Qed.

Lemma lookup_context_ftv : forall Gamma x T X,
  lookup_context x Gamma = Some T -> In X (fv_ty T) -> In X (ftv_context Gamma).
Proof.
  induction Gamma as [|[y U] Gamma IH]; intros x T X Hlookup Hin; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y).
    + injection Hlookup as ->. apply in_or_app. left. exact Hin.
    + apply in_or_app. right. eapply IH; eauto.
Qed.

Inductive evaluates : tm -> tm -> Prop :=
  | EvalValue : forall v, value v -> evaluates v v
  | EvalApp : forall f arg U body v result,
      evaluates f (tm_abs U body) -> evaluates arg v ->
      evaluates (open_tm body v) result -> evaluates (tm_app f arg) result
  | EvalTApp : forall f U body result,
      evaluates f (tm_tabs body) -> locally_closed_ty U ->
      evaluates (open_tm_ty body U) result -> evaluates (tm_tapp f U) result
  | EvalChoiceLeft : forall t1 t2 v,
      evaluates t1 v -> locally_closed_tm t2 -> evaluates (tm_choice t1 t2) v
  | EvalChoiceRight : forall t1 t2 v,
      locally_closed_tm t1 -> evaluates t2 v -> evaluates (tm_choice t1 t2) v.

Lemma evaluates_value : forall t v, evaluates t v -> value v.
Proof.
  intros t v H. induction H; try assumption.
Qed.

Lemma evaluates_lc : forall t v, evaluates t v -> locally_closed_tm t.
Proof.
  intros t v H. induction H.
  - apply value_regular. exact H.
  - apply lc_tm_app; assumption.
  - apply lc_tm_tapp; assumption.
  - apply lc_tm_choice; assumption.
  - apply lc_tm_choice; assumption.
Qed.

Lemma multi_trans : forall t u v, t -->* u -> u -->* v -> t -->* v.
Proof. intros t u v H. induction H; eauto using multi. Qed.

Lemma multi_app_left : forall t u arg,
  t -->* u -> locally_closed_tm arg -> tm_app t arg -->* tm_app u arg.
Proof. intros t u arg H. induction H; eauto using multi, step. Qed.

Lemma multi_app_right : forall f t u,
  value f -> t -->* u -> tm_app f t -->* tm_app f u.
Proof. intros f t u Hv H. induction H; eauto using multi, step. Qed.

Lemma multi_tapp : forall t u U,
  t -->* u -> locally_closed_ty U -> tm_tapp t U -->* tm_tapp u U.
Proof. intros t u U H. induction H; eauto using multi, step. Qed.

Lemma evaluates_smallstep : forall t v, evaluates t v -> t -->* v.
Proof.
  intros t v H. induction H.
  - constructor.
  - eapply multi_trans. apply multi_app_left. exact IHevaluates1.
    eapply evaluates_lc; eauto.
    eapply multi_trans. apply multi_app_right.
    eapply evaluates_value; eauto. exact IHevaluates2.
    eapply multi_step. apply ST_AppAbs.
    apply value_regular. eapply evaluates_value; eauto.
    eapply evaluates_value; eauto. exact IHevaluates3.
  - eapply multi_trans. apply multi_tapp; eauto.
    eapply multi_step. apply ST_TAppTabs; auto.
    apply value_regular. eapply evaluates_value; eauto. exact IHevaluates2.
  - eapply multi_step. apply ST_ChoiceLeft; auto.
    eapply evaluates_lc; eauto. exact IHevaluates.
  - eapply multi_step. apply ST_ChoiceRight; auto.
    eapply evaluates_lc; eauto. exact IHevaluates.
Qed.

Definition binary_relation := tm -> tm -> Prop.

Record binary_candidate := {
  candidate_relation : binary_relation;
  candidate_values : forall v1 v2, candidate_relation v1 v2 -> value v1 /\ value v2
}.

Definition binary_env := atom -> option binary_candidate.
Definition relation_update (rho : binary_env) (X : atom) (a : binary_candidate) :=
  fun Y => if Nat.eqb X Y then Some a else rho Y.

Definition results_match (R : binary_relation) (t1 t2 : tm) : Prop :=
  exists v1 v2,
    evaluates t1 v1 /\ evaluates t2 v2 /\ R v1 v2.

Definition expression_lifting (R : binary_relation) (t1 t2 : tm) : Prop :=
  locally_closed_tm t1 /\ locally_closed_tm t2 /\ results_match R t1 t2.

Fixpoint value_relation (eta : list binary_candidate) (rho : binary_env)
    (T : ty) (v1 v2 : tm) : Prop :=
  match T with
  | Ty_BVar i =>
      match nth_error eta i with Some a => a.(candidate_relation) v1 v2 | None => False end
  | Ty_FVar X =>
      match rho X with Some a => a.(candidate_relation) v1 v2 | None => False end
  | Ty_Arrow T1 T2 =>
      value v1 /\ value v2 /\
      exists U1 body1 U2 body2,
        v1 = tm_abs U1 body1 /\ v2 = tm_abs U2 body2 /\
        forall arg1 arg2, value_relation eta rho T1 arg1 arg2 ->
          expression_lifting (value_relation eta rho T2)
            (open_tm body1 arg1) (open_tm body2 arg2)
  | Ty_All T =>
      value v1 /\ value v2 /\
      exists body1 body2,
        v1 = tm_tabs body1 /\ v2 = tm_tabs body2 /\
        forall (U1 U2 : ty) (a : binary_candidate),
          locally_closed_ty U1 -> locally_closed_ty U2 ->
          expression_lifting (value_relation (a :: eta) rho T)
            (open_tm_ty body1 U1) (open_tm_ty body2 U2)
  end.

Definition expression_relation eta rho T t1 t2 :=
  expression_lifting (value_relation eta rho T) t1 t2.

Lemma value_relation_values : forall eta rho T v1 v2,
  value_relation eta rho T v1 v2 -> value v1 /\ value v2.
Proof.
  intros eta rho T v1 v2 H. destruct T; simpl in H.
  - destruct (nth_error eta n) as [a|]; try contradiction.
    exact (candidate_values a v1 v2 H).
  - destruct (rho a) as [b|]; try contradiction.
    exact (candidate_values b v1 v2 H).
  - tauto.
  - tauto.
Qed.

Definition interpreted_candidate eta rho T : binary_candidate :=
  {| candidate_relation := value_relation eta rho T;
     candidate_values := value_relation_values eta rho T |}.

Lemma expression_lifting_equiv : forall R S,
  (forall v1 v2, R v1 v2 <-> S v1 v2) ->
  forall t1 t2, expression_lifting R t1 t2 <-> expression_lifting S t1 t2.
Proof.
  intros R S H t1 t2. unfold expression_lifting, results_match.
  split; intros [H1 [H2 [v1 [v2 [E1 [E2 HR]]]]]].
  - split; [exact H1|]. split; [exact H2|].
    exists v1, v2. repeat split; try assumption. apply H. exact HR.
  - split; [exact H1|]. split; [exact H2|].
    exists v1, v2. repeat split; try assumption. apply H. exact HR.
Qed.

Lemma value_arrow_equiv : forall eta1 eta2 rho1 rho2 A1 A2 B1 B2,
  (forall v w, value_relation eta1 rho1 A1 v w <-> value_relation eta2 rho2 A2 v w) ->
  (forall v w, value_relation eta1 rho1 B1 v w <-> value_relation eta2 rho2 B2 v w) ->
  forall v w, value_relation eta1 rho1 (Ty_Arrow A1 B1) v w <->
              value_relation eta2 rho2 (Ty_Arrow A2 B2) v w.
Proof.
  intros eta1 eta2 rho1 rho2 A1 A2 B1 B2 HA HB v w.
  cbn [value_relation]. split;
    intros [Hv [Hw [U [b [V [c [Ev [Ew Hmap]]]]]]]];
    split; [exact Hv| |exact Hv|]; split; [exact Hw| |exact Hw|];
    exists U, b, V, c; split; [exact Ev| |exact Ev|];
    split; [exact Ew| |exact Ew|]; intros a1 a2 Harg.
  - apply (proj1 (expression_lifting_equiv _ _ HB _ _)).
    apply Hmap. apply (proj2 (HA a1 a2)). exact Harg.
  - apply (proj2 (expression_lifting_equiv _ _ HB _ _)).
    apply Hmap. apply (proj1 (HA a1 a2)). exact Harg.
Qed.

Lemma value_all_equiv : forall eta1 eta2 rho1 rho2 T1 T2,
  (forall a v w, value_relation (a :: eta1) rho1 T1 v w <->
                 value_relation (a :: eta2) rho2 T2 v w) ->
  forall v w, value_relation eta1 rho1 (Ty_All T1) v w <->
              value_relation eta2 rho2 (Ty_All T2) v w.
Proof.
  intros eta1 eta2 rho1 rho2 T1 T2 H v w.
  cbn [value_relation]. split;
    intros [Hv [Hw [b [c [Ev [Ew Hmap]]]]]];
    split; [exact Hv| |exact Hv|]; split; [exact Hw| |exact Hw|];
    exists b, c; split; [exact Ev| |exact Ev|];
    split; [exact Ew| |exact Ew|]; intros U V a HU HV.
  - apply (proj1 (expression_lifting_equiv _ _ (H a) _ _)). apply Hmap; assumption.
  - apply (proj2 (expression_lifting_equiv _ _ (H a) _ _)). apply Hmap; assumption.
Qed.

Lemma value_relation_env_equiv : forall T k eta1 eta2 rho,
  lc_ty_at k T ->
  (forall i, i < k -> nth_error eta1 i = nth_error eta2 i) ->
  forall v w, value_relation eta1 rho T v w <-> value_relation eta2 rho T v w.
Proof.
  induction T; intros k eta1 eta2 rho Hlc Henv v w.
  - cbn [value_relation]. rewrite Henv; [reflexivity|inversion Hlc; assumption].
  - reflexivity.
  - apply value_arrow_equiv; intros u z; eapply IHT1 || eapply IHT2;
      try (inversion Hlc; eassumption); exact Henv.
  - apply value_all_equiv. intros a u z.
    apply (IHT (S k)); [inversion Hlc; assumption|].
    intros i Hi. destruct i; simpl; [reflexivity|apply Henv; lia].
Qed.

Lemma value_relation_closed_env : forall T eta1 eta2 rho,
  locally_closed_ty T ->
  forall v w, value_relation eta1 rho T v w <-> value_relation eta2 rho T v w.
Proof.
  intros T eta1 eta2 rho Hlc. apply (value_relation_env_equiv T 0); auto.
  intros i Hi. lia.
Qed.

Lemma value_relation_rho_update_irrelevant : forall T eta rho X a,
  ~ In X (fv_ty T) ->
  forall v w, value_relation eta (relation_update rho X a) T v w <->
            value_relation eta rho T v w.
Proof.
  induction T; intros eta rho X b Hfresh v w; simpl in Hfresh.
  - reflexivity.
  - cbn [value_relation]. unfold relation_update.
    destruct (Nat.eqb X a) eqn:E; [apply Nat.eqb_eq in E; subst; tauto|reflexivity].
  - rewrite in_app_iff in Hfresh. apply value_arrow_equiv.
    + apply IHT1. tauto.
    + apply IHT2. tauto.
  - apply value_all_equiv. intros a u z. apply IHT. exact Hfresh.
Qed.

Lemma nth_error_snoc_last : forall (A : Type) (xs : list A) x,
  nth_error (xs ++ [x]) (length xs) = Some x.
Proof.
  intros A xs x. induction xs; simpl; auto.
Qed.

Lemma value_relation_open_relation : forall T k eta rho X a,
  length eta = k -> lc_ty_at (S k) T -> ~ In X (fv_ty T) ->
  forall v w, value_relation (eta ++ [a]) rho T v w <->
    value_relation eta (relation_update rho X a) (open_ty_rec k (Ty_FVar X) T) v w.
Proof.
  induction T; intros k eta rho X b Hlen Hlc Hfresh v w.
  - assert (Hlt : n < S k) by (inversion Hlc; assumption).
    cbn [open_ty_rec]. destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n.
      cbn [value_relation]. rewrite <- Hlen, nth_error_snoc_last.
      unfold relation_update. rewrite Nat.eqb_refl. reflexivity.
    + cbn [value_relation]. rewrite nth_error_app1.
      * reflexivity.
      * apply Nat.eqb_neq in E. lia.
  - cbn [open_ty_rec value_relation]. unfold relation_update.
    destruct (Nat.eqb X a) eqn:E; [apply Nat.eqb_eq in E; subst; simpl in Hfresh; tauto|reflexivity].
  - cbn [open_ty_rec]. apply value_arrow_equiv.
    + apply IHT1 with (k := k); try assumption.
      * inversion Hlc; assumption.
      * simpl in Hfresh. rewrite in_app_iff in Hfresh. tauto.
    + apply IHT2 with (k := k); try assumption.
      * inversion Hlc; assumption.
      * simpl in Hfresh. rewrite in_app_iff in Hfresh. tauto.
  - cbn [open_ty_rec]. apply value_all_equiv. intros a u z.
    apply (IHT (S k) (a :: eta)); simpl; try congruence; try assumption.
    inversion Hlc; assumption.
Qed.

Lemma value_relation_open_type : forall T k eta rho U,
  length eta = k -> lc_ty_at (S k) T -> locally_closed_ty U ->
  forall v w,
    value_relation (eta ++ [interpreted_candidate [] rho U]) rho T v w <->
    value_relation eta rho (open_ty_rec k U T) v w.
Proof.
  induction T; intros k eta rho U Hlen Hlc HU v w.
  - assert (Hlt : n < S k) by (inversion Hlc; assumption).
    cbn [open_ty_rec]. destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n.
      cbn [value_relation]. rewrite <- Hlen, nth_error_snoc_last.
      cbn [interpreted_candidate candidate_relation].
      apply value_relation_closed_env. exact HU.
    + cbn [value_relation]. rewrite nth_error_app1.
      * reflexivity.
      * apply Nat.eqb_neq in E. lia.
  - reflexivity.
  - cbn [open_ty_rec]. apply value_arrow_equiv.
    + apply IHT1 with (k := k); try assumption. inversion Hlc; assumption.
    + apply IHT2 with (k := k); try assumption. inversion Hlc; assumption.
  - cbn [open_ty_rec]. apply value_all_equiv. intros a u z.
    apply (IHT (S k) (a :: eta)); simpl; try congruence; try assumption.
    inversion Hlc; assumption.
Qed.

Lemma value_is_expression : forall eta rho T v w,
  value_relation eta rho T v w -> expression_relation eta rho T v w.
Proof.
  intros eta rho T v w HR.
  destruct (value_relation_values _ _ _ _ _ HR) as [Hv Hw].
  split. apply value_regular; assumption.
  split. apply value_regular; assumption.
  exists v, w. repeat split; eauto using EvalValue.
Qed.

Lemma expression_app : forall eta rho A B f1 f2 t1 t2,
  expression_relation eta rho (Ty_Arrow A B) f1 f2 ->
  expression_relation eta rho A t1 t2 ->
  expression_relation eta rho B (tm_app f1 t1) (tm_app f2 t2).
Proof.
  intros eta rho A B f1 f2 t1 t2
    [Hf1 [Hf2 [vf1 [vf2 [Ef1 [Ef2 HRf]]]]]]
    [Ht1 [Ht2 [va1 [va2 [Ea1 [Ea2 HRa]]]]]].
  split. apply lc_tm_app; assumption.
  split. apply lc_tm_app; assumption.
  destruct HRf as [_ [_ [U1 [body1 [U2 [body2 [E1 [E2 Hmap]]]]]]]].
  subst vf1 vf2.
  destruct (Hmap va1 va2 HRa) as [_ [_ [v1 [v2 [Ebody1 [Ebody2 HR]]]]]].
  exists v1, v2. repeat split; eauto using EvalApp.
Qed.

Lemma expression_tapp : forall eta rho T t1 t2 U1 U2 a,
  expression_relation eta rho (Ty_All T) t1 t2 ->
  locally_closed_ty U1 -> locally_closed_ty U2 ->
  expression_relation (a :: eta) rho T (tm_tapp t1 U1) (tm_tapp t2 U2).
Proof.
  intros eta rho T t1 t2 U1 U2 a
    [H1 [H2 [v1 [v2 [E1 [E2 HR]]]]]] HU1 HU2.
  split. apply lc_tm_tapp; assumption.
  split. apply lc_tm_tapp; assumption.
  destruct HR as [_ [_ [body1 [body2 [Ev1 [Ev2 Hmap]]]]]].
  subst v1 v2.
  destruct (Hmap U1 U2 a HU1 HU2) as [_ [_ [w1 [w2 [Ebody1 [Ebody2 HR]]]]]].
  exists w1, w2. repeat split; eauto using EvalTApp.
Qed.

Lemma expression_choice : forall eta rho T t1 t2 u1 u2,
  expression_relation eta rho T t1 t2 ->
  expression_relation eta rho T u1 u2 ->
  expression_relation eta rho T (tm_choice t1 u1) (tm_choice t2 u2).
Proof.
  intros eta rho T t1 t2 u1 u2
    [Ht1 [Ht2 [v1 [v2 [E1 [E2 HR]]]]]]
    [Hu1 [Hu2 Hother]].
  split. apply lc_tm_choice; assumption.
  split. apply lc_tm_choice; assumption.
  exists v1, v2. repeat split; eauto using EvalChoiceLeft.
Qed.

Definition related_substitutions (rho : binary_env) (Gamma : context)
    (gamma1 gamma2 : term_substitution) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    value_relation [] rho T (gamma1 x) (gamma2 x).

Lemma related_substitutions_update : forall rho Gamma gamma1 gamma2 x T v1 v2,
  related_substitutions rho Gamma gamma1 gamma2 -> value_relation [] rho T v1 v2 ->
  related_substitutions rho (update Gamma x T)
    (term_subst_update gamma1 x v1) (term_subst_update gamma2 x v2).
Proof.
  intros rho Gamma gamma1 gamma2 x T v1 v2 Hrel HV y U Hy.
  unfold update, term_subst_update in *. simpl in Hy.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y. rewrite Nat.eqb_refl.
    injection Hy as ->. exact HV.
  - assert (E' : Nat.eqb x y = false) by
      (apply Nat.eqb_neq; apply Nat.eqb_neq in E; congruence).
    rewrite E'. apply Hrel. exact Hy.
Qed.

Lemma related_substitutions_relation_update : forall rho Gamma gamma1 gamma2 X a,
  related_substitutions rho Gamma gamma1 gamma2 -> ~ In X (ftv_context Gamma) ->
  related_substitutions (relation_update rho X a) Gamma gamma1 gamma2.
Proof.
  intros rho Gamma gamma1 gamma2 X a Hrel Hfresh x T Hlookup.
  assert (Hnot : ~ In X (fv_ty T)).
  { intros Hin. apply Hfresh. eapply lookup_context_ftv; eauto. }
  apply (proj2 (value_relation_rho_update_irrelevant T [] rho X a Hnot _ _)).
  apply Hrel. exact Hlookup.
Qed.

Theorem binary_fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall theta1 theta2 rho gamma1 gamma2,
    type_substitution_closed theta1 -> type_substitution_closed theta2 ->
    term_substitution_closed gamma1 -> term_substitution_closed gamma2 ->
    related_substitutions rho Gamma gamma1 gamma2 ->
    expression_relation [] rho T
      (instantiate theta1 gamma1 t) (instantiate theta2 gamma2 t).
Proof.
  intros Delta Gamma t T Hty.
  induction Hty as
      [Delta Gamma x T Hlookup Hwf
      | L Delta Gamma T1 body T2 Hwf Hbody IHbody
      | Delta Gamma t1 t2 T1 T2 Ht1 IHt1 Ht2 IHt2
      | L Delta Gamma body T Hbody IHbody
      | Delta Gamma t T U Ht IHt HU
      | Delta Gamma t1 t2 T Ht1 IHt1 Ht2 IHt2];
    intros theta1 theta2 rho gamma1 gamma2 Htheta1 Htheta2 Hgamma1 Hgamma2 Hterms.
  - apply value_is_expression. apply Hterms. exact Hlookup.
  - assert (Hwhole : has_type Delta Gamma (tm_abs T1 body) (Ty_Arrow T1 T2)).
    { eapply T_Abs; eauto. }
    assert (Hlc1 : locally_closed_tm (instantiate theta1 gamma1 (tm_abs T1 body))).
    { apply instantiate_closed; try assumption. eapply typing_lc; eauto. }
    assert (Hlc2 : locally_closed_tm (instantiate theta2 gamma2 (tm_abs T1 body))).
    { apply instantiate_closed; try assumption. eapply typing_lc; eauto. }
    apply value_is_expression. cbn [value_relation instantiate].
    split. apply v_abs. exact Hlc1.
    split. apply v_abs. exact Hlc2.
    exists (instantiate_ty theta1 T1), (instantiate theta1 gamma1 body),
      (instantiate_ty theta2 T1), (instantiate theta2 gamma2 body).
    split. reflexivity. split. reflexivity. intros arg1 arg2 Harg.
    destruct (value_relation_values _ _ _ _ _ Harg) as [Hv1 Hv2].
    pose proof (value_regular _ Hv1) as Ha1.
    pose proof (value_regular _ Hv2) as Ha2.
    set (x := fresh (L ++ fv_tm body)).
    assert (Hxall : ~ In x (L ++ fv_tm body)) by (subst x; apply fresh_notin).
    rewrite in_app_iff in Hxall.
    assert (HxL : ~ In x L) by tauto.
    assert (Hxb : ~ In x (fv_tm body)) by tauto.
    pose proof (IHbody x HxL theta1 theta2 rho
      (term_subst_update gamma1 x arg1) (term_subst_update gamma2 x arg2)
      Htheta1 Htheta2
      (term_subst_update_closed _ _ _ Hgamma1 Ha1)
      (term_subst_update_closed _ _ _ Hgamma2 Ha2)
      (related_substitutions_update _ _ _ _ _ _ _ _ Hterms Harg)) as IH.
    rewrite (instantiate_open_tm body theta1 gamma1 x arg1 Hxb Htheta1 Hgamma1 Ha1),
      (instantiate_open_tm body theta2 gamma2 x arg2 Hxb Htheta2 Hgamma2 Ha2) in IH.
    exact IH.
  - apply expression_app with (A := T1); [apply IHt1|apply IHt2]; assumption.
  - assert (Hwhole : has_type Delta Gamma (tm_tabs body) (Ty_All T)).
    { eapply T_TAbs; eauto. }
    assert (Hlc1 : locally_closed_tm (instantiate theta1 gamma1 (tm_tabs body))).
    { apply instantiate_closed; try assumption. eapply typing_lc; eauto. }
    assert (Hlc2 : locally_closed_tm (instantiate theta2 gamma2 (tm_tabs body))).
    { apply instantiate_closed; try assumption. eapply typing_lc; eauto. }
    apply value_is_expression. cbn [value_relation instantiate].
    split. apply v_tabs. exact Hlc1.
    split. apply v_tabs. exact Hlc2.
    exists (instantiate theta1 gamma1 body), (instantiate theta2 gamma2 body).
    split. reflexivity. split. reflexivity. intros U1 U2 a HU1 HU2.
    set (X := fresh (L ++ fv_ty T ++ ftv_tm body ++ ftv_context Gamma)).
    assert (HXall : ~ In X (L ++ fv_ty T ++ ftv_tm body ++ ftv_context Gamma))
      by (subst X; apply fresh_notin).
    repeat rewrite in_app_iff in HXall.
    assert (HXL : ~ In X L) by tauto.
    assert (HXT : ~ In X (fv_ty T)) by tauto.
    assert (HXb : ~ In X (ftv_tm body)) by tauto.
    assert (HXG : ~ In X (ftv_context Gamma)) by tauto.
    pose proof (IHbody X HXL
      (type_subst_update theta1 X U1) (type_subst_update theta2 X U2)
      (relation_update rho X a) gamma1 gamma2
      (type_subst_update_closed _ _ _ Htheta1 HU1)
      (type_subst_update_closed _ _ _ Htheta2 HU2) Hgamma1 Hgamma2
      (related_substitutions_relation_update _ _ _ _ _ _ Hterms HXG)) as IH.
    rewrite (instantiate_open_ty body theta1 gamma1 X U1 HXb Htheta1 Hgamma1 HU1),
      (instantiate_open_ty body theta2 gamma2 X U2 HXb Htheta2 Hgamma2 HU2) in IH.
    assert (HTlc : lc_ty_at 1 T).
    { pose proof (typing_type_lc _ _ _ _ Hwhole) as HH. inversion HH; assumption. }
    apply (proj2 (expression_lifting_equiv _ _
      (value_relation_open_relation T 0 [] rho X a eq_refl HTlc HXT) _ _)). exact IH.
  - cbn [instantiate].
    pose proof (IHt theta1 theta2 rho gamma1 gamma2
      Htheta1 Htheta2 Hgamma1 Hgamma2 Hterms) as HE.
    assert (HUlc : locally_closed_ty U) by (eapply wf_ty_lc; eauto).
    assert (HU1 : locally_closed_ty (instantiate_ty theta1 U)).
    { apply instantiate_ty_closed; assumption. }
    assert (HU2 : locally_closed_ty (instantiate_ty theta2 U)).
    { apply instantiate_ty_closed; assumption. }
    pose proof (expression_tapp [] rho T _ _ _ _
      (interpreted_candidate [] rho U) HE HU1 HU2) as Hout.
    assert (HTlc : lc_ty_at 1 T).
    { pose proof (typing_type_lc _ _ _ _ Ht) as HH. inversion HH; assumption. }
    apply (proj1 (expression_lifting_equiv _ _
      (value_relation_open_type T 0 [] rho U eq_refl HTlc HUlc) _ _)). exact Hout.
  - apply expression_choice; [apply IHt1|apply IHt2]; assumption.
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
  (* Complete the proof of the free theorem. *)
Qed.

End SystemFParametricityNondeterminismEasyTask.
