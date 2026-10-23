(** System F parametricity benchmark, Easy variant.
    Features: nondeterminism. *)

From Stdlib Require Import Arith.PeanoNat Arith.Wf_nat Lists.List Lia FunctionalExtensionality.
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

(* A unary logical relation.  The head of [rho] interprets the type
   variable bound by a universal type; [theta] interprets free type names. *)
Definition value_pred := tm -> Prop.

Fixpoint related_value (theta : atom -> value_pred)
    (rho : list value_pred) (T : ty) (v : tm) : Prop :=
  match T with
  | Ty_BVar n => nth n rho (fun _ => False) v
  | Ty_FVar X => theta X v
  | Ty_Arrow A B =>
      exists S body, v = tm_abs S body /\
        locally_closed_tm v /\
        forall w, related_value theta rho A w ->
          exists z, tm_app v w -->* z /\ value z /\
            related_value theta rho B z
  | Ty_All B =>
      exists body, v = tm_tabs body /\ locally_closed_tm v /\
        forall (U : ty) (P : value_pred), locally_closed_ty U ->
          exists z, tm_tapp v U -->* z /\ value z /\
            related_value theta (P :: rho) B z
  end.

Definition reducible (theta : atom -> value_pred) (rho : list value_pred)
    (T : ty) (t : tm) : Prop :=
  exists v, t -->* v /\ value v /\ related_value theta rho T v.

(* A relational interpretation packages both instantiated types with the
   relation on their values.  Keeping the types in the package is important
   at type application: the relation chosen for a quantified variable need
   not be the structural relation of the type used to instantiate it. *)
Record semantic_type : Type := SemType {
  sem_left_type : ty;
  sem_right_type : ty;
  sem_value_rel : tm -> tm -> Prop
}.

Definition sem_term_rel (R : semantic_type) (t u : tm) : Prop :=
  exists v w, t -->* v /\ u -->* w /\ value v /\ value w /\
    sem_value_rel R v w.

Definition sem_base (A B : ty) (P : tm -> tm -> Prop) : semantic_type :=
  SemType A B P.

Definition sem_arrow (A B : semantic_type) : semantic_type.
Proof.
  refine (SemType (Ty_Arrow (sem_left_type A) (sem_left_type B))
    (Ty_Arrow (sem_right_type A) (sem_right_type B))
    (fun f g => exists T1 b1 T2 b2,
      f = tm_abs T1 b1 /\ g = tm_abs T2 b2 /\
      locally_closed_tm f /\ locally_closed_tm g /\
      forall x y, sem_term_rel A x y ->
        sem_term_rel B (tm_app f x) (tm_app g y))).
Defined.

Definition sem_all (T1 T2 : ty)
    (Body : forall U V, locally_closed_ty U -> locally_closed_ty V ->
      (tm -> tm -> Prop) -> semantic_type) : semantic_type.
Proof.
  exact (SemType (Ty_All T1) (Ty_All T2)
    (fun f g => exists b1 b2,
      f = tm_tabs b1 /\ g = tm_tabs b2 /\
      locally_closed_tm f /\ locally_closed_tm g /\
      forall U V (P : tm -> tm -> Prop) (HU : locally_closed_ty U) (HV : locally_closed_ty V),
        sem_term_rel (Body U V HU HV P) (tm_tapp f U) (tm_tapp g V))).
Defined.

Definition sem_default : semantic_type :=
  sem_base (Ty_BVar 0) (Ty_BVar 0) (fun _ _ => False).

Fixpoint sem_subst_rec (proj : semantic_type -> ty)
    (theta : atom -> semantic_type) (rho : list semantic_type)
    (k : nat) (T : ty) : ty :=
  match T with
  | Ty_BVar n =>
      if n <? k then Ty_BVar n
      else proj (nth (n - k) rho sem_default)
  | Ty_FVar X => proj (theta X)
  | Ty_Arrow A B => Ty_Arrow (sem_subst_rec proj theta rho k A)
                              (sem_subst_rec proj theta rho k B)
  | Ty_All A => Ty_All (sem_subst_rec proj theta rho (S k) A)
  end.

Definition sem_subst (theta : atom -> semantic_type)
    (rho : list semantic_type) (T : ty) : ty :=
  sem_subst_rec sem_left_type theta rho 0 T.

Definition sem_update (theta : atom -> semantic_type) (X : atom)
    (R : semantic_type) : atom -> semantic_type :=
  fun Y => if Nat.eqb X Y then R else theta Y.

Fixpoint sem_insert (k : nat) (R : semantic_type)
    (rho : list semantic_type) : list semantic_type :=
  match k, rho with
  | 0, _ => R :: rho
  | S k', [] => []
  | S k', a :: rho' => a :: sem_insert k' R rho'
  end.

Lemma sem_insert_nth_error : forall k R rho,
  k <= length rho -> forall n,
  (n < k -> nth_error (sem_insert k R rho) n = nth_error rho n) /\
  (n = k -> nth_error (sem_insert k R rho) n = Some R) /\
  (k < n -> nth_error (sem_insert k R rho) n = nth_error rho (Nat.pred n)).
Proof.
  induction k; intros R rho Hlen n; destruct rho as [|a rho']; simpl in *.
  - split; [intros H; lia|]. split; [intros H; subst; reflexivity|].
    intros H. destruct n; [lia|reflexivity].
  - split; [intros H; lia|]. split; [intros H; subst; reflexivity|].
    intros H. destruct n; [lia|reflexivity].
  - lia.
  - split.
    + intros Hn. destruct n as [|n].
      * simpl. reflexivity.
      * simpl. destruct (IHk R rho' ltac:(simpl in Hlen; lia) n)
          as [Hlt [Heq Hgt]]. rewrite Hlt; [reflexivity|lia].
    + split.
      * intros Heq. subst n. simpl.
        destruct (IHk R rho' ltac:(simpl in Hlen; lia) k)
          as [_ [HeqR _]]. apply HeqR. reflexivity.
      * intros Hn. destruct n as [|n]; [lia|]. simpl.
        destruct (IHk R rho' ltac:(simpl in Hlen; lia) n)
          as [Hlt [Heq Hgt]].
        destruct n as [|n]; [lia|]. simpl.
        specialize (Hgt ltac:(lia)).
        change (nth_error (sem_insert k R rho') (S n) = nth_error rho' n).
        exact Hgt.
Qed.

Lemma Nat_ltb_succ_succ_eq : forall n k,
  (S n <? S k) = (n <? k).
Proof.
  intros n k. destruct (S n <? S k) eqn:E1, (n <? k) eqn:E2; try reflexivity;
    apply Nat.ltb_lt in E1 || apply Nat.ltb_ge in E1;
    apply Nat.ltb_lt in E2 || apply Nat.ltb_ge in E2; lia.
Qed.

Lemma Nat_eqb_succ_succ_eq : forall n k,
  Nat.eqb (S n) (S k) = Nat.eqb n k.
Proof.
  intros n k. destruct (Nat.eqb (S n) (S k)) eqn:E1,
    (Nat.eqb n k) eqn:E2; try reflexivity;
    apply Nat.eqb_eq in E1 || apply Nat.eqb_neq in E1;
    apply Nat.eqb_eq in E2 || apply Nat.eqb_neq in E2; lia.
Qed.

Lemma sem_insert_nth : forall k R rho,
  k <= length rho -> forall n,
  nth n (sem_insert k R rho) sem_default =
    if n <? k then nth n rho sem_default
    else if Nat.eqb n k then R else nth (Nat.pred n) rho sem_default.
Proof.
  induction k; intros R rho Hlen n; destruct rho as [|a rho']; simpl in *.
  - destruct n; reflexivity.
  - destruct n; reflexivity.
  - lia.
  - destruct n as [|n].
    + simpl. reflexivity.
    + simpl. rewrite Nat_ltb_succ_succ_eq.
      rewrite (IHk R rho' ltac:(simpl in Hlen; lia) n).
      destruct (n <? k) eqn:Elt; [reflexivity|].
      destruct (Nat.eqb n k) eqn:Eeq; [reflexivity|].
      apply Nat.ltb_ge in Elt. apply Nat.eqb_neq in Eeq.
      destruct n; [lia|]. simpl. reflexivity.
Qed.

Lemma sem_subst_open_rec : forall proj theta X R rho k d T,
  ~ In X (fv_ty T) -> length rho >= k ->
  lc_ty_at (S (k + d)) T ->
  sem_subst_rec proj (sem_update theta X R) rho d
    (open_ty_rec (k + d) (Ty_FVar X) T) =
  sem_subst_rec proj theta (sem_insert k R rho) d T.
Proof.
  intros proj theta X R rho k d T. revert proj theta X R rho k d.
  induction T; intros proj theta X R rho k d Hfresh Hlen Hlc; simpl in *.
  - inversion Hlc; subst.
    destruct (Nat.eqb (k + d) n) eqn:Eopen.
    + apply Nat.eqb_eq in Eopen. subst n.
      unfold sem_subst_rec, sem_update. rewrite Nat.eqb_refl. simpl.
      assert (Edepth : (k + d <? d) = false) by (apply Nat.ltb_ge; lia).
      rewrite Edepth. rewrite Nat.add_sub by lia.
      rewrite sem_insert_nth with (k := k) (R := R) (rho := rho) (n := k) by lia.
      rewrite Nat.ltb_irrefl, Nat.eqb_refl. reflexivity.
    + apply Nat.eqb_neq in Eopen.
      destruct (n <? d) eqn:Edepth.
      * unfold sem_subst_rec. rewrite Edepth. reflexivity.
      * apply Nat.ltb_ge in Edepth.
        assert (Hnk : n - d < k) by lia.
        rewrite sem_insert_nth with (k := k) (R := R) (rho := rho)
          (n := n - d) by lia.
        assert (Eidx : (n - d <? k) = true) by (apply Nat.ltb_lt; exact Hnk).
        unfold sem_subst_rec.
        assert (Edepthb : (n <? d) = false) by (apply Nat.ltb_ge; lia).
        rewrite Edepthb, Eidx. reflexivity.
  - assert (Hneq : X <> a) by (intro Heq; subst; apply Hfresh; simpl; auto).
    unfold sem_subst_rec, sem_update. simpl.
    destruct (Nat.eqb X a) eqn:EX.
    + apply Nat.eqb_eq in EX. contradiction.
    + reflexivity.
  - inversion Hlc; subst.
    assert (Hfresh1 : ~ In X (fv_ty T1)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ In X (fv_ty T2)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    rewrite (IHT1 proj theta X R rho k d Hfresh1 Hlen H2).
    rewrite (IHT2 proj theta X R rho k d Hfresh2 Hlen H3).
    reflexivity.
  - inversion Hlc as [| |K kk B Hbody|]; subst.
    replace (S (k + d)) with (k + S d) in * by lia.
    rewrite (IHT proj theta X R rho k (S d)); [reflexivity|exact Hfresh|exact Hlen|exact H].
Qed.

Lemma sem_subst_env_irrel : forall proj theta Q rho k d T,
  length rho >= k ->
  lc_ty_at (k + d) T ->
  sem_subst_rec proj theta (sem_insert k Q rho) d T =
  sem_subst_rec proj theta rho d T.
Proof.
  intros proj theta Q rho k d T. revert proj theta Q rho k d.
  induction T; intros proj theta Q rho k d Hlen Hlc; simpl in *.
  - inversion Hlc; subst.
    destruct (n <? d) eqn:E.
    + reflexivity.
    + apply Nat.ltb_ge in E. assert (Hnk : n - d < k) by lia.
      rewrite sem_insert_nth with (k := k) (R := Q) (rho := rho) (n := n - d)
        by (simpl in Hlen; lia).
      assert (Eidx : (n - d <? k) = true) by (apply Nat.ltb_lt; exact Hnk).
      rewrite Eidx. reflexivity.
  - reflexivity.
  - inversion Hlc; subst.
    rewrite (IHT1 proj theta Q rho k d Hlen H2).
    rewrite (IHT2 proj theta Q rho k d Hlen H3). reflexivity.
  - inversion Hlc; subst.
    replace (k + S d) with (S (k + d)) in * by lia.
    assert (H1' : lc_ty_at (k + S d) T) by (replace (k + S d) with (S (k + d)) by lia; exact H1).
    rewrite (IHT proj theta Q rho k (S d) Hlen H1').
    reflexivity.
Qed.

Lemma sem_subst_depth_irrel : forall proj theta rho T k d1 d2,
  lc_ty_at k T -> k <= d1 -> k <= d2 ->
  sem_subst_rec proj theta rho d1 T = sem_subst_rec proj theta rho d2 T.
Proof.
  intros proj theta rho T. revert proj theta rho.
  induction T; intros proj theta rho k d1 d2 Hlc Hle1 Hle2; simpl in *.
  - inversion Hlc; subst.
    assert (E1 : (n <? d1) = true) by (apply Nat.ltb_lt; lia).
    assert (E2 : (n <? d2) = true) by (apply Nat.ltb_lt; lia).
    rewrite E1, E2. reflexivity.
  - reflexivity.
  - inversion Hlc; subst.
    rewrite (IHT1 proj theta rho k d1 d2 H2 Hle1 Hle2).
    rewrite (IHT2 proj theta rho k d1 d2 H3 Hle1 Hle2). reflexivity.
  - inversion Hlc; subst.
    rewrite (IHT proj theta rho (S k) (S d1) (S d2) H1 ltac:(lia) ltac:(lia)).
    reflexivity.
Qed.

Fixpoint interpret_type (theta : atom -> semantic_type)
    (rho : list semantic_type) (T : ty) : semantic_type :=
  match T with
  | Ty_BVar n => nth n rho sem_default
  | Ty_FVar X => theta X
  | Ty_Arrow A B => sem_arrow (interpret_type theta rho A)
                              (interpret_type theta rho B)
  | Ty_All B =>
      sem_all (sem_subst_rec sem_left_type theta rho 1 B)
        (sem_subst_rec sem_right_type theta rho 1 B)
        (fun U V _ _ P =>
          interpret_type theta (sem_base U V P :: rho) B)
  end.

Lemma sem_subst_closed_left : forall theta rho d U,
  locally_closed_ty U ->
  sem_subst_rec sem_left_type theta rho d U =
    sem_left_type (interpret_type theta rho U).
Proof.
  intros theta rho d U Hlc. revert theta rho d Hlc.
  induction U; intros theta rho d Hlc; simpl in *.
  - inversion Hlc; lia.
  - reflexivity.
  - inversion Hlc; subst.
    rewrite (IHU1 theta rho d H2), (IHU2 theta rho d H3). reflexivity.
  - inversion Hlc; subst.
    rewrite (sem_subst_depth_irrel sem_left_type theta rho U 1 (S d) 1 H1 ltac:(lia) ltac:(lia)).
    reflexivity.
Qed.

Lemma sem_subst_closed_right : forall theta rho d U,
  locally_closed_ty U ->
  sem_subst_rec sem_right_type theta rho d U =
    sem_right_type (interpret_type theta rho U).
Proof.
  intros theta rho d U Hlc. revert theta rho d Hlc.
  induction U; intros theta rho d Hlc; simpl in *.
  - inversion Hlc; lia.
  - reflexivity.
  - inversion Hlc; subst.
    rewrite (IHU1 theta rho d H2), (IHU2 theta rho d H3). reflexivity.
  - inversion Hlc; subst.
    rewrite (sem_subst_depth_irrel sem_right_type theta rho U 1 (S d) 1 H1 ltac:(lia) ltac:(lia)).
    reflexivity.
Qed.

Lemma sem_subst_open_any : forall proj theta rho k d T U,
  (forall d', sem_subst_rec proj theta rho d' U =
      proj (interpret_type theta rho U)) ->
  locally_closed_ty U -> length rho >= k ->
  lc_ty_at (S (k + d)) T ->
  sem_subst_rec proj theta rho d
    (open_ty_rec (k + d) U T) =
  sem_subst_rec proj theta
    (sem_insert k (interpret_type theta rho U) rho) d T.
Proof.
  intros proj theta rho k d T. revert proj theta rho k d.
  induction T; intros proj theta rho k d U Hclosed HU Hlen Hlc; simpl in *.
  - inversion Hlc; subst.
    destruct (Nat.eqb (k + d) n) eqn:Eopen.
    + apply Nat.eqb_eq in Eopen. subst n.
      rewrite Hclosed.
      unfold sem_subst_rec.
      assert (Edepth : (k + d <? d) = false) by (apply Nat.ltb_ge; lia).
      rewrite Edepth. rewrite Nat.add_sub by lia.
      rewrite sem_insert_nth with (k := k) (R := interpret_type theta rho U)
        (rho := rho) (n := k) by lia.
      rewrite Nat.ltb_irrefl, Nat.eqb_refl. reflexivity.
    + apply Nat.eqb_neq in Eopen.
      destruct (n <? d) eqn:Edepth.
      * unfold sem_subst_rec. rewrite Edepth. reflexivity.
      * apply Nat.ltb_ge in Edepth.
        assert (Hnk : n - d < k) by lia.
        rewrite sem_insert_nth with (k := k) (R := interpret_type theta rho U)
          (rho := rho) (n := n - d) by (simpl in Hlen; lia).
        assert (Eidx : (n - d <? k) = true) by (apply Nat.ltb_lt; exact Hnk).
        unfold sem_subst_rec.
        assert (Edepthb : (n <? d) = false) by (apply Nat.ltb_ge; lia).
        rewrite Edepthb, Eidx. reflexivity.
  - reflexivity.
  - inversion Hlc; subst.
    rewrite (IHT1 proj theta rho k d U Hclosed HU Hlen H2).
    rewrite (IHT2 proj theta rho k d U Hclosed HU Hlen H3). reflexivity.
  - inversion Hlc; subst.
    replace (S (k + d)) with (k + S d) in * by lia.
    rewrite (IHT proj theta rho k (S d) U Hclosed HU Hlen H1).
    reflexivity.
Qed.

Definition sem_equiv (A B : semantic_type) : Prop :=
  sem_left_type A = sem_left_type B /\
  sem_right_type A = sem_right_type B /\
  forall x y, sem_value_rel A x y <-> sem_value_rel B x y.

Lemma sem_term_rel_equiv : forall A B x y,
  sem_equiv A B -> (sem_term_rel A x y <-> sem_term_rel B x y).
Proof.
  intros A B x y [_ [_ Hrel]]. unfold sem_term_rel. split;
    intros [v [w [Hx [Hy [Hv [Hw Hvw]]]]]];
    exists v, w; repeat split; try assumption; apply Hrel; assumption.
Qed.

Lemma sem_equiv_refl : forall A, sem_equiv A A.
Proof. intros; repeat split; try reflexivity; tauto. Qed.

Lemma sem_equiv_sym : forall A B, sem_equiv A B -> sem_equiv B A.
Proof.
  intros A B [H1 [H2 H3]]. split; [symmetry; exact H1|].
  split; [symmetry; exact H2|]. intros x y. specialize (H3 x y). tauto.
Qed.

Lemma sem_arrow_ext : forall A A' B B',
  sem_equiv A A' -> sem_equiv B B' ->
  sem_equiv (sem_arrow A B) (sem_arrow A' B').
Proof.
  intros A A' B B' [HAl [HAr HA]] [HBl [HBr HB]].
  split; [simpl; rewrite HAl, HBl; reflexivity|].
  split; [simpl; rewrite HAr, HBr; reflexivity|].
  intros f g. simpl. split;
    intros [T1 [b1 [T2 [b2 [Hf [Hg [Hlc1 [Hlc2 Hfun]]]]]]]];
    exists T1, b1, T2, b2; repeat split; try assumption; intros x y Hxy.
  - apply sem_term_rel_equiv with (A := B) (B := B'); [split; [exact HBl|split; assumption]|].
    apply Hfun. apply sem_term_rel_equiv with (A := A') (B := A).
    + apply sem_equiv_sym. split; [exact HAl|split; assumption].
    + exact Hxy.
  - apply sem_term_rel_equiv with (A := B') (B := B).
    + apply sem_equiv_sym. split; [exact HBl|split; assumption].
    + apply Hfun. apply sem_term_rel_equiv with (A := A) (B := A').
      * split; [exact HAl|split; assumption].
      * exact Hxy.
Qed.

Lemma sem_all_ext : forall T1 T2 (F G : forall U V,
    locally_closed_ty U -> locally_closed_ty V -> (tm -> tm -> Prop) -> semantic_type),
  (forall U V HU HV P, sem_equiv (F U V HU HV P) (G U V HU HV P)) ->
  sem_equiv (sem_all T1 T2 F) (sem_all T1 T2 G).
Proof.
  intros T1 T2 F G HFG. split; [reflexivity|]. split; [reflexivity|].
  intros f g. simpl. split.
  - intros [b1 [b2 [Hf [Hg [Hlc1 [Hlc2 Hall]]]]]].
    exists b1, b2. repeat split; try assumption. intros U V P HU HV.
    apply sem_term_rel_equiv with (A := F U V HU HV P) (B := G U V HU HV P).
    + apply HFG.
    + apply Hall.
  - intros [b1 [b2 [Hf [Hg [Hlc1 [Hlc2 Hall]]]]]].
    exists b1, b2. repeat split; try assumption. intros U V P HU HV.
    apply sem_term_rel_equiv with (A := G U V HU HV P) (B := F U V HU HV P).
    + apply sem_equiv_sym. apply HFG.
    + apply Hall.
Qed.

Definition sem_env_equiv (rho sigma : list semantic_type) : Prop :=
  length rho = length sigma /\
  forall n, n < length rho -> sem_equiv (nth n rho sem_default) (nth n sigma sem_default).

Lemma sem_env_equiv_cons : forall R S rho sigma,
  sem_equiv R S -> sem_env_equiv rho sigma ->
  sem_env_equiv (R :: rho) (S :: sigma).
Proof.
  intros R S rho sigma HRS [Hlen Henv]. split; simpl; [lia|].
  intros [|n] Hn; simpl.
  - exact HRS.
  - apply Henv. simpl in Hn. lia.
Qed.

Lemma sem_subst_env_congr : forall proj theta rho sigma d T,
  (forall A B, sem_equiv A B -> proj A = proj B) ->
  sem_env_equiv rho sigma ->
  lc_ty_at (length rho + d) T ->
  sem_subst_rec proj theta rho d T = sem_subst_rec proj theta sigma d T.
Proof.
  intros proj theta rho sigma d T Hproj Henv. revert proj theta rho sigma d Hproj Henv.
  induction T; intros proj theta rho sigma d Hproj [Hlen Hrelations] Hlc; simpl in *.
  - inversion Hlc; subst.
    destruct (n <? d) eqn:E; [reflexivity|].
    apply Nat.ltb_ge in E. assert (Hidx : n - d < length rho) by lia.
    specialize (Hrelations (n - d) Hidx) as Hsem.
    rewrite (Hproj _ _ Hsem). reflexivity.
  - reflexivity.
  - inversion Hlc; subst.
    rewrite (IHT1 proj theta rho sigma d Hproj (conj Hlen Hrelations) H2).
    rewrite (IHT2 proj theta rho sigma d Hproj (conj Hlen Hrelations) H3). reflexivity.
  - inversion Hlc; subst.
    assert (H1' : lc_ty_at (length rho + S d) T).
    { replace (length rho + S d) with (S (length rho + d)) by lia. exact H1. }
    rewrite (IHT proj theta rho sigma (S d) Hproj (conj Hlen Hrelations) H1').
    reflexivity.
Qed.

Lemma sem_interp_env_congr : forall theta rho sigma T,
  sem_env_equiv rho sigma ->
  lc_ty_at (length rho) T ->
  sem_equiv (interpret_type theta rho T) (interpret_type theta sigma T).
Proof.
  intros theta rho sigma T Henv. revert theta rho sigma Henv.
  induction T; intros theta rho sigma Henv Hlc; simpl in *.
  - inversion Hlc; subst. destruct Henv as [Hlen Hrel].
    apply Hrel. assumption.
  - apply sem_equiv_refl.
  - inversion Hlc; subst. apply sem_arrow_ext.
    + apply IHT1; assumption.
    + apply IHT2; assumption.
  - inversion Hlc; subst.
    destruct Henv as [Hlen Hrel].
    assert (HlcB1 : lc_ty_at (length rho + 1) T).
    { replace (length rho + 1) with (S (length rho)) by lia. exact H1. }
    pose proof (@sem_subst_env_congr sem_left_type theta rho sigma 1 T
      (fun A B Heq => proj1 Heq)
      (conj Hlen Hrel) HlcB1) as HL.
    pose proof (@sem_subst_env_congr sem_right_type theta rho sigma 1 T
      (fun A B Heq => proj1 (proj2 Heq))
      (conj Hlen Hrel) HlcB1) as HR.
    rewrite HL, HR. apply sem_all_ext.
    intros U V HU HV P.
    apply IHT with (rho := sem_base U V P :: rho)
      (sigma := sem_base U V P :: sigma).
    + apply sem_env_equiv_cons; [apply sem_equiv_refl|]. split; assumption.
    + exact H1.
Qed.

Lemma sem_equiv_trans : forall A B C,
  sem_equiv A B -> sem_equiv B C -> sem_equiv A C.
Proof.
  intros A B C [H1 [H2 H3]] [H4 [H5 H6]].
  split; [congruence|]. split; [congruence|]. intros x y. specialize (H3 x y); specialize (H6 x y). tauto.
Qed.

Lemma sem_insert_env_equiv : forall k R S rho,
  sem_equiv R S -> sem_env_equiv (sem_insert k R rho) (sem_insert k S rho).
Proof.
  induction k; intros R S rho HRS; simpl.
  - apply sem_env_equiv_cons; [exact HRS|]. split; [reflexivity|]. intros n Hn. apply sem_equiv_refl.
  - destruct rho as [|a rho].
    + split; [reflexivity|]. intros n Hn. exfalso. simpl in Hn. lia.
    + simpl. apply sem_env_equiv_cons; [apply sem_equiv_refl|apply IHk; exact HRS].
Qed.

Lemma sem_insert_cons : forall k R Q rho,
  sem_insert (S k) R (Q :: rho) = Q :: sem_insert k R rho.
Proof. destruct k; reflexivity. Qed.

Lemma sem_insert_length : forall k R rho,
  k <= length rho -> length (sem_insert k R rho) = S (length rho).
Proof.
  induction k; intros R rho Hlen; destruct rho as [|a rho']; simpl in *.
  - reflexivity.
  - reflexivity.
  - lia.
  - rewrite IHk by (simpl in Hlen; lia). reflexivity.
Qed.

Lemma sem_interpret_open : forall theta X R rho k T,
  ~ In X (fv_ty T) -> length rho >= k -> lc_ty_at (S k) T ->
  sem_equiv
    (interpret_type (sem_update theta X R) rho
      (open_ty_rec k (Ty_FVar X) T))
    (interpret_type theta (sem_insert k R rho) T).
Proof.
  intros theta X R rho k T. revert theta X R rho k.
  induction T; intros theta X R rho k Hfresh Hlen Hlc; simpl in *.
  - inversion Hlc as [K kk i Hbound| | |]; subst.
    destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n.
      unfold sem_update. simpl. rewrite Nat.eqb_refl.
      rewrite sem_insert_nth with (k := k) (R := R) (rho := rho) (n := k) by lia.
      rewrite Nat.ltb_irrefl, Nat.eqb_refl. apply sem_equiv_refl.
    + apply Nat.eqb_neq in E.
      assert (Hnk : n < k) by lia.
      unfold sem_update. simpl.
      rewrite sem_insert_nth with (k := k) (R := R) (rho := rho) (n := n) by lia.
      assert (El : (n <? k) = true) by (apply Nat.ltb_lt; exact Hnk).
      rewrite El. apply sem_equiv_refl.
  - assert (Hneq : X <> a) by (intro Heq; subst; apply Hfresh; simpl; auto).
    unfold sem_update. simpl. destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E. contradiction.
    + apply sem_equiv_refl.
  - inversion Hlc as [| |K kk A B H1 H2|]; subst.
    assert (Hfresh1 : ~ In X (fv_ty T1)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ In X (fv_ty T2)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    apply sem_arrow_ext.
    + apply IHT1; assumption.
    + apply IHT2; assumption.
  - inversion Hlc as [| | |K kk B Hbody]; subst.
    assert (HfreshB : ~ In X (fv_ty T)). exact Hfresh.
    assert (Hbody : lc_ty_at (S (k + 1)) T) by (replace (S (k + 1)) with (S (S k)) by lia; exact B).
    pose proof (sem_subst_open_rec sem_left_type theta X R rho k 1 T
      HfreshB Hlen Hbody) as Hleft.
    pose proof (sem_subst_open_rec sem_right_type theta X R rho k 1 T
      HfreshB Hlen Hbody) as Hright.
    replace (S k) with (k + 1) by lia.
    rewrite Hleft, Hright.
    apply sem_all_ext.
    intros U V P HU HV.
    replace (k + 1) with (S k) by lia.
    apply IHT with (X := X) (R := R) (k := S k).
    + exact HfreshB.
    + simpl. lia.
    + exact B.
Qed.

Lemma sem_interpret_env_irrel : forall theta Q rho k T,
  length rho >= k -> lc_ty_at k T ->
  sem_equiv (interpret_type theta (sem_insert k Q rho) T)
            (interpret_type theta rho T).
Proof.
  intros theta Q rho k T. revert theta Q rho k.
  induction T; intros theta Q rho k Hlen Hlc; simpl in *.
  - inversion Hlc; subst.
    rewrite sem_insert_nth with (k := k) (R := Q) (rho := rho) (n := n) by lia.
    assert (E : (n <? k) = true) by (apply Nat.ltb_lt; assumption).
    rewrite E. apply sem_equiv_refl.
  - apply sem_equiv_refl.
  - inversion Hlc; subst. apply sem_arrow_ext.
    + apply IHT1; assumption.
    + apply IHT2; assumption.
  - inversion Hlc; subst.
    assert (Hbody : lc_ty_at (k + 1) T) by (replace (k + 1) with (S k) by lia; assumption).
    pose proof (sem_subst_env_irrel sem_left_type theta Q rho k 1 T Hlen Hbody) as HL.
    pose proof (sem_subst_env_irrel sem_right_type theta Q rho k 1 T Hlen Hbody) as HR.
    rewrite HL, HR. apply sem_all_ext.
    intros U V HU HV P.
    apply IHT with (Q := Q) (rho := sem_base U V P :: rho) (k := S k).
    + simpl. lia.
    + exact H1.
Qed.

Lemma sem_interpret_subst : forall theta rho k T U,
  locally_closed_ty U -> length rho >= k -> lc_ty_at (S k) T ->
  sem_equiv
    (interpret_type theta rho (open_ty_rec k U T))
    (interpret_type theta
      (sem_insert k (interpret_type theta rho U) rho) T).
Proof.
  intros theta rho k T. revert theta rho k.
  induction T; intros theta rho k U HU Hlen Hlc; simpl in *.
  - inversion Hlc as [K kk i Hbound| | |]; subst.
    destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n.
      rewrite sem_insert_nth with (k := k) (R := interpret_type theta rho U)
        (rho := rho) (n := k) by lia.
      rewrite Nat.ltb_irrefl, Nat.eqb_refl. apply sem_equiv_refl.
    + apply Nat.eqb_neq in E. assert (Hnk : n < k) by lia.
      rewrite sem_insert_nth with (k := k) (R := interpret_type theta rho U)
        (rho := rho) (n := n) by lia.
      assert (Eidx : (n <? k) = true) by (apply Nat.ltb_lt; exact Hnk).
      rewrite Eidx. apply sem_equiv_refl.
  - apply sem_equiv_refl.
  - inversion Hlc; subst. apply sem_arrow_ext.
    + apply IHT1; assumption.
    + apply IHT2; assumption.
  - inversion Hlc; subst.
    assert (Hbody : lc_ty_at (S (k + 1)) T).
    { replace (S (k + 1)) with (S (S k)) by lia. exact H1. }
    pose proof (@sem_subst_open_any sem_left_type theta rho k 1 T U
      (fun d' => sem_subst_closed_left theta rho d' U HU) HU Hlen Hbody) as Hleft.
    pose proof (@sem_subst_open_any sem_right_type theta rho k 1 T U
      (fun d' => sem_subst_closed_right theta rho d' U HU) HU Hlen Hbody) as Hright.
    replace (S k) with (k + 1) by lia. rewrite Hleft, Hright.
    apply sem_all_ext. intros A B HA HB P.
    set (Q := sem_base A B P).
    set (R := interpret_type theta rho U).
    set (R' := interpret_type theta (Q :: rho) U).
    pose proof (sem_interpret_env_irrel theta Q rho 0 U ltac:(lia) HU) as HUR.
    assert (Htail : sem_env_equiv (sem_insert k R' rho) (sem_insert k R rho)).
    { apply sem_insert_env_equiv. exact HUR. }
    assert (Henv : sem_env_equiv (Q :: sem_insert k R' rho)
      (Q :: sem_insert k R rho)).
    { apply sem_env_equiv_cons; [apply sem_equiv_refl|exact Htail]. }
    assert (HlcT : lc_ty_at (length (Q :: sem_insert k R' rho)) T).
    { simpl. rewrite (@sem_insert_length k R' rho ltac:(lia)).
      eapply lc_ty_at_monotone.
      - exact H1.
      - lia. }
    replace (k + 1) with (S k) by lia.
    pose proof (IHT theta (Q :: rho) (S k) U HU ltac:(simpl; lia) H1) as Hsub.
    eapply sem_equiv_trans.
    + exact Hsub.
    + apply sem_interp_env_congr; assumption.
Qed.

Lemma multi_choice_left : forall t1 t2,
  locally_closed_tm t1 -> locally_closed_tm t2 ->
  tm_choice t1 t2 -->* t1.
Proof. intros; eapply multi_step; [constructor; assumption|constructor]. Qed.

Lemma multi_choice_right : forall t1 t2,
  locally_closed_tm t1 -> locally_closed_tm t2 ->
  tm_choice t1 t2 -->* t2.
Proof. intros; eapply multi_step; [constructor; assumption|constructor]. Qed.

Fixpoint ty_size (T : ty) : nat :=
  match T with
  | Ty_BVar _ | Ty_FVar _ => 1
  | Ty_Arrow A B => S (ty_size A + ty_size B)
  | Ty_All A => S (ty_size A)
  end.

Lemma ty_size_open_ty_rec : forall T k X,
  ty_size (open_ty_rec k (Ty_FVar X) T) <= ty_size T.
Proof.
  induction T; intros; simpl; try lia.
  - destruct (Nat.eqb k n); simpl; lia.
  - specialize (IHT1 k X). specialize (IHT2 k X). lia.
  - specialize (IHT (S k) X). lia.
Qed.

Lemma wf_ty_locally_closed : forall Delta U, wf_ty Delta U -> locally_closed_ty U.
Proof.
  assert (Hgen : forall n, forall Delta U, ty_size U < n ->
      wf_ty Delta U -> locally_closed_ty U).
  { induction n using lt_wf_ind; intros Delta U Hsize Hwf.
    destruct U; simpl in Hsize.
    - inversion Hwf.
    - constructor.
    - inversion Hwf; subst. constructor.
      + eapply H with (m := S (ty_size U1)) (Delta := Delta) (U := U1).
        * simpl in Hsize. lia.
        * simpl. lia.
        * assumption.
      + eapply H with (m := S (ty_size U2)) (Delta := Delta) (U := U2).
        * simpl in Hsize. lia.
        * simpl. lia.
        * assumption.
    - inversion Hwf as [| | L Delta0 B Hall]; subst.
      constructor. apply lc_ty_at_open_inv with (X := fresh L).
      apply H with (m := ty_size (Ty_All U))
        (Delta := fresh L :: Delta).
      + exact Hsize.
      + eapply Nat.le_lt_trans.
        * apply ty_size_open_ty_rec.
        * simpl. lia.
      + apply Hall. apply fresh_notin.
  }
  intros Delta U Hwf. apply Hgen with (n := S (ty_size U)) (Delta := Delta) (U := U).
  - lia.
  - exact Hwf.
Qed.

Lemma wf_ty_weaken : forall Delta E T,
  (forall X, In X Delta -> In X E) -> wf_ty Delta T -> wf_ty E T.
Proof.
  intros Delta E T Hinc Hwf. revert E Hinc. induction Hwf; intros E Hinc.
  - constructor. apply Hinc. assumption.
  - constructor; [apply IHHwf1|apply IHHwf2]; exact Hinc.
  - eapply WF_All with (L := L). intros X HX.
    apply H0; [exact HX|]. intros Y HY. simpl in HY.
    destruct HY as [->|HY]; simpl; auto.
Qed.

Lemma ty_subst_open_fresh : forall X U Y k T,
  locally_closed_ty U ->
  X <> Y ->
  ty_subst X U (open_ty_rec k (Ty_FVar Y) T) =
    open_ty_rec k (Ty_FVar Y) (ty_subst X U T).
Proof.
  intros X U Y k T. revert k. induction T; intros k HU Hneq; simpl.
  - destruct (Nat.eqb k n); simpl.
    + assert (E : Nat.eqb X Y = false) by (apply Nat.eqb_neq; exact Hneq).
      unfold ty_subst. rewrite E. reflexivity.
    + reflexivity.
  - destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E. subst a. assert (Y <> X) by congruence.
      rewrite open_ty_rec_lc_at; [reflexivity|].
      eapply lc_ty_at_monotone; [exact HU|lia].
    + reflexivity.
  - change (Ty_Arrow (ty_subst X U (open_ty_rec k (Ty_FVar Y) T1))
      (ty_subst X U (open_ty_rec k (Ty_FVar Y) T2)) =
      Ty_Arrow (open_ty_rec k (Ty_FVar Y) (ty_subst X U T1))
      (open_ty_rec k (Ty_FVar Y) (ty_subst X U T2))).
    rewrite (IHT1 k HU Hneq), (IHT2 k HU Hneq). reflexivity.
  - change (Ty_All (ty_subst X U (open_ty_rec (S k) (Ty_FVar Y) T)) =
      Ty_All (open_ty_rec (S k) (Ty_FVar Y) (ty_subst X U T))).
    rewrite (IHT (S k) HU Hneq). reflexivity.
Qed.

Lemma wf_ty_subst_prefix : forall pref Delta X T U,
  ~ In X pref ->
  wf_ty (pref ++ X :: Delta) T -> wf_ty Delta U ->
  wf_ty (pref ++ Delta) (ty_subst X U T).
Proof.
  intros pref Delta X T U Hfresh Hwf HU.
  assert (Hgen : forall G T, wf_ty G T ->
    forall p D Z S, G = p ++ Z :: D -> ~ In Z p -> wf_ty D S ->
      wf_ty (p ++ D) (ty_subst Z S T)).
  { intros G A H. induction H; intros p D Z S Heq Hnot HS.
    - rewrite Heq in H. simpl in H. apply in_app_iff in H. destruct H as [Hp|Htail].
      + assert (E : Nat.eqb Z X0 = false).
        { apply Nat.eqb_neq. intro HeqZX. subst. apply Hnot. exact Hp. }
        unfold ty_subst. rewrite E. constructor. apply in_or_app. left. exact Hp.
      + simpl in Htail. destruct Htail as [Hz|HD].
        * subst X0. unfold ty_subst. rewrite Nat.eqb_refl.
          apply wf_ty_weaken with (Delta := D); [|exact HS].
          intros Y HY. apply in_or_app. right. exact HY.
        * unfold ty_subst. destruct (Nat.eqb Z X0) eqn:E.
          -- apply wf_ty_weaken with (Delta := D); [|exact HS].
             intros Y HY. apply in_or_app. right. exact HY.
          -- constructor. apply in_or_app. right. exact HD.
    - simpl. constructor.
      + apply IHwf_ty1 with (p := p) (D := D) (Z := Z) (S := S); assumption.
      + apply IHwf_ty2 with (p := p) (D := D) (Z := Z) (S := S); assumption.
    - simpl. eapply WF_All with (L := L ++ p ++ Z :: D ++ fv_ty S).
      intros Y HY.
      assert (HYL : ~ In Y L).
      { intro Hin. apply HY. apply in_or_app. left. exact Hin. }
      assert (HYp : ~ In Y p).
      { intro Hin. apply HY. apply in_or_app. right. apply in_or_app. left. exact Hin. }
      assert (HYZ : Y <> Z).
      { intro HeqYZ. subst Y. apply HY. apply in_or_app. right. apply in_or_app. right.
        simpl. left. reflexivity. }
      pose proof (H Y HYL) as Hbody.
      assert (Heq' : Y :: Delta0 = (Y :: p) ++ Z :: D).
      { rewrite Heq. reflexivity. }
      specialize (H0 Y HYL (Y :: p) D Z S Heq' ltac:(simpl; tauto) HS) as Hbody'.
      pose proof (ty_subst_open_fresh Z S Y 0 T0
        (wf_ty_locally_closed D S HS) ltac:(congruence)) as Hcomm.
      unfold open_ty in Hbody'. rewrite Hcomm in Hbody'. exact Hbody'. }
  eapply Hgen; [exact Hwf|reflexivity|exact Hfresh|exact HU].
Qed.

Lemma ty_subst_open_same_fresh : forall X U k T,
  locally_closed_ty U -> ~ In X (fv_ty T) ->
  ty_subst X U (open_ty_rec k (Ty_FVar X) T) = open_ty_rec k U T.
Proof.
  intros X U k T. revert k. induction T; intros k HU Hfresh; simpl in *.
  - destruct (Nat.eqb k n); simpl.
    + unfold ty_subst. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - assert (Hneq : Nat.eqb X a = false).
    { apply Nat.eqb_neq. intro E; subst. apply Hfresh. simpl. auto. }
    rewrite Hneq. reflexivity.
  - assert (H1 : ~ In X (fv_ty T1)) by
      (intro H; apply Hfresh; apply in_or_app; left; exact H).
    assert (H2 : ~ In X (fv_ty T2)) by
      (intro H; apply Hfresh; apply in_or_app; right; exact H).
    rewrite (IHT1 k HU H1), (IHT2 k HU H2). reflexivity.
  - assert (Hbody : ~ In X (fv_ty T)) by exact Hfresh.
    rewrite (IHT (S k) HU Hbody). reflexivity.
Qed.

Lemma wf_ty_open : forall Delta T U,
  wf_ty Delta (Ty_All T) -> wf_ty Delta U ->
  wf_ty Delta (open_ty T U).
Proof.
  intros Delta T U HAll HU. inversion HAll as [| |L D B Hall]; subst.
  set (X := fresh (L ++ Delta ++ fv_ty T)).
  assert (HX : ~ In X L).
  { unfold X. intro Hin. apply (fresh_notin (L ++ Delta ++ fv_ty T)).
    apply in_or_app. left. exact Hin. }
  pose proof (Hall X HX) as Hbody.
  assert (Hfresh : ~ In X []) by (simpl; tauto).
  pose proof (wf_ty_subst_prefix [] Delta X
    (open_ty T (Ty_FVar X)) U Hfresh Hbody HU) as Hsub.
  unfold open_ty in Hsub.
  rewrite ty_subst_open_same_fresh in Hsub.
  - exact Hsub.
  - apply wf_ty_locally_closed with (Delta := Delta). exact HU.
  - unfold X. intro Hin. apply (fresh_notin (L ++ Delta ++ fv_ty T)).
    apply in_or_app. right. apply in_or_app. right. exact Hin.
Qed.

Lemma has_type_wf_result : forall Delta Gamma t T,
  has_type Delta Gamma t T -> wf_ty Delta T.
Proof.
  intros Delta Gamma t T Hty. induction Hty.
  - assumption.
  - apply WF_Arrow; [assumption|]. apply H1 with (x := fresh L).
    apply fresh_notin.
  - inversion IHHty1; assumption.
  - eapply WF_All with (L := L). intros X HX. apply H0; assumption.
  - eapply wf_ty_open; eauto.
  - assumption.
Qed.

Lemma has_type_locally_closed : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T Hty. induction Hty.
  - constructor.
  - apply lc_tm_abs.
    + apply wf_ty_locally_closed with (Delta := Delta). assumption.
    + apply lc_tm_at_open_tm_inv with (x := fresh L).
      apply H1. apply fresh_notin.
  - constructor; assumption.
  - apply lc_tm_tabs. eapply lc_tm_at_open_ty_inv with (X := fresh L).
    apply H0. apply fresh_notin.
  - apply lc_tm_tapp; [assumption|apply wf_ty_locally_closed with (Delta := Delta); assumption].
  - constructor; assumption.
Qed.

Lemma instantiate_ty_lc_at : forall theta T K,
  lc_ty_at K T ->
  (forall X, lc_ty_at K (theta X)) ->
  lc_ty_at K (instantiate_ty theta T).
Proof.
  intros theta T K Hlc. revert theta.
  induction Hlc; intros theta Htheta; simpl.
  - apply lc_ty_bvar. assumption.
  - apply Htheta.
  - apply lc_ty_arrow; [apply IHHlc1|apply IHHlc2]; assumption.
  - apply lc_ty_all. apply IHHlc.
    intros X. eapply lc_ty_at_monotone; [apply Htheta|lia].
Qed.

Lemma instantiate_lc_at : forall theta gamma t K k,
  lc_tm_at K k t ->
  (forall X, lc_ty_at K (theta X)) ->
  term_substitution_closed gamma ->
  lc_tm_at K k (instantiate theta gamma t).
Proof.
  intros theta gamma t K k Hlc. revert theta gamma.
  induction Hlc; intros theta gamma Htheta Hgamma; simpl.
  - apply lc_tm_bvar. assumption.
  - apply lc_tm_at_monotone with (K := 0) (k := 0); try lia.
    apply Hgamma.
  - apply lc_tm_abs.
    + eapply instantiate_ty_lc_at; eauto.
    + apply IHHlc; assumption.
  - apply lc_tm_app; [apply IHHlc1|apply IHHlc2]; assumption.
  - apply lc_tm_tabs. apply IHHlc.
    + intros X. eapply lc_ty_at_monotone; [apply Htheta|lia].
    + intros x. eapply lc_tm_at_monotone; [apply Hgamma|lia|lia].
  - apply lc_tm_tapp.
    + apply IHHlc; assumption.
    + eapply instantiate_ty_lc_at; eauto.
  - apply lc_tm_choice; [apply IHHlc1|apply IHHlc2]; assumption.
Qed.

Lemma instantiate_ty_open_rec_fresh : forall theta X U T k,
  type_substitution_closed theta ->
  ~ In X (fv_ty T) ->
  instantiate_ty (type_subst_update theta X U)
    (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k U (instantiate_ty theta T).
Proof.
  intros theta X U T. induction T; intros k Htheta Hfresh; simpl in *.
  - destruct (Nat.eqb k n); simpl.
    + unfold type_subst_update. simpl. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - assert (Hneq : X <> a) by (intro Heq; subst; apply Hfresh; simpl; auto).
    unfold type_subst_update. simpl. destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E. contradiction.
    + rewrite open_ty_rec_lc_at; [reflexivity|].
      eapply lc_ty_at_monotone; [apply Htheta|lia].
  - assert (H1 : ~ In X (fv_ty T1)) by
      (intro H; apply Hfresh; apply in_or_app; left; exact H).
    assert (H2 : ~ In X (fv_ty T2)) by
      (intro H; apply Hfresh; apply in_or_app; right; exact H).
    rewrite IHT1 by assumption. rewrite IHT2 by assumption. reflexivity.
  - rewrite IHT. reflexivity. exact Htheta. exact Hfresh.
Qed.

Lemma instantiate_open_tm_ty_rec_fresh : forall theta gamma X U t k,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  ~ In X (ftv_tm t) ->
  instantiate (type_subst_update theta X U) gamma
    (open_tm_ty_rec k (Ty_FVar X) t) =
  open_tm_ty_rec k U (instantiate theta gamma t).
Proof.
  intros theta gamma X U t. induction t; intros k Htheta Hgamma Hfresh; simpl in *.
  - reflexivity.
  - rewrite (open_tm_ty_rec_lc_at (gamma a) k 0 U); [reflexivity|].
    eapply lc_tm_at_monotone; [apply Hgamma|lia|lia].
  - assert (Hty : ~ In X (fv_ty t)) by
      (intro H; apply Hfresh; apply in_or_app; left; exact H).
    assert (Htm : ~ In X (ftv_tm t0)) by
      (intro H; apply Hfresh; apply in_or_app; right; exact H).
    rewrite instantiate_ty_open_rec_fresh by eauto.
    rewrite (IHt k Htheta Hgamma Htm). reflexivity.
  - assert (H1 : ~ In X (ftv_tm t1)) by
      (intro H; apply Hfresh; apply in_or_app; left; exact H).
    assert (H2 : ~ In X (ftv_tm t2)) by
      (intro H; apply Hfresh; apply in_or_app; right; exact H).
    rewrite IHt1 by eauto. rewrite IHt2 by eauto. reflexivity.
  - rewrite (IHt (S k) Htheta Hgamma Hfresh). reflexivity.
  - assert (Htm : ~ In X (ftv_tm t)) by
      (intro H; apply Hfresh; apply in_or_app; left; exact H).
    assert (Hty : ~ In X (fv_ty t0)) by
      (intro H; apply Hfresh; apply in_or_app; right; exact H).
    rewrite IHt by eauto.
    rewrite instantiate_ty_open_rec_fresh by eauto. reflexivity.
  - assert (H1 : ~ In X (ftv_tm t1)) by
      (intro H; apply Hfresh; apply in_or_app; left; exact H).
    assert (H2 : ~ In X (ftv_tm t2)) by
      (intro H; apply Hfresh; apply in_or_app; right; exact H).
    rewrite IHt1 by eauto. rewrite IHt2 by eauto. reflexivity.
Qed.

Lemma instantiate_open_tm_rec : forall theta gamma x s t k,
  term_substitution_closed gamma -> locally_closed_tm s ->
  ~ In x (fv_tm t) ->
  instantiate theta (term_subst_update gamma x s)
    (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k s (instantiate theta gamma t).
Proof.
  intros theta gamma x s t. induction t; intros k Hgamma Hs Hfresh; simpl in *.
  - destruct (Nat.eqb k n); simpl.
    + unfold term_subst_update. simpl. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E. subst a. exfalso. apply Hfresh. simpl. auto.
    + unfold term_subst_update. rewrite E.
      rewrite (open_tm_rec_lc_at (gamma a) 0 k s); [reflexivity|].
      eapply lc_tm_at_monotone; [apply Hgamma|lia|lia].
  - rewrite (IHt (S k) Hgamma Hs Hfresh). reflexivity.
  - assert (H1 : ~ In x (fv_tm t1)) by
      (intro H; apply Hfresh; apply in_or_app; left; exact H).
    assert (H2 : ~ In x (fv_tm t2)) by
      (intro H; apply Hfresh; apply in_or_app; right; exact H).
    rewrite IHt1 by assumption. rewrite IHt2 by assumption. reflexivity.
  - f_equal. apply IHt; assumption.
  - f_equal. apply IHt; assumption.
  - assert (H1 : ~ In x (fv_tm t1)) by
      (intro H; apply Hfresh; apply in_or_app; left; exact H).
    assert (H2 : ~ In x (fv_tm t2)) by
      (intro H; apply Hfresh; apply in_or_app; right; exact H).
    rewrite IHt1 by assumption. rewrite IHt2 by assumption. reflexivity.
Qed.

Lemma instantiate_ty_sem_subst_left_at : forall theta T d,
  lc_ty_at d T ->
  instantiate_ty (fun X => sem_left_type (theta X)) T =
    sem_subst_rec sem_left_type theta [] d T.
Proof.
  intros theta T. induction T; intros d Hlc; simpl in *.
  - destruct (n <? d) eqn:E; [reflexivity|].
    apply Nat.ltb_ge in E. inversion Hlc. lia.
  - reflexivity.
  - inversion Hlc; subst. rewrite (IHT1 d H2), (IHT2 d H3). reflexivity.
  - inversion Hlc; subst. rewrite (IHT (S d) H1). reflexivity.
Qed.

Lemma instantiate_ty_sem_subst_left : forall theta T,
  locally_closed_ty T ->
  instantiate_ty (fun X => sem_left_type (theta X)) T =
    sem_subst_rec sem_left_type theta [] 0 T.
Proof. intros; eapply instantiate_ty_sem_subst_left_at; eauto. Qed.

Lemma instantiate_ty_sem_subst_right_at : forall theta T d,
  lc_ty_at d T ->
  instantiate_ty (fun X => sem_right_type (theta X)) T =
    sem_subst_rec sem_right_type theta [] d T.
Proof.
  intros theta T. induction T; intros d Hlc; simpl in *.
  - destruct (n <? d) eqn:E; [reflexivity|].
    apply Nat.ltb_ge in E. inversion Hlc. lia.
  - reflexivity.
  - inversion Hlc; subst. rewrite (IHT1 d H2), (IHT2 d H3). reflexivity.
  - inversion Hlc; subst. rewrite (IHT (S d) H1). reflexivity.
Qed.

Lemma instantiate_ty_sem_subst_right : forall theta T,
  locally_closed_ty T ->
  instantiate_ty (fun X => sem_right_type (theta X)) T =
    sem_subst_rec sem_right_type theta [] 0 T.
Proof. intros; eapply instantiate_ty_sem_subst_right_at; eauto. Qed.

Lemma sem_subst_update_fresh : forall proj theta X R rho d T,
  ~ In X (fv_ty T) ->
  sem_subst_rec proj (sem_update theta X R) rho d T =
  sem_subst_rec proj theta rho d T.
Proof.
  intros proj theta X R rho d T. revert d. induction T; intros d Hfresh; simpl in *.
  - reflexivity.
  - assert (Hneq : X <> a) by (intro E; subst; apply Hfresh; simpl; auto).
    unfold sem_update. assert (E : Nat.eqb X a = false) by
      (apply Nat.eqb_neq; exact Hneq). rewrite E. reflexivity.
  - assert (H1 : ~ In X (fv_ty T1)) by
      (intro H; apply Hfresh; apply in_or_app; left; exact H).
    assert (H2 : ~ In X (fv_ty T2)) by
      (intro H; apply Hfresh; apply in_or_app; right; exact H).
    rewrite IHT1 by exact H1. rewrite IHT2 by exact H2. reflexivity.
  - f_equal. apply IHT. exact Hfresh.
Qed.

Definition sem_left_sub (theta : atom -> semantic_type) : type_substitution :=
  fun X => sem_left_type (theta X).
Definition sem_right_sub (theta : atom -> semantic_type) : type_substitution :=
  fun X => sem_right_type (theta X).

Definition related_context (theta : atom -> semantic_type) (Gamma : context)
    (g1 g2 : term_substitution) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    sem_term_rel (interpret_type theta [] T) (g1 x) (g2 x).

Fixpoint context_fv (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (_, T) :: Gamma' => fv_ty T ++ context_fv Gamma'
  end.

Lemma lookup_type_fv_context : forall Gamma x T A,
  lookup_context x Gamma = Some T -> In A (fv_ty T) -> In A (context_fv Gamma).
Proof.
  induction Gamma as [|[y S] Gamma IH]; intros x T A Hlook Hfv; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + inversion Hlook; subst. apply in_or_app. left. exact Hfv.
    + apply in_or_app. right. eapply IH; eassumption.
Qed.

Lemma sem_term_rel_prefix : forall R t t' u u',
  t -->* t' -> u -->* u' -> sem_term_rel R t' u' -> sem_term_rel R t u.
Proof.
  intros R t t' u u' Ht Hu [v [w [Ht' [Hu' [Hv [Hw Hrel]]]]]].
  exists v, w. repeat split; try assumption; eapply multi_trans; eauto.
Qed.

Lemma sem_interpret_update_fresh : forall theta X R rho T,
  ~ In X (fv_ty T) ->
  sem_equiv (interpret_type (sem_update theta X R) rho T)
    (interpret_type theta rho T).
Proof.
  intros theta X R rho T. revert rho. induction T; intros rho Hfresh; simpl in *.
  - apply sem_equiv_refl.
  - assert (Hneq : X <> a) by (intro E; subst; apply Hfresh; simpl; auto).
    unfold sem_update. assert (E : Nat.eqb X a = false).
    { apply Nat.eqb_neq. exact Hneq. }
    rewrite E. apply sem_equiv_refl.
  - assert (H1 : ~ In X (fv_ty T1)) by
      (intro H; apply Hfresh; apply in_or_app; left; exact H).
    assert (H2 : ~ In X (fv_ty T2)) by
      (intro H; apply Hfresh; apply in_or_app; right; exact H).
    apply sem_arrow_ext; [apply IHT1|apply IHT2]; assumption.
  - pose proof (sem_subst_update_fresh sem_left_type theta X R rho 1 T Hfresh) as HL.
    pose proof (sem_subst_update_fresh sem_right_type theta X R rho 1 T Hfresh) as HR.
    simpl. rewrite HL, HR. apply sem_all_ext. intros U V HU HV P.
    apply IHT. exact Hfresh.
Qed.

Definition semantic_environment_closed (theta : atom -> semantic_type) : Prop :=
  forall X, locally_closed_ty (sem_left_type (theta X)) /\
            locally_closed_ty (sem_right_type (theta X)).

Lemma fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall theta g1 g2,
    semantic_environment_closed theta ->
    term_substitution_closed g1 -> term_substitution_closed g2 ->
    related_context theta Gamma g1 g2 ->
    sem_term_rel (interpret_type theta [] T)
      (instantiate (sem_left_sub theta) g1 t)
      (instantiate (sem_right_sub theta) g2 t).
Proof.
  intros Delta Gamma t T Htyping. induction Htyping;
    intros theta g1 g2 Htheta Hg1 Hg2 Hctx.
  - simpl. apply Hctx with (T := T); assumption.
  - assert (Htylc : locally_closed_ty T1) by
      (eapply wf_ty_locally_closed; eassumption).
    assert (HabsLC : locally_closed_tm (tm_abs T1 t2)).
    { eapply has_type_locally_closed. econstructor; eauto. }
    assert (HtermL : locally_closed_tm (instantiate (sem_left_sub theta) g1
      (tm_abs T1 t2))).
    { eapply instantiate_lc_at; [exact HabsLC| |exact Hg1].
      intros X. destruct (Htheta X); assumption. }
    assert (HtermR : locally_closed_tm (instantiate (sem_right_sub theta) g2
      (tm_abs T1 t2))).
    { eapply instantiate_lc_at; [exact HabsLC| |exact Hg2].
      intros X. destruct (Htheta X); assumption. }
    simpl. exists (instantiate (sem_left_sub theta) g1 (tm_abs T1 t2)),
      (instantiate (sem_right_sub theta) g2 (tm_abs T1 t2)).
    repeat split; try constructor; try assumption.
    simpl. exists (sem_left_type (interpret_type theta [] T1)),
      (instantiate (sem_left_sub theta) g1 t2),
      (sem_right_type (interpret_type theta [] T1)),
      (instantiate (sem_right_sub theta) g2 t2).
    repeat split; try reflexivity; try assumption.
    unfold sem_left_sub, sem_right_sub.
    rewrite (instantiate_ty_sem_subst_left theta T1 Htylc).
    rewrite (sem_subst_closed_left theta [] 0 T1 Htylc).
    reflexivity.
    unfold sem_right_sub.
    rewrite (instantiate_ty_sem_subst_right theta T1 Htylc).
    rewrite (sem_subst_closed_right theta [] 0 T1 Htylc).
    reflexivity.
    intros a b Hab.
    destruct Hab as [va [vb [Ha [Hb [Hva [Hvb Hrel]]]]]].
    set (x := fresh (L ++ fv_tm t2)).
    assert (HxL : ~ In x L).
    { unfold x. intro Hin. apply (fresh_notin (L ++ fv_tm t2)).
      apply in_or_app. left. exact Hin. }
    assert (HxT : ~ In x (fv_tm t2)).
    { unfold x. intro Hin. apply (fresh_notin (L ++ fv_tm t2)).
      apply in_or_app. right. exact Hin. }
    assert (Harg : sem_term_rel (interpret_type theta [] T1) va vb).
    { exists va, vb. repeat split; try assumption; constructor. }
    assert (Hctx' : related_context theta (update Gamma x T1)
      (term_subst_update g1 x va) (term_subst_update g2 x vb)).
    { intros y S Hlook. destruct (Nat.eq_dec y x) as [->|Hneq].
      - rewrite lookup_context_update_eq in Hlook. inversion Hlook; subst S.
        unfold term_subst_update. rewrite Nat.eqb_refl. exact Harg.
      - rewrite lookup_context_update_neq in Hlook by (intro E; apply Hneq; symmetry; exact E).
        specialize (Hctx y S Hlook).
        unfold term_subst_update. assert (E : Nat.eqb x y = false)
          by (apply Nat.eqb_neq; intro E; apply Hneq; symmetry; exact E).
        rewrite E. exact Hctx. }
    pose proof (H1 x HxL theta
      (term_subst_update g1 x va) (term_subst_update g2 x vb)
      Htheta
      (term_subst_update_closed g1 x va Hg1 (value_regular _ Hva))
      (term_subst_update_closed g2 x vb Hg2 (value_regular _ Hvb)) Hctx') as Hbody.
    assert (HopenL : instantiate (sem_left_sub theta)
        (term_subst_update g1 x va) (open_tm t2 (tm_fvar x)) =
      open_tm (instantiate (sem_left_sub theta) g1 t2) va).
    { unfold open_tm. simpl.
      apply (instantiate_open_tm_rec (sem_left_sub theta) g1 x va t2 0).
      - exact Hg1.
      - exact (value_regular _ Hva).
      - exact HxT. }
    assert (HopenR : instantiate (sem_right_sub theta)
        (term_subst_update g2 x vb) (open_tm t2 (tm_fvar x)) =
      open_tm (instantiate (sem_right_sub theta) g2 t2) vb).
    { unfold open_tm. simpl.
      apply (instantiate_open_tm_rec (sem_right_sub theta) g2 x vb t2 0).
      - exact Hg2.
      - exact (value_regular _ Hvb).
      - exact HxT. }
    rewrite HopenL, HopenR in Hbody.
    eapply sem_term_rel_prefix with
      (t' := open_tm (instantiate (sem_left_sub theta) g1 t2) va)
      (u' := open_tm (instantiate (sem_right_sub theta) g2 t2) vb).
    + eapply multi_trans.
      * apply multi_app_right; [constructor; exact HtermL|exact Ha].
      * eapply multi_step; [apply ST_AppAbs; [exact HtermL|exact Hva]|constructor].
    + eapply multi_trans.
      * apply multi_app_right; [constructor; exact HtermR|exact Hb].
      * eapply multi_step; [apply ST_AppAbs; [exact HtermR|exact Hvb]|constructor].
    + exact Hbody.
  - simpl. destruct (IHHtyping1 theta g1 g2 Htheta Hg1 Hg2 Hctx)
      as [f [g [Hf [Hg [Hfv [Hgv Hfg]]]]]].
    pose proof (IHHtyping2 theta g1 g2 Htheta Hg1 Hg2 Hctx) as Harg.
    simpl in Hfg. destruct Hfg as [S1 [b1 [S2 [b2 [Hfeq [Hgeq [Hflc [Hglc Hfun]]]]]]]].
    subst f. subst g.
    specialize (Hfun (instantiate (sem_left_sub theta) g1 t2)
      (instantiate (sem_right_sub theta) g2 t2) Harg) as Hres.
    pose proof (has_type_locally_closed _ _ _ _ Htyping2) as Harglc.
    assert (HargL : locally_closed_tm (instantiate (sem_left_sub theta) g1 t2)).
    { eapply instantiate_lc_at; [exact Harglc| |exact Hg1].
      intros X. destruct (Htheta X); assumption. }
    assert (HargR : locally_closed_tm (instantiate (sem_right_sub theta) g2 t2)).
    { eapply instantiate_lc_at; [exact Harglc| |exact Hg2].
      intros X. destruct (Htheta X); assumption. }
    eapply sem_term_rel_prefix with
      (t' := tm_app (tm_abs S1 b1) (instantiate (sem_left_sub theta) g1 t2))
      (u' := tm_app (tm_abs S2 b2) (instantiate (sem_right_sub theta) g2 t2)).
    + apply multi_app_left; [exact Hf|exact HargL].
    + apply multi_app_left; [exact Hg|exact HargR].
    + exact Hres.
  - simpl.
    set (x := fresh (L ++ ftv_tm t ++ fv_ty T ++ context_fv Gamma)).
    assert (HxL : ~ In x L).
    { unfold x. intro Hin. apply (fresh_notin (L ++ ftv_tm t ++ fv_ty T ++ context_fv Gamma)).
      apply in_or_app. left. exact Hin. }
    assert (HxT : ~ In x (ftv_tm t)).
    { unfold x. intro Hin. apply (fresh_notin (L ++ ftv_tm t ++ fv_ty T ++ context_fv Gamma)).
      apply in_or_app. right. apply in_or_app. left. exact Hin. }
    assert (HxTy : ~ In x (fv_ty T)).
    { unfold x. intro Hin. apply (fresh_notin (L ++ ftv_tm t ++ fv_ty T ++ context_fv Gamma)).
      apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hin. }
    assert (HxGamma : ~ In x (context_fv Gamma)).
    { unfold x. intro Hin. apply (fresh_notin (L ++ ftv_tm t ++ fv_ty T ++ context_fv Gamma)).
      apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact Hin. }
    pose proof (H x HxL) as HtypedX.
    pose proof (has_type_wf_result _ _ _ _ HtypedX) as HwfOpened.
    pose proof (wf_ty_locally_closed _ _ HwfOpened) as Hopenedty.
    pose proof (lc_ty_at_open_inv T 0 x Hopenedty) as HTlc.
    pose proof (has_type_locally_closed _ _ _ _ HtypedX) as Hopenedtm.
    pose proof (lc_tm_at_open_ty_inv t 0 0 x Hopenedtm) as Htclosed.
    assert (HtabsL : locally_closed_tm (instantiate (sem_left_sub theta) g1 (tm_tabs t))).
    { eapply instantiate_lc_at; [apply lc_tm_tabs; exact Htclosed| |exact Hg1].
      intros Y. destruct (Htheta Y); assumption. }
    assert (HtabsR : locally_closed_tm (instantiate (sem_right_sub theta) g2 (tm_tabs t))).
    { eapply instantiate_lc_at; [apply lc_tm_tabs; exact Htclosed| |exact Hg2].
      intros Y. destruct (Htheta Y); assumption. }
    unfold sem_term_rel. simpl.
    exists (instantiate (sem_left_sub theta) g1 (tm_tabs t)),
      (instantiate (sem_right_sub theta) g2 (tm_tabs t)).
    repeat split; try constructor; try assumption.
    simpl. exists (instantiate (sem_left_sub theta) g1 t),
      (instantiate (sem_right_sub theta) g2 t).
    repeat split; try reflexivity; try assumption.
    intros U V P HU HV.
    set (R := sem_base U V P).
    set (theta' := sem_update theta x R).
    assert (Htheta' : semantic_environment_closed theta').
    { intros Y. unfold theta'. unfold sem_update.
      destruct (Nat.eqb x Y) eqn:E.
      - apply Nat.eqb_eq in E. subst. simpl. auto.
      - apply Htheta. }
    assert (Hctx' : related_context theta' Gamma g1 g2).
    { intros y S Hlook. specialize (Hctx y S Hlook).
      apply sem_term_rel_equiv with (A := interpret_type theta [] S)
        (B := interpret_type theta' [] S).
      - apply sem_equiv_sym. unfold theta'.
        apply sem_interpret_update_fresh.
        intro Hin. apply HxGamma.
        eapply lookup_type_fv_context; eassumption.
      - exact Hctx. }
    pose proof (H0 x HxL theta' g1 g2 Htheta' Hg1 Hg2 Hctx') as Hbody'.
    assert (HopenL : instantiate (sem_left_sub theta') g1 (open_tm_ty t (Ty_FVar x)) =
      open_tm_ty (instantiate (sem_left_sub theta) g1 t) U).
    { assert (Hsub : sem_left_sub theta' = type_subst_update (sem_left_sub theta) x U).
      { apply functional_extensionality. intro Y. unfold sem_left_sub, theta', sem_update, R, sem_base.
        unfold type_subst_update. destruct (Nat.eqb x Y); cbn; reflexivity. }
      rewrite Hsub. unfold open_tm_ty.
      eapply instantiate_open_tm_ty_rec_fresh.
      - intros Y. destruct (Htheta Y); assumption.
      - exact Hg1.
      - exact HxT. }
    assert (HopenR : instantiate (sem_right_sub theta') g2 (open_tm_ty t (Ty_FVar x)) =
      open_tm_ty (instantiate (sem_right_sub theta) g2 t) V).
    { assert (Hsub : sem_right_sub theta' = type_subst_update (sem_right_sub theta) x V).
      { apply functional_extensionality. intro Y. unfold sem_right_sub, theta', sem_update, R, sem_base.
        unfold type_subst_update. destruct (Nat.eqb x Y); cbn; reflexivity. }
      rewrite Hsub. unfold open_tm_ty.
      eapply instantiate_open_tm_ty_rec_fresh.
      - intros Y. destruct (Htheta Y); assumption.
      - exact Hg2.
      - exact HxT. }
    rewrite HopenL, HopenR in Hbody'.
    assert (HtypeEq : sem_equiv
      (interpret_type theta' [] (open_ty T (Ty_FVar x)))
      (interpret_type theta [R] T)).
    { unfold theta'. apply sem_interpret_open; try assumption; simpl; lia. }
    eapply sem_term_rel_prefix with
      (t' := open_tm_ty (instantiate (sem_left_sub theta) g1 t) U)
      (u' := open_tm_ty (instantiate (sem_right_sub theta) g2 t) V).
    + eapply multi_step; [apply ST_TAppTabs; [exact HtabsL|exact HU]|constructor].
    + eapply multi_step; [apply ST_TAppTabs; [exact HtabsR|exact HV]|constructor].
    + apply (proj1 (sem_term_rel_equiv _ _ _ _ HtypeEq)). exact Hbody'.
  - simpl.
    destruct (IHHtyping theta g1 g2 Htheta Hg1 Hg2 Hctx)
      as [f [g [Hf [Hg [Hfv [Hgv Hrel]]]]]].
    simpl in Hrel. destruct Hrel as [bf [bg [-> [-> [Hflc [Hglc Hall]]]]]].
    assert (HU : locally_closed_ty U) by (eapply wf_ty_locally_closed; eassumption).
    set (RI := interpret_type theta [] U).
    assert (Eleft : instantiate_ty (sem_left_sub theta) U = sem_left_type RI).
    { unfold sem_left_sub. rewrite instantiate_ty_sem_subst_left; [|exact HU].
      unfold RI. apply sem_subst_closed_left. exact HU. }
    assert (Eright : instantiate_ty (sem_right_sub theta) U = sem_right_type RI).
    { unfold sem_right_sub. rewrite instantiate_ty_sem_subst_right; [|exact HU].
      unfold RI. apply sem_subst_closed_right. exact HU. }
    assert (HleftU : locally_closed_ty (sem_left_type RI)).
    { rewrite <- Eleft. eapply instantiate_ty_lc_at; [exact HU|].
      intros X. destruct (Htheta X); assumption. }
    assert (HrightU : locally_closed_ty (sem_right_type RI)).
    { rewrite <- Eright. eapply instantiate_ty_lc_at; [exact HU|].
      intros X. destruct (Htheta X); assumption. }
    specialize (Hall (sem_left_type RI) (sem_right_type RI)
      (sem_value_rel RI) HleftU HrightU) as Hinst.
    pose proof (has_type_wf_result _ _ _ _ Htyping) as HwfAll.
    pose proof (wf_ty_locally_closed _ _ HwfAll) as HlcAll.
    inversion HlcAll as [| | |K B Hbodylc]; subst.
    assert (HtypeEq : sem_equiv (interpret_type theta [] (open_ty T U))
      (interpret_type theta [RI] T)).
    { unfold open_ty. simpl. apply sem_interpret_subst; try assumption; simpl; lia. }
    assert (HRIrel : sem_equiv
      (sem_base (sem_left_type RI) (sem_right_type RI) (sem_value_rel RI)) RI).
    { destruct RI. apply sem_equiv_refl. }
    assert (HenvRI : sem_env_equiv
      [sem_base (sem_left_type RI) (sem_right_type RI) (sem_value_rel RI)] [RI]).
    { split; [reflexivity|]. intros n Hn. destruct n; [exact HRIrel|simpl in Hn; lia]. }
    assert (HbodyEq : sem_equiv
      (interpret_type theta [sem_base (sem_left_type RI) (sem_right_type RI)
        (sem_value_rel RI)] T) (interpret_type theta [RI] T)).
    { eapply sem_interp_env_congr; [exact HenvRI|]. simpl. exact Hbodylc. }
    pose proof (proj1 (sem_term_rel_equiv _ _ _ _ HbodyEq) Hinst) as Hinst'.
    eapply sem_term_rel_prefix with
      (t' := tm_tapp (tm_tabs bf) (sem_left_type RI))
      (u' := tm_tapp (tm_tabs bg) (sem_right_type RI)).
    + replace (instantiate_ty (sem_left_sub theta) U) with (sem_left_type RI)
        by (symmetry; exact Eleft).
      apply multi_tapp; [exact Hf|exact HleftU].
    + replace (instantiate_ty (sem_right_sub theta) U) with (sem_right_type RI)
        by (symmetry; exact Eright).
      apply multi_tapp; [exact Hg|exact HrightU].
    + apply (proj2 (sem_term_rel_equiv _ _ _ _ HtypeEq)). exact Hinst'.
  - simpl.
    pose proof (IHHtyping1 theta g1 g2 Htheta Hg1 Hg2 Hctx) as Hbranch.
    pose proof (has_type_locally_closed _ _ _ _ Htyping1) as Hlc_t1.
    pose proof (has_type_locally_closed _ _ _ _ Htyping2) as Hlc_t2.
    assert (Hlc1L : locally_closed_tm (instantiate (sem_left_sub theta) g1 t1)).
    { eapply instantiate_lc_at; [exact Hlc_t1| |exact Hg1].
      intros X. destruct (Htheta X); assumption. }
    assert (Hlc2L : locally_closed_tm (instantiate (sem_left_sub theta) g1 t2)).
    { eapply instantiate_lc_at; [exact Hlc_t2| |exact Hg1].
      intros X. destruct (Htheta X); assumption. }
    assert (Hlc1R : locally_closed_tm (instantiate (sem_right_sub theta) g2 t1)).
    { eapply instantiate_lc_at; [exact Hlc_t1| |exact Hg2].
      intros X. destruct (Htheta X); assumption. }
    assert (Hlc2R : locally_closed_tm (instantiate (sem_right_sub theta) g2 t2)).
    { eapply instantiate_lc_at; [exact Hlc_t2| |exact Hg2].
      intros X. destruct (Htheta X); assumption. }
    eapply sem_term_rel_prefix with
      (t' := instantiate (sem_left_sub theta) g1 t1)
      (u' := instantiate (sem_right_sub theta) g2 t1).
    + eapply multi_step; [apply ST_ChoiceLeft; assumption|constructor].
    + eapply multi_step; [apply ST_ChoiceLeft; assumption|constructor].
    + exact Hbranch.
Qed.

Lemma identity_from_related_value : forall theta f U v,
  related_value theta []
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) f ->
  wf_ty [] U -> value v -> has_type [] empty v U ->
  tm_app (tm_tapp f U) v -->* v.
Proof.
  intros theta f U v Hrel Hwf Hv Hty.
  destruct Hrel as [body [-> [Hlc Hall]]].
  set (P := fun w : tm => w = v).
  assert (HP : related_value theta (P :: []) (Ty_BVar 0) v).
  { simpl. reflexivity. }
  specialize (Hall U P (wf_ty_locally_closed [] U Hwf)) as Hinst.
  destruct Hinst as [g [Htap [Hgv Hgre]]].
  simpl in Hgre.
  destruct Hgre as [S [b [Hg [Hgl Hfun]]]].
  subst g.
  specialize (Hfun v HP) as Happ.
  destruct Happ as [z [Happ [Hz Hrz]]].
  simpl in Hrz. unfold P in Hrz. subst z.
  eapply multi_trans.
  - apply multi_app_left.
    + exact Htap.
    + apply value_regular. exact Hv.
  - exact Happ.
Qed.

Lemma identity_from_reducible : forall theta t U v,
  reducible theta []
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) t ->
  wf_ty [] U -> value v -> has_type [] empty v U ->
  tm_app (tm_tapp t U) v -->* v.
Proof.
  intros theta t U v [f [Htf [Hfv Hfr]]] Hwf Hv Hty.
  eapply multi_trans.
  - apply multi_app_left.
    + apply multi_tapp; [exact Htf|apply wf_ty_locally_closed with (Delta := []); exact Hwf].
    + apply value_regular; exact Hv.
  - eapply identity_from_related_value; eauto.
Qed.

Definition theta_identity : atom -> semantic_type :=
  fun X => sem_base (Ty_FVar X) (Ty_FVar X) (fun a b => a = b).
Definition gamma_identity : term_substitution := fun x => tm_fvar x.

Lemma instantiate_ty_identity : forall T,
  instantiate_ty (fun X => Ty_FVar X) T = T.
Proof.
  induction T; simpl; try rewrite ?IHT1, ?IHT2, ?IHT; reflexivity.
Qed.

Lemma instantiate_identity : forall t,
  instantiate (fun X => Ty_FVar X) gamma_identity t = t.
Proof.
  induction t; simpl; try rewrite ?instantiate_ty_identity, ?IHt, ?IHt1, ?IHt2;
    unfold gamma_identity; try reflexivity.
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
  set (P := fun a b : tm => a = v /\ b = v).
  set (theta0 := theta_identity).
  assert (Htheta0 : semantic_environment_closed theta0).
  { intros X. unfold theta0, theta_identity, sem_base. simpl. split; constructor. }
  assert (Hgamma0 : term_substitution_closed gamma_identity).
  { intros x. unfold gamma_identity. constructor. }
  assert (Hctx0 : related_context theta0 [] gamma_identity gamma_identity).
  { intros x T Hlook. discriminate. }
  pose proof (@fundamental [] [] t
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) Hty
    theta0 gamma_identity gamma_identity Htheta0 Hgamma0 Hgamma0 Hctx0) as Hrel.
  unfold theta0 in Hrel. unfold theta_identity, sem_left_sub, sem_right_sub in Hrel.
  cbn [sem_base sem_left_type sem_right_type] in Hrel.
  rewrite instantiate_identity in Hrel.
  change (sem_term_rel
    (interpret_type theta_identity []
      (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0)))) t t) in Hrel.
  destruct Hrel as [f [g [Htf [Htg [Hfv [Hgv Hsem]]]]]].
  simpl in Hsem.
  destruct Hsem as [bf [bg [Hfb [Hgb [Hfblc [Hgblc Hall]]]]]].
  subst f. subst g.
  assert (HU : locally_closed_ty U) by (eapply wf_ty_locally_closed; eassumption).
  specialize (Hall U U P HU HU) as Htapp.
  assert (Hvv : sem_term_rel (sem_base U U P) v v).
  { exists v, v. repeat split; try constructor; try assumption. }
  simpl in Htapp.
  destruct Htapp as [a [b [Hta [Htb [Hva [Hvb Hfunrel]]]]]].
  simpl in Hfunrel.
  destruct Hfunrel as [S1 [body1 [S2 [body2 [Haeq [Hbeq [Hal [Hbl Hfun]]]]]]]].
  subst a. subst b.
  specialize (Hfun v v Hvv) as Happ.
  simpl in Happ.
  destruct Happ as [z [w [HappL [HappR [Hz [Hw HP]]]]]].
  unfold P in HP. destruct HP as [Hzv Hwv]. subst z.
  eapply multi_trans.
  - apply multi_app_left.
    + eapply multi_trans.
      * apply multi_tapp; [exact Htf|exact HU].
      * exact Hta.
    + apply value_regular. exact Hv.
  - exact HappL.
Qed.

End SystemFParametricityNondeterminismEasyTask.
