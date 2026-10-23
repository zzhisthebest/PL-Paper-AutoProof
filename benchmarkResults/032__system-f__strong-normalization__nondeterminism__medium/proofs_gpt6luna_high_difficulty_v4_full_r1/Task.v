(** System F CBV strong-normalization benchmark, Easy variant.
    Features: nondeterminism. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFNormalizationNondeterminismEasyTask.

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

Inductive strongly_normalizing : tm -> Prop :=
  | SN_intro : forall t,
      (forall u, t --> u -> strongly_normalizing u) -> strongly_normalizing t.

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

Lemma value_no_step : forall v, value v -> forall t, ~ (v --> t).
Proof. intros v Hv t Hs. destruct Hv; inversion Hs. Qed.

Lemma value_multi_eq : forall v t,
  value v ->
  v -->* t ->
  t = v.
Proof.
  intros v t Hv Hmulti.
  inversion Hmulti; subst.
  - reflexivity.
  - exfalso. eapply value_no_step; eauto.
Qed.

Lemma choice_sn : forall t1 t2,
  strongly_normalizing t1 -> strongly_normalizing t2 ->
  strongly_normalizing (tm_choice t1 t2).
Proof.
  intros t1 t2 H1 H2. constructor. intros u Hstep.
  inversion Hstep; subst; assumption.
Qed.

Inductive neutral : tm -> Prop :=
| neutral_var : forall x, neutral (tm_fvar x)
| neutral_app : forall t u, neutral (tm_app t u)
| neutral_tapp : forall t T, neutral (tm_tapp t T).

Lemma neutral_not_value : forall t, neutral t -> ~ value t.
Proof. intros t H; induction H; intros Hv; inversion Hv; subst; eauto. Qed.

Lemma fvar_no_step : forall x u, ~ tm_fvar x --> u.
Proof. intros x u H; inversion H. Qed.

Lemma step_preserves_lc : forall t u,
  locally_closed_tm t -> t --> u -> locally_closed_tm u.
Proof.
  intros t u Hlc Hstep. revert Hlc.
  induction Hstep; intros Hlc; inversion Hlc; subst;
    try (eapply lc_tm_app; eauto);
    try (eapply lc_tm_tapp; eauto);
    try assumption.
  all: try match goal with
  | Habs : locally_closed_tm (tm_abs _ _) |- locally_closed_tm (open_tm _ _) =>
      unfold locally_closed_tm, open_tm in *;
      match goal with
      | Habs' : lc_tm_at 0 0 (tm_abs _ _) |- _ =>
          inversion Habs'; subst;
          eapply open_tm_preserves_lc_at; eauto using value_regular
      end
  end.
  all: try match goal with
  | Htabs : locally_closed_tm (tm_tabs _) |- locally_closed_tm (open_tm_ty _ _) =>
      unfold locally_closed_tm, locally_closed_ty, open_tm_ty in *;
      match goal with
      | Htabs' : lc_tm_at 0 0 (tm_tabs _) |- _ =>
          inversion Htabs'; subst;
          eapply open_tm_ty_preserves_lc_at; eauto
      end
  end.
  all: unfold locally_closed_tm in *; eauto 8.
Qed.

Definition red_set := tm -> Prop.
Record RC (S : red_set) : Prop := {
  rc_lc : forall t, S t -> locally_closed_tm t;
  rc_sn : forall t, S t -> strongly_normalizing t;
  rc_step : forall t u, S t -> t --> u -> S u;
  rc_choice : forall t1 t2, S t1 -> S t2 -> S (tm_choice t1 t2);
  rc_neutral : forall t, locally_closed_tm t -> neutral t ->
    (forall u, t --> u -> S u) -> S t
}.

Definition sn_set : red_set := fun t => locally_closed_tm t /\ strongly_normalizing t.

Lemma RC_sn : RC sn_set.
Proof.
  constructor.
  - intros t H; exact (proj1 H).
  - intros t H; exact (proj2 H).
  - intros t u [Hlc Hsn] Hstep. split.
    + eapply step_preserves_lc; eauto.
    + inversion Hsn; subst. eapply H; eauto.
  - intros t1 t2 [Hlc1 Hsn1] [Hlc2 Hsn2]. split.
    + constructor; assumption.
    + apply choice_sn; assumption.
  - intros t Hlc Hneutral Hred. split; [exact Hlc|].
    constructor. intros u Hu. exact (proj2 (Hred u Hu)).
Qed.

Lemma sn_app_left : forall t u,
  locally_closed_tm u -> strongly_normalizing (tm_app t u) -> strongly_normalizing t.
Proof.
  intros t u Hu H. remember (tm_app t u) as p eqn:E in H |- *.
  revert t u E Hu. induction H as [p Hnext IH]; intros t u E Hu; inversion E; subst.
  constructor. intros t' Hstep.
  exact (IH (tm_app t' u) (ST_App1 t t' u Hstep Hu) t' u eq_refl Hu).
Qed.

Lemma sn_tapp_left : forall t T,
  locally_closed_ty T -> strongly_normalizing (tm_tapp t T) -> strongly_normalizing t.
Proof.
  intros t T HT H. remember (tm_tapp t T) as p eqn:E in H |- *.
  revert t T E HT. induction H as [p Hnext IH]; intros t T E HT; inversion E; subst.
  constructor. intros t' Hstep.
  exact (IH (tm_tapp t' T) (ST_TApp t t' T Hstep HT) t' T eq_refl HT).
Qed.

Definition arr_set (S1 S2 : red_set) : red_set :=
  fun t => forall u, S1 u -> S2 (tm_app t u).

Definition all_set (F : red_set -> red_set) : red_set :=
  fun t => forall S, RC S -> forall U, locally_closed_ty U ->
    F S (tm_tapp t U).

Lemma fvar_in_RC : forall S x, RC S -> S (tm_fvar x).
Proof.
  intros S x H. eapply (rc_neutral S H (tm_fvar x)).
  - apply lc_tm_fvar.
  - constructor.
  - intros u Hu. inversion Hu.
Qed.

Lemma RC_arr : forall S1 S2,
  RC S1 -> RC S2 -> RC (arr_set S1 S2).
Proof.
  intros S1 S2 H1 H2. constructor.
  - intros t Ht.
    specialize (Ht (tm_fvar 0) (fvar_in_RC S1 0 H1)).
    pose proof (rc_lc S2 H2 (tm_app t (tm_fvar 0)) Ht) as Hlc.
    inversion Hlc; assumption.
  - intros t Ht.
    specialize (Ht (tm_fvar 0) (fvar_in_RC S1 0 H1)).
    apply (sn_app_left t (tm_fvar 0)); [apply lc_tm_fvar|].
    eapply rc_sn; eauto.
  - intros t t' Ht Hstep u Hu.
    eapply (rc_step S2 H2 (tm_app t u) (tm_app t' u)).
    + apply Ht. exact Hu.
    + apply ST_App1; [exact Hstep|]. exact (rc_lc S1 H1 u Hu).
  - intros t1 t2 Ht1 Ht2 u Hu.
    assert (Hlc1 : locally_closed_tm t1).
    { pose proof (Ht1 (tm_fvar 0) (fvar_in_RC S1 0 H1)) as Happ.
      pose proof (rc_lc S2 H2 (tm_app t1 (tm_fvar 0)) Happ) as Hlc.
      inversion Hlc; assumption. }
    assert (Hlc2 : locally_closed_tm t2).
    { pose proof (Ht2 (tm_fvar 0) (fvar_in_RC S1 0 H1)) as Happ.
      pose proof (rc_lc S2 H2 (tm_app t2 (tm_fvar 0)) Happ) as Hlc.
      inversion Hlc; assumption. }
    eapply (rc_neutral S2 H2 (tm_app (tm_choice t1 t2) u)).
    + apply lc_tm_app.
      * apply lc_tm_choice; assumption.
      * exact (rc_lc S1 H1 u Hu).
    + constructor.
    + intros z Hz. inversion Hz; subst.
      * inversion H3; subst; [exact (Ht1 u Hu)|exact (Ht2 u Hu)].
      * exfalso. match goal with Hv : value (tm_choice t1 t2) |- _ => inversion Hv end.
  - intros t Hlc Hn Hred u Hu.
    eapply (rc_neutral S2 H2 (tm_app t u)).
    + apply lc_tm_app; [exact Hlc|exact (rc_lc S1 H1 u Hu)].
    + constructor.
    + intros z Hz. inversion Hz; subst.
      * exfalso. eapply neutral_not_value; eauto using v_abs.
      * eapply Hred; eauto.
      * exfalso. eapply neutral_not_value; eauto.
Qed.

Lemma RC_all : forall F,
  (forall S, RC S -> RC (F S)) -> RC (all_set F).
Proof.
  intros F HF. constructor.
  - intros t Ht.
    specialize (Ht sn_set RC_sn (Ty_FVar 0) (lc_ty_fvar 0 0)).
    pose proof (rc_lc (F sn_set) (HF sn_set RC_sn)
      (tm_tapp t (Ty_FVar 0)) Ht) as Hlc.
    inversion Hlc; assumption.
  - intros t Ht.
    exact (sn_tapp_left t (Ty_FVar 0) (lc_ty_fvar 0 0)
      (rc_sn (F sn_set) (HF sn_set RC_sn) (tm_tapp t (Ty_FVar 0))
        (Ht sn_set RC_sn (Ty_FVar 0) (lc_ty_fvar 0 0)))).
  - intros t t' Ht Hstep S HS U HU.
    eapply (rc_step (F S) (HF S HS) (tm_tapp t U) (tm_tapp t' U)).
    + apply Ht; assumption.
    + apply ST_TApp; assumption.
  - intros t1 t2 Ht1 Ht2 S HS U HU.
    assert (Hlc1 : locally_closed_tm t1).
    { pose proof (Ht1 sn_set RC_sn (Ty_FVar 0) (lc_ty_fvar 0 0)) as Ht.
      pose proof (rc_lc (F sn_set) (HF sn_set RC_sn)
        (tm_tapp t1 (Ty_FVar 0)) Ht) as Hlc. inversion Hlc; assumption. }
    assert (Hlc2 : locally_closed_tm t2).
    { pose proof (Ht2 sn_set RC_sn (Ty_FVar 0) (lc_ty_fvar 0 0)) as Ht.
      pose proof (rc_lc (F sn_set) (HF sn_set RC_sn)
        (tm_tapp t2 (Ty_FVar 0)) Ht) as Hlc. inversion Hlc; assumption. }
    eapply (rc_neutral (F S) (HF S HS) (tm_tapp (tm_choice t1 t2) U)).
    + apply lc_tm_tapp; [apply lc_tm_choice; assumption|exact HU].
    + constructor.
    + intros z Hz. inversion Hz; subst.
      * inversion H1; subst; [apply Ht1|apply Ht2]; assumption.
  - intros t Hlc Hn Hred S HS U HU.
    eapply (rc_neutral (F S) (HF S HS) (tm_tapp t U)).
    + apply lc_tm_tapp; assumption.
    + constructor.
    + intros z Hz. inversion Hz; subst.
      * exfalso. eapply neutral_not_value; eauto using v_tabs.
      * apply Hred; assumption.
Qed.

Record sem_env : Type := SemEnv {
  sem_bound : list red_set;
  sem_free : atom -> red_set
}.

Definition sem_valid (rho : sem_env) : Prop :=
  Forall RC (sem_bound rho) /\ (forall X, RC (sem_free rho X)).

Definition sem_extend_bound (rho : sem_env) (S : red_set) : sem_env :=
  SemEnv (S :: sem_bound rho) (sem_free rho).

Fixpoint interp (rho : sem_env) (T : ty) : red_set :=
  match T with
  | Ty_BVar i => nth i (sem_bound rho) sn_set
  | Ty_FVar X => sem_free rho X
  | Ty_Arrow T1 T2 => arr_set (interp rho T1) (interp rho T2)
  | Ty_All T1 => all_set (fun S => interp (sem_extend_bound rho S) T1)
  end.

Fixpoint insert_bound (k : nat) (C : red_set) (xs : list red_set) : list red_set :=
  match k, xs with
  | 0, _ => C :: xs
  | Datatypes.S k', a :: xs' => a :: insert_bound k' C xs'
  | S _, [] => []
  end.

Definition sem_insert_bound (rho : sem_env) (k : nat) (C : red_set) : sem_env :=
  SemEnv (insert_bound k C (sem_bound rho)) (sem_free rho).

Lemma insert_bound_succ_cons : forall k C a xs,
  insert_bound (Datatypes.S k) C (a :: xs) = a :: insert_bound k C xs.
Proof. reflexivity. Qed.

Lemma ltb_succ_succ : forall i k, Nat.ltb (S i) (S k) = Nat.ltb i k.
Proof. reflexivity. Qed.
Lemma eqb_succ_succ : forall i k, Nat.eqb (S i) (S k) = Nat.eqb i k.
Proof. reflexivity. Qed.

Lemma nth_insert_bound : forall xs k C i d,
  k <= length xs ->
  nth i (insert_bound k C xs) d =
    if Nat.ltb i k then nth i xs d
    else if Nat.eqb i k then C else nth (Nat.pred i) xs d.
Proof.
  induction xs as [|a xs IH]; intros [|k] C i d Hlen.
  - destruct i; reflexivity.
  - simpl in Hlen. lia.
  - destruct i; simpl; reflexivity.
  - simpl in Hlen. destruct i; simpl.
    + reflexivity.
    + rewrite ltb_succ_succ. rewrite IH by lia.
      destruct (Nat.ltb i k) eqn:E1; destruct (Nat.eqb i k) eqn:E2; simpl.
      * apply Nat.ltb_lt in E1. apply Nat.eqb_eq in E2. lia.
      * reflexivity.
      * apply Nat.ltb_ge in E1. apply Nat.eqb_eq in E2. subst. reflexivity.
      * apply Nat.ltb_ge in E1. apply Nat.eqb_neq in E2.
        assert (i > k) by lia.
        destruct i; simpl in *; try lia. reflexivity.
Qed.

Lemma not_in_app_lists : forall (x : atom) (l1 l2 : list atom),
  ~ In x (l1 ++ l2) -> ~ In x l1 /\ ~ In x l2.
Proof.
  intros x l1 l2 H. split; intros Hin; apply H; apply in_or_app; auto.
Qed.

Definition red_equiv (S T : red_set) : Prop := forall t, S t <-> T t.

Definition sem_free_update (rho : sem_env) (X : atom) (S : red_set) : sem_env :=
  SemEnv (sem_bound rho) (fun Y => if Nat.eqb X Y then S else sem_free rho Y).

Lemma sem_extend_insert : forall rho k C D,
  sem_insert_bound (sem_extend_bound rho C) (Datatypes.S k) D =
  sem_extend_bound (sem_insert_bound rho k D) C.
Proof. intros; unfold sem_insert_bound, sem_extend_bound; simpl. reflexivity. Qed.

Lemma interp_open_ty_fvar_at : forall T rho k X C,
  k <= length (sem_bound rho) ->
  lc_ty_at (S k) T -> ~ In X (fv_ty T) ->
  red_equiv (interp (sem_insert_bound rho k C) T)
    (interp (sem_free_update rho X C) (open_ty_rec k (Ty_FVar X) T)).
Proof.
  induction T; intros rho k X C Hlen Hlc Hfresh; simpl in *.
  - inversion Hlc; subst.
    destruct (Nat.lt_ge_cases n k) as [Hlt|Hge].
    + unfold red_equiv. intros t. rewrite (nth_insert_bound (sem_bound rho) k C n sn_set Hlen).
      assert (Nat.ltb n k = true) by (apply Nat.ltb_lt; exact Hlt).
      assert (Nat.eqb k n = false) by (apply Nat.eqb_neq; lia).
      rewrite H, H0. simpl. tauto.
    + assert (n = k) by lia. subst n. unfold red_equiv. intros t.
      rewrite (nth_insert_bound (sem_bound rho) k C k sn_set Hlen).
      assert (Nat.ltb k k = false) by (apply Nat.ltb_ge; lia).
      assert (Nat.eqb k k = true) by apply Nat.eqb_refl.
      rewrite H, H0. simpl. rewrite Nat.eqb_refl. tauto.
  - assert (X <> a) by (intro E; subst; apply Hfresh; simpl; auto).
    unfold red_equiv, sem_free_update. intros t. simpl.
    destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E. contradiction.
    + tauto.
  - apply not_in_app_lists in Hfresh as [H1 H2].
    inversion Hlc; subst. unfold red_equiv in *; intros t; simpl.
    specialize (IHT1 rho k X C Hlen H4 H1).
    specialize (IHT2 rho k X C Hlen H5 H2).
    unfold arr_set. split; intros H u Hu.
    + apply (proj1 (IHT2 (tm_app t u))). apply H. apply (proj2 (IHT1 u)); exact Hu.
    + apply (proj2 (IHT2 (tm_app t u))). apply H. apply (proj1 (IHT1 u)); exact Hu.
  - simpl in Hfresh. inversion Hlc; subst.
    unfold red_equiv, all_set. intros t. split; intros H S HS U HU.
    + apply (proj1 (IHT (sem_extend_bound rho S) (Datatypes.S k) X C
        ltac:(simpl; lia) H1 Hfresh (tm_tapp t U))).
      rewrite sem_extend_insert. apply H; assumption.
    + rewrite <- sem_extend_insert.
      apply (proj2 (IHT (sem_extend_bound rho S) (Datatypes.S k) X C
        ltac:(simpl; lia) H1 Hfresh (tm_tapp t U))).
      apply H; assumption.
Qed.

Lemma interp_insert_proper : forall T rho k C D,
  k <= length (sem_bound rho) -> red_equiv C D ->
  red_equiv (interp (sem_insert_bound rho k C) T)
    (interp (sem_insert_bound rho k D) T).
Proof.
  induction T; intros rho k C D Hlen Heq t; simpl.
  - unfold red_equiv in *. destruct (Nat.lt_trichotomy n k) as [Hlt|[Heqnk|Hgt]].
    + rewrite (nth_insert_bound (sem_bound rho) k C n sn_set Hlen),
        (nth_insert_bound (sem_bound rho) k D n sn_set Hlen).
      assert (Nat.ltb n k = true) by (apply Nat.ltb_lt; exact Hlt).
      assert (Nat.eqb n k = false) by (apply Nat.eqb_neq; lia).
      rewrite H. tauto.
    + subst n. rewrite (nth_insert_bound (sem_bound rho) k C k sn_set Hlen),
        (nth_insert_bound (sem_bound rho) k D k sn_set Hlen).
      assert (Nat.ltb k k = false) by (apply Nat.ltb_ge; lia).
      rewrite H. rewrite Nat.eqb_refl. apply Heq.
    + rewrite (nth_insert_bound (sem_bound rho) k C n sn_set Hlen),
        (nth_insert_bound (sem_bound rho) k D n sn_set Hlen).
      assert (Nat.ltb n k = false) by (apply Nat.ltb_ge; lia).
      assert (Nat.eqb n k = false) by (apply Nat.eqb_neq; lia).
      rewrite H, H0. tauto.
  - unfold red_equiv. tauto.
  - unfold red_equiv in *; simpl. unfold arr_set. split; intros H u Hu.
    + apply (proj1 (IHT2 rho k C D Hlen Heq (tm_app t u))). apply H.
      apply (proj2 (IHT1 rho k C D Hlen Heq u)); exact Hu.
    + apply (proj2 (IHT2 rho k C D Hlen Heq (tm_app t u))). apply H.
      apply (proj1 (IHT1 rho k C D Hlen Heq u)); exact Hu.
  - unfold red_equiv, all_set. split; intros H S HS U HU.
    + apply (proj1 (IHT (sem_extend_bound rho S) (Datatypes.S k) C D
        ltac:(simpl; lia) Heq (tm_tapp t U))).
      rewrite sem_extend_insert. apply H; assumption.
    + rewrite <- sem_extend_insert.
      apply (proj2 (IHT (sem_extend_bound rho S) (Datatypes.S k) C D
        ltac:(simpl; lia) Heq (tm_tapp t U))).
      apply H; assumption.
Qed.

Lemma interp_bound_irrel_at : forall T rho k C,
  k <= length (sem_bound rho) -> lc_ty_at k T ->
  red_equiv (interp (sem_insert_bound rho k C) T) (interp rho T).
Proof.
  induction T; intros rho k C Hlen Hlc; simpl in *.
  - inversion Hlc; subst. unfold red_equiv. intros t.
    rewrite (nth_insert_bound (sem_bound rho) k C n sn_set Hlen).
    assert (Nat.ltb n k = true) by (apply Nat.ltb_lt; assumption).
    rewrite H. tauto.
  - unfold red_equiv. tauto.
  - inversion Hlc; subst. unfold red_equiv in *; intros t; simpl.
    specialize (IHT1 rho k C Hlen H2).
    specialize (IHT2 rho k C Hlen H3).
    unfold arr_set. split; intros H u Hu.
    + apply (proj1 (IHT2 (tm_app t u))). apply H. apply (proj2 (IHT1 u)); exact Hu.
    + apply (proj2 (IHT2 (tm_app t u))). apply H. apply (proj1 (IHT1 u)); exact Hu.
  - inversion Hlc; subst. unfold red_equiv, all_set. intros t. split; intros H C' HC U HU.
    + apply (proj1 (IHT (sem_extend_bound rho C') (Datatypes.S k) C
        ltac:(simpl; lia) H1 (tm_tapp t U))).
      rewrite sem_extend_insert. apply H; assumption.
    + rewrite <- sem_extend_insert.
      apply (proj2 (IHT (sem_extend_bound rho C') (Datatypes.S k) C
        ltac:(simpl; lia) H1 (tm_tapp t U))).
      apply H; assumption.
Qed.

Lemma interp_open_ty_bound_at : forall T U rho k,
  k <= length (sem_bound rho) -> lc_ty_at (Datatypes.S k) T ->
  locally_closed_ty U ->
  red_equiv (interp (sem_insert_bound rho k (interp rho U)) T)
    (interp rho (open_ty_rec k U T)).
Proof.
  induction T; intros U rho k Hlen Hlc HU; simpl in *.
  - inversion Hlc; subst. unfold red_equiv. intros t.
    destruct (Nat.lt_ge_cases n k) as [Hlt|Hge].
    + rewrite (nth_insert_bound (sem_bound rho) k (interp rho U) n sn_set Hlen).
      assert (Nat.ltb n k = true) by (apply Nat.ltb_lt; exact Hlt).
      assert (Nat.eqb k n = false) by (apply Nat.eqb_neq; lia).
      rewrite H, H0. simpl. tauto.
    + assert (n = k) by lia. subst n.
      rewrite (nth_insert_bound (sem_bound rho) k (interp rho U) k sn_set Hlen).
      assert (Nat.ltb k k = false) by (apply Nat.ltb_ge; lia).
      assert (Nat.eqb k k = true) by apply Nat.eqb_refl.
      rewrite H, H0. tauto.
  - unfold red_equiv. tauto.
  - inversion Hlc; subst. unfold red_equiv in *; intros t; simpl.
    specialize (IHT1 U rho k Hlen H2 HU).
    specialize (IHT2 U rho k Hlen H3 HU).
    unfold arr_set. split; intros H u Hu.
    + apply (proj1 (IHT2 (tm_app t u))). apply H. apply (proj2 (IHT1 u)); exact Hu.
    + apply (proj2 (IHT2 (tm_app t u))). apply H. apply (proj1 (IHT1 u)); exact Hu.
  - inversion Hlc; subst. unfold red_equiv, all_set. intros t. split; intros H C HC V HV.
    assert (HeqU : red_equiv (interp (sem_extend_bound rho C) U) (interp rho U)).
    { unfold sem_extend_bound.
      exact (interp_bound_irrel_at U rho 0 C (Nat.le_0_l _) HU). }
    + apply (proj1 (IHT U (sem_extend_bound rho C) (Datatypes.S k)
        ltac:(simpl; lia) H1 HU (tm_tapp t V))).
      apply (proj2 (interp_insert_proper T (sem_extend_bound rho C) (Datatypes.S k)
        (interp (sem_extend_bound rho C) U) (interp rho U)
        ltac:(simpl; lia) HeqU (tm_tapp t V))).
      rewrite sem_extend_insert. apply H; assumption.
    + assert (HeqU : red_equiv (interp (sem_extend_bound rho C) U) (interp rho U)).
      { unfold sem_extend_bound.
        exact (interp_bound_irrel_at U rho 0 C (Nat.le_0_l _) HU). }
      rewrite <- sem_extend_insert.
      apply (proj1 (interp_insert_proper T (sem_extend_bound rho C) (Datatypes.S k)
        (interp (sem_extend_bound rho C) U) (interp rho U)
        ltac:(simpl; lia) HeqU (tm_tapp t V))).
      apply (proj2 (IHT U (sem_extend_bound rho C) (Datatypes.S k)
        ltac:(simpl; lia) H1 HU (tm_tapp t V))).
      apply H; assumption.
Qed.

Lemma interp_free_update_irrel : forall T rho X C,
  ~ In X (fv_ty T) ->
  red_equiv (interp (sem_free_update rho X C) T) (interp rho T).
Proof.
  induction T; intros rho X C Hfresh; simpl in *.
  - unfold red_equiv. tauto.
  - assert (X <> a) by (intro E; subst; apply Hfresh; simpl; auto).
    unfold red_equiv, sem_free_update. intros t. simpl.
    destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E. contradiction.
    + tauto.
  - apply not_in_app_lists in Hfresh as [H1 H2].
    unfold red_equiv in *; intros t; simpl. unfold arr_set. split; intros H u Hu.
    + apply (proj1 (IHT2 rho X C H2 (tm_app t u))). apply H.
      apply (proj2 (IHT1 rho X C H1 u)); exact Hu.
    + apply (proj2 (IHT2 rho X C H2 (tm_app t u))). apply H.
      apply (proj1 (IHT1 rho X C H1 u)); exact Hu.
  - unfold red_equiv, all_set. intros t. split; intros H C' HC U HU.
    + apply (proj1 (IHT (sem_extend_bound rho C') X C Hfresh (tm_tapp t U))).
      apply H; assumption.
    + apply (proj2 (IHT (sem_extend_bound rho C') X C Hfresh (tm_tapp t U))).
      apply H; assumption.
Qed.

Definition env_rel (Delta : ty_context) (Gamma : context)
    (rho : sem_env) (theta : type_substitution) (gamma : term_substitution) : Prop :=
  (forall X, In X Delta -> RC (sem_free rho X) /\ locally_closed_ty (theta X)) /\
  (forall x T, In (x,T) Gamma -> interp rho T (gamma x)) /\
  type_substitution_closed theta /\ term_substitution_closed gamma.

Lemma sem_valid_free_update : forall rho X C,
  sem_valid rho -> RC C -> sem_valid (sem_free_update rho X C).
Proof.
  intros rho X C [Hb Hf] HC. split; [exact Hb|]. intros Y.
  unfold sem_free_update. simpl. destruct (Nat.eqb X Y); auto.
Qed.

Lemma in_context_ftv : forall Gamma x T X,
  In (x,T) Gamma -> In X (fv_ty T) -> In X (ftv_context Gamma).
Proof.
  induction Gamma as [|[y U] Gamma IH]; intros x T X Hin Hfv; simpl in *.
  - contradiction.
  - destruct Hin as [Hin|Hin].
    + inversion Hin; subst. apply in_or_app. left. exact Hfv.
    + apply in_or_app. right. eapply IH; eauto.
Qed.

Lemma type_substitution_update_related : forall Delta Gamma rho theta gamma X C U,
  sem_valid rho -> env_rel Delta Gamma rho theta gamma -> RC C ->
  locally_closed_ty U -> ~ In X Delta -> ~ In X (ftv_context Gamma) ->
  env_rel (X :: Delta) Gamma (sem_free_update rho X C)
    (type_subst_update theta X U) gamma.
Proof.
  intros Delta Gamma rho theta gamma X C U Hvalid Hrel HC HU Hfresh Hctxfresh.
  destruct Hrel as [Hfree [Hterms [Htheta Hgamma]]].
  unfold env_rel. split.
  - intros Y HY. simpl in HY. destruct HY as [HY|HY].
    + subst Y. split.
      * unfold sem_free_update. simpl. rewrite Nat.eqb_refl. exact HC.
      * unfold type_subst_update. rewrite Nat.eqb_refl. exact HU.
    + assert (Y <> X) by (intro E; subst; contradiction).
      split.
      * unfold sem_free_update. simpl. destruct (Nat.eqb X Y) eqn:E.
        -- apply Nat.eqb_eq in E. exfalso. apply H. symmetry. exact E.
        -- apply (proj1 (Hfree Y HY)).
      * unfold type_subst_update. destruct (Nat.eqb X Y) eqn:E.
        -- apply Nat.eqb_eq in E. exfalso. apply H. symmetry. exact E.
        -- apply (proj2 (Hfree Y HY)).
  - split.
    + intros x T Hin.
      assert (Hnotin : ~ In X (fv_ty T)).
      { intro Hfv. apply Hctxfresh. eapply in_context_ftv; eauto. }
      apply (proj2 (interp_free_update_irrel T rho X C Hnotin (gamma x))).
      apply Hterms with (x:=x) (T:=T). exact Hin.
    + split.
      * intros Y. unfold type_subst_update. destruct (Nat.eqb X Y); auto.
      * exact Hgamma.
Qed.

Lemma Forall_nth_default : forall (A : Type) (P : A -> Prop) xs n d,
  Forall P xs -> P d -> P (nth n xs d).
Proof.
  intros A P xs n d Hall. revert n d.
  induction Hall; intros [|n] d Hd; simpl; auto.
Qed.

Lemma sem_valid_extend_bound : forall rho S,
  sem_valid rho -> RC S -> sem_valid (sem_extend_bound rho S).
Proof.
  intros rho S [Hb Hf] HS. split.
  - constructor; assumption.
  - exact Hf.
Qed.

Lemma interp_soundness : forall T rho,
  sem_valid rho -> RC (interp rho T).
Proof.
  induction T; intros rho Hvalid; simpl.
  - destruct Hvalid as [Hb Hf]. eapply Forall_nth_default; eauto using RC_sn.
  - destruct Hvalid as [Hb Hf]. apply Hf.
  - apply RC_arr; [apply IHT1|apply IHT2]; assumption.
  - apply RC_all. intros S HS. apply IHT.
    eapply sem_valid_extend_bound; eauto.
Qed.

Lemma RC_app_lam : forall A t u S,
  RC S -> locally_closed_tm u -> strongly_normalizing u ->
  locally_closed_tm (tm_abs A t) ->
  (forall u', multi u u' -> S (open_tm t u')) ->
  S (tm_app (tm_abs A t) u).
Proof.
  intros A t u S HRC Hu Hsn Hlam Hbody.
  revert A t Hlam Hbody.
  induction Hsn as [u Hnext IH]; intros A t Hlam Hbody.
  eapply (rc_neutral S HRC (tm_app (tm_abs A t) u)).
  - apply lc_tm_app; assumption.
  - constructor.
  - intros z Hz. inversion Hz; subst.
    + apply Hbody. constructor.
    + exfalso. eapply value_no_step; [apply v_abs; exact Hlam|eassumption].
    + exact (IH t2' H3 (step_preserves_lc u t2' Hu H3) A t Hlam
        (fun u'' Hmulti => Hbody u'' (multi_step u t2' u'' H3 Hmulti))).
Qed.

Lemma RC_tapp_tabs : forall t U S,
  RC S -> locally_closed_tm (tm_tabs t) -> locally_closed_ty U ->
  S (open_tm_ty t U) -> S (tm_tapp (tm_tabs t) U).
Proof.
  intros t U S HRC Htabs HU Hbody.
  eapply (rc_neutral S HRC (tm_tapp (tm_tabs t) U)).
  - apply lc_tm_tapp; assumption.
  - constructor.
  - intros z Hz. inversion Hz; subst.
    + exact Hbody.
    + exfalso. eapply value_no_step; [apply v_tabs; exact Htabs|exact H1].
Qed.

Lemma sem_env_empty_valid :
  sem_valid (SemEnv [] (fun _ => sn_set)).
Proof.
  split; [constructor|]. intros X. apply RC_sn.
Qed.

Lemma type_substitution_update_closed : forall theta X U,
  type_substitution_closed theta -> locally_closed_ty U ->
  type_substitution_closed (type_subst_update theta X U).
Proof.
  intros theta X U Htheta HU Y. unfold type_subst_update.
  destruct (Nat.eqb X Y); auto.
Qed.

Lemma in_context_dom : forall Gamma x T,
  In (x,T) Gamma -> In x (dom_context Gamma).
Proof.
  induction Gamma as [|[y U] Gamma IH]; intros x T Hin; simpl in *.
  - contradiction.
  - destruct Hin as [Hin|Hin].
    + inversion Hin; subst. simpl. auto.
    + simpl. right. eapply IH; eauto.
Qed.

Lemma lookup_context_in : forall Gamma x T,
  lookup_context x Gamma = Some T -> In (x,T) Gamma.
Proof.
  induction Gamma as [|[y U] Gamma IH]; intros x T H; simpl in H.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. inversion H; subst. simpl. auto.
    + right. apply IH. exact H.
Qed.

Lemma term_substitution_update_related : forall Delta Gamma rho theta gamma x T u,
  sem_valid rho ->
  env_rel Delta Gamma rho theta gamma ->
  interp rho T u ->
  ~ In x (dom_context Gamma) ->
  env_rel Delta (update Gamma x T) rho theta
    (term_subst_update gamma x u).
Proof.
  intros Delta Gamma rho theta gamma x T u Hvalid Hrel Hu Hfresh.
  destruct Hrel as [Hfree [Hctx [Htheta Hgamma]]].
  unfold env_rel. split; [exact Hfree|]. split.
  - intros y A Hin. unfold update in Hin. simpl in Hin.
    destruct Hin as [Hin|Hin].
    + inversion Hin; subst. unfold term_subst_update. rewrite Nat.eqb_refl. exact Hu.
    + assert (Hy : y <> x).
      { intro E. subst y. apply Hfresh. eapply in_context_dom; eauto. }
      unfold term_subst_update. destruct (Nat.eqb x y) eqn:E.
      * apply Nat.eqb_eq in E. exfalso. apply Hy. symmetry. exact E.
      *
      apply Hctx with (x:=y) (T:=A). exact Hin.
  - split; [exact Htheta|]. intros y. unfold term_subst_update.
    destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst.
      exact (rc_lc (interp rho T) (interp_soundness T rho Hvalid) u Hu).
    + apply Hgamma.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T Hwf. induction Hwf as
    [Delta X Hin | Delta T1 T2 H1 IH1 H2 IH2 | L Delta T Hopen IH].
  - apply lc_ty_fvar.
  - constructor; assumption.
  - apply lc_ty_all.
    specialize (IH (fresh L) (fresh_notin L)).
    unfold locally_closed_ty in IH.
    eapply lc_ty_at_open_inv; exact IH.
Qed.

Lemma typing_lc_type : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_ty T.
Proof.
  intros Delta Gamma t T Htyping. induction Htyping as
    [Delta Gamma x T Hlookup Hwf
    | L Delta Gamma T1 t2 T2 Hwf Hbody IH
    | Delta Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
    | L Delta Gamma t T Hbody IH
    | Delta Gamma t T U Ht IH HwfU
    | Delta Gamma t1 t2 T H1 IH1 H2 IH2].
  - exact (wf_ty_lc Delta T Hwf).
  - apply lc_ty_arrow.
    + exact (wf_ty_lc Delta T1 Hwf).
    + specialize (IH (fresh L) (fresh_notin L)). exact IH.
  - inversion IH1; assumption.
  - apply lc_ty_all. specialize (IH (fresh L) (fresh_notin L)).
    unfold locally_closed_ty in IH. eapply lc_ty_at_open_inv; exact IH.
  - inversion IH; subst. apply lc_ty_at_open.
    + assumption.
    + exact (wf_ty_lc Delta U HwfU).
  - exact IH1.
Qed.

Lemma typing_lc_tm : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T Htyping. induction Htyping as
    [Delta Gamma x T Hlookup Hwf
    | L Delta Gamma T1 t2 T2 Hwf Hbody IH
    | Delta Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
    | L Delta Gamma t T Hbody IH
    | Delta Gamma t T U Ht IH HwfU
    | Delta Gamma t1 t2 T H1 IH1 H2 IH2].
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + exact (wf_ty_lc Delta T1 Hwf).
    + apply (lc_tm_at_open_tm_inv t2 0 0 (fresh L)).
      specialize (IH (fresh L) (fresh_notin L)). exact IH.
  - apply lc_tm_app; assumption.
  - apply lc_tm_tabs. apply (lc_tm_at_open_ty_inv t 0 0 (fresh L)).
    specialize (IH (fresh L) (fresh_notin L)). exact IH.
  - apply lc_tm_tapp.
    + exact IH.
    + exact (wf_ty_lc Delta U HwfU).
  - apply lc_tm_choice; assumption.
Qed.

Lemma instantiate_ty_lc_at : forall T k theta,
  lc_ty_at k T -> type_substitution_closed theta ->
  lc_ty_at k (instantiate_ty theta T).
Proof.
  induction T; intros k theta Hlc Htheta; simpl in *.
  - inversion Hlc; subst. constructor; assumption.
  - eapply lc_ty_at_monotone; [apply Htheta|lia].
  - inversion Hlc; subst. constructor; [eapply IHT1|eapply IHT2]; eauto.
  - inversion Hlc; subst. constructor. eapply IHT; eauto.
Qed.

Lemma instantiate_lc_at : forall t K k theta gamma,
  lc_tm_at K k t -> type_substitution_closed theta ->
  term_substitution_closed gamma -> lc_tm_at K k (instantiate theta gamma t).
Proof.
  induction t; intros K k theta gamma Hlc Htheta Hgamma; simpl in *.
  - assumption.
  - eapply lc_tm_at_monotone with (K:=0) (k:=0).
    + unfold locally_closed_tm. apply Hgamma.
    + lia.
    + lia.
  - inversion Hlc; subst. apply lc_tm_abs.
    + eapply instantiate_ty_lc_at; eauto.
    + eapply IHt; eauto.
  - inversion Hlc; subst. apply lc_tm_app; eauto.
  - inversion Hlc; subst. apply lc_tm_tabs. eapply IHt; eauto.
  - inversion Hlc; subst. apply lc_tm_tapp.
    + eapply IHt; eauto.
    + eapply instantiate_ty_lc_at; eauto.
  - inversion Hlc; subst. apply lc_tm_choice; eauto.
Qed.

Lemma rc_multi : forall S,
  RC S -> forall t u, S t -> multi t u -> S u.
Proof.
  intros S HRC t u Ht Hmulti. induction Hmulti.
  - exact Ht.
  - apply IHHmulti. eapply (rc_step S HRC x y); eauto.
Qed.

Lemma instantiate_ty_identity : forall T,
  instantiate_ty identity_type_substitution T = T.
Proof. induction T; simpl; try rewrite ?IHT, ?IHT1, ?IHT2; reflexivity. Qed.

Lemma instantiate_identity : forall t,
  instantiate identity_type_substitution identity_term_substitution t = t.
Proof.
  induction t; simpl; try rewrite ?instantiate_ty_identity, ?IHt, ?IHt1, ?IHt2;
    try reflexivity.
Qed.

Lemma instantiate_ty_open_rec_fresh : forall T theta X U k,
  type_substitution_closed theta -> locally_closed_ty U ->
  ~ In X (fv_ty T) ->
  instantiate_ty (type_subst_update theta X U)
    (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k U (instantiate_ty theta T).
Proof.
  induction T; intros theta X U k Htheta HU Hfresh; simpl in *.
  - destruct (Nat.eqb k n); simpl.
    + unfold type_subst_update. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - assert (Hneq : X <> a) by (intro E; subst; apply Hfresh; simpl; auto).
    unfold type_subst_update. destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E. contradiction.
    + rewrite open_ty_rec_lc_at.
      * reflexivity.
      * eapply lc_ty_at_monotone.
        -- apply Htheta.
        -- lia.
  - simpl in Hfresh. apply not_in_app_lists in Hfresh as [H1 H2].
    rewrite IHT1, IHT2; eauto.
  - rewrite IHT; eauto.
Qed.

Lemma instantiate_open_tm_rec_fresh : forall t theta gamma x u k,
  term_substitution_closed gamma ->
  ~ In x (fv_tm t) ->
  instantiate theta (term_subst_update gamma x u)
    (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k u (instantiate theta gamma t).
Proof.
  induction t; intros theta gamma x u k Hgamma Hfresh; simpl in *.
  - destruct (Nat.eqb k n); simpl.
    + unfold term_subst_update. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - assert (Hneq : x <> a) by (intro E; subst; apply Hfresh; simpl; auto).
    unfold term_subst_update. destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E. contradiction.
    + assert (Hlc : lc_tm_at 0 k (gamma a)).
      { eapply lc_tm_at_monotone with (K:=0) (k:=0).
        - unfold locally_closed_tm. apply Hgamma.
        - lia.
        - lia. }
      rewrite (open_tm_rec_lc_at (gamma a) 0 k u Hlc). reflexivity.
  - rewrite IHt; auto.
  - simpl in Hfresh. apply not_in_app_lists in Hfresh as [H1 H2]. rewrite IHt1, IHt2; auto.
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - simpl in Hfresh. apply not_in_app_lists in Hfresh as [H1 H2]. rewrite IHt1, IHt2; auto.
Qed.

Lemma instantiate_open_tm_ty_rec_fresh : forall t theta gamma X U k,
  type_substitution_closed theta -> locally_closed_ty U ->
  term_substitution_closed gamma ->
  ~ In X (ftv_tm t) ->
  instantiate (type_subst_update theta X U) gamma
    (open_tm_ty_rec k (Ty_FVar X) t) =
  open_tm_ty_rec k U (instantiate theta gamma t).
Proof.
  induction t; intros theta gamma X U k Htheta HU Hgamma Hfresh; simpl in *.
  - reflexivity.
  - assert (Hlc : lc_tm_at k 0 (gamma a)).
    { eapply lc_tm_at_monotone with (K:=0) (k:=0).
      - unfold locally_closed_tm. apply Hgamma.
      - lia.
      - lia. }
    rewrite (open_tm_ty_rec_lc_at (gamma a) k 0 U Hlc). reflexivity.
  - simpl in Hfresh. apply not_in_app_lists in Hfresh as [HT Ht].
    rewrite instantiate_ty_open_rec_fresh by eauto.
    rewrite (IHt theta gamma X U k Htheta HU Hgamma Ht). reflexivity.
  - simpl in Hfresh. apply not_in_app_lists in Hfresh as [H1 H2].
    rewrite (IHt1 theta gamma X U k Htheta HU Hgamma H1),
      (IHt2 theta gamma X U k Htheta HU Hgamma H2). reflexivity.
  - rewrite (IHt theta gamma X U (S k) Htheta HU Hgamma Hfresh). reflexivity.
  - simpl in Hfresh. apply not_in_app_lists in Hfresh as [Ht HT].
    rewrite (IHt theta gamma X U k Htheta HU Hgamma Ht).
    rewrite instantiate_ty_open_rec_fresh by eauto. reflexivity.
  - simpl in Hfresh. apply not_in_app_lists in Hfresh as [H1 H2].
    rewrite (IHt1 theta gamma X U k Htheta HU Hgamma H1),
      (IHt2 theta gamma X U k Htheta HU Hgamma H2). reflexivity.
Qed.

Theorem fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall rho theta gamma,
    sem_valid rho -> env_rel Delta Gamma rho theta gamma ->
    interp rho T (instantiate theta gamma t).
Proof.
  intros Delta Gamma t T Htyping. induction Htyping;
    intros rho theta gamma Hvalid Henv.
  - simpl. destruct Henv as [_ [Hterms _]].
    apply Hterms. eapply lookup_context_in; eauto.
  - simpl. intros u Hu.
    set (x := fresh (L ++ fv_tm t2 ++ dom_context Gamma)).
    pose proof (fresh_notin (L ++ fv_tm t2 ++ dom_context Gamma)) as Hfresh.
    apply not_in_app_lists in Hfresh as [HxL Hrest].
    apply not_in_app_lists in Hrest as [Hxfv Hxdom].
    assert (Hbodylc : locally_closed_tm (open_tm t2 (tm_fvar x))).
    { apply typing_lc_tm with (Delta:=Delta) (Gamma:=update Gamma x T1) (T:=T2).
      apply H0; exact HxL. }
    assert (Hlcabs : locally_closed_tm (tm_abs T1 t2)).
    { apply lc_tm_abs.
      - exact (wf_ty_lc Delta T1 H).
      - eapply lc_tm_at_open_tm_inv; exact Hbodylc. }
    assert (Henvx : env_rel Delta (update Gamma x T1) rho theta
        (term_subst_update gamma x u)).
    { eapply term_substitution_update_related; eauto. }
    assert (Hbodyu : interp rho T2
        (instantiate theta (term_subst_update gamma x u)
          (open_tm t2 (tm_fvar x)))).
    { apply (H1 x HxL rho theta (term_subst_update gamma x u) Hvalid Henvx). }
    unfold open_tm in Hbodyu. rewrite instantiate_open_tm_rec_fresh in Hbodyu.
    2: exact (proj2 (proj2 (proj2 Henv))).
    2: exact Hxfv.
    apply (RC_app_lam (instantiate_ty theta T1) (instantiate theta gamma t2) u
      (interp rho T2) (interp_soundness T2 rho Hvalid)).
    + exact (rc_lc (interp rho T1) (interp_soundness T1 rho Hvalid) u Hu).
    + exact (rc_sn (interp rho T1) (interp_soundness T1 rho Hvalid) u Hu).
    + exact (instantiate_lc_at (tm_abs T1 t2) 0 0 theta gamma Hlcabs
        (proj1 (proj2 (proj2 Henv))) (proj2 (proj2 (proj2 Henv)))).
    + intros u' Hmulti.
      assert (Hu' : interp rho T1 u').
      { eapply rc_multi; [apply interp_soundness; exact Hvalid|exact Hu|exact Hmulti]. }
      assert (Henvx' : env_rel Delta (update Gamma x T1) rho theta
          (term_subst_update gamma x u')).
      { eapply term_substitution_update_related; eauto. }
      assert (Hbodyu' : interp rho T2
          (instantiate theta (term_subst_update gamma x u')
            (open_tm t2 (tm_fvar x)))).
      { apply (H1 x HxL rho theta (term_subst_update gamma x u') Hvalid Henvx'). }
      unfold open_tm in Hbodyu'. rewrite instantiate_open_tm_rec_fresh in Hbodyu'.
      2: exact (proj2 (proj2 (proj2 Henv))).
      2: exact Hxfv.
      exact Hbodyu'.
  - simpl. apply (IHHtyping1 rho theta gamma Hvalid Henv).
    apply (IHHtyping2 rho theta gamma Hvalid Henv).
  - simpl. intros S HS U HU.
    set (X := fresh (L ++ Delta ++ ftv_context Gamma ++ fv_ty T ++ ftv_tm t)).
    pose proof (fresh_notin (L ++ Delta ++ ftv_context Gamma ++ fv_ty T ++ ftv_tm t)) as Hfresh.
    apply not_in_app_lists in Hfresh as [HxL Hrest].
    apply not_in_app_lists in Hrest as [HxDelta Hrest].
    apply not_in_app_lists in Hrest as [Hxctx Hrest].
    apply not_in_app_lists in Hrest as [HxTy Hxftv].
    assert (Htypebody : has_type (X :: Delta) Gamma
        (open_tm_ty t (Ty_FVar X)) (open_ty T (Ty_FVar X))).
    { apply H; exact HxL. }
    assert (HvalidX : sem_valid (sem_free_update rho X S)).
    { apply sem_valid_free_update; assumption. }
    assert (HenvX : env_rel (X :: Delta) Gamma (sem_free_update rho X S)
        (type_subst_update theta X U) gamma).
    { eapply type_substitution_update_related; eauto. }
    pose proof (H0 X HxL (sem_free_update rho X S)
      (type_subst_update theta X U) gamma HvalidX HenvX) as Hopened.
    assert (HlcT1 : lc_ty_at 1 T).
    { pose proof (typing_lc_type _ _ _ _ Htypebody) as Hlc.
      unfold locally_closed_ty in Hlc. eapply lc_ty_at_open_inv; exact Hlc. }
    assert (HlcTabs : locally_closed_tm (tm_tabs t)).
    { apply lc_tm_tabs. apply (lc_tm_at_open_ty_inv t 0 0 X).
      apply typing_lc_tm with (Delta:=X::Delta) (Gamma:=Gamma)
        (T:=open_ty T (Ty_FVar X)). exact Htypebody. }
    assert (Htabsinst : locally_closed_tm (instantiate theta gamma (tm_tabs t))).
    { exact (instantiate_lc_at (tm_tabs t) 0 0 theta gamma HlcTabs
        (proj1 (proj2 (proj2 Henv))) (proj2 (proj2 (proj2 Henv)))). }
    change (interp (sem_extend_bound rho S) T
      (tm_tapp (instantiate theta gamma (tm_tabs t)) U)).
    eapply RC_tapp_tabs with (t:=instantiate theta gamma t) (U:=U)
      (S:=interp (sem_extend_bound rho S) T).
    + apply interp_soundness. eapply sem_valid_extend_bound; eauto.
    + exact Htabsinst.
    + exact HU.
    + apply (proj2 (interp_open_ty_fvar_at T rho 0 X S
        (Nat.le_0_l _) HlcT1 HxTy (open_tm_ty (instantiate theta gamma t) U))).
      unfold open_tm_ty in Hopened. rewrite instantiate_open_tm_ty_rec_fresh in Hopened.
      2: exact (proj1 (proj2 (proj2 Henv))).
      2: exact HU.
      2: exact (proj2 (proj2 (proj2 Henv))).
      2: exact Hxftv.
      exact Hopened.
  - simpl. pose proof (IHHtyping rho theta gamma Hvalid Henv) as Hfun.
    assert (HU : locally_closed_ty (instantiate_ty theta U)).
    { eapply instantiate_ty_lc_at; [apply wf_ty_lc with (Delta:=Delta); exact H|].
      exact (proj1 (proj2 (proj2 Henv))). }
    assert (HlcT : lc_ty_at 1 T).
    { pose proof (typing_lc_type _ _ _ _ Htyping) as Hlc.
      inversion Hlc; subst; assumption. }
    change (all_set (fun S => interp (sem_extend_bound rho S) T)
      (instantiate theta gamma t)) in Hfun.
    specialize (Hfun (interp rho U) (interp_soundness U rho Hvalid)
      (instantiate_ty theta U) HU).
    apply (proj1 (interp_open_ty_bound_at T U rho 0
      (Nat.le_0_l _) HlcT (wf_ty_lc Delta U H) (tm_tapp (instantiate theta gamma t) (instantiate_ty theta U)))).
    exact Hfun.
  - simpl. destruct Henv as [Hfree [Hterms [Htheta Hgamma]]].
    eapply rc_choice.
    + apply interp_soundness; exact Hvalid.
    + apply (IHHtyping1 rho theta gamma Hvalid (conj Hfree (conj Hterms (conj Htheta Hgamma)))).
    + apply (IHHtyping2 rho theta gamma Hvalid (conj Hfree (conj Hterms (conj Htheta Hgamma)))).
Qed.

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  intros t T Htyping.
  set (rho := SemEnv [] (fun _ => sn_set)).
  assert (Hvalid : sem_valid rho).
  { unfold rho. apply sem_env_empty_valid. }
  assert (Henv : env_rel [] [] rho identity_type_substitution identity_term_substitution).
  { unfold env_rel. split.
    - intros X Hin. contradiction.
    - split.
      + intros x U Hin. contradiction.
      + split; [apply identity_type_substitution_closed|apply identity_term_substitution_closed]. }
  pose proof (fundamental [] [] t T Htyping rho
    identity_type_substitution identity_term_substitution Hvalid Henv) as Hred.
  rewrite instantiate_identity in Hred.
  exact (rc_sn (interp rho T) (interp_soundness T rho Hvalid) t Hred).
Qed.

End SystemFNormalizationNondeterminismEasyTask.
