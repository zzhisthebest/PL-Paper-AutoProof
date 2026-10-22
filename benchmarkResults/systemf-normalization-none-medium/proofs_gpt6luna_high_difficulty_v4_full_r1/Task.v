(** System F CBV strong-normalization benchmark, Easy variant.
    Features: none. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFNormalizationNoneEasyTask.

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
  end.

Fixpoint ftv_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_fvar _ => []
  | tm_abs T t1 => fv_ty T ++ ftv_tm t1
  | tm_app t1 t2 => ftv_tm t1 ++ ftv_tm t2
  | tm_tabs t1 => ftv_tm t1
  | tm_tapp t1 T => ftv_tm t1 ++ fv_ty T
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

(* Candidates are interpreted under semantic assignments for free and
   bound type variables.  The bound-variable environment makes the
   interpretation structurally recursive even at universal types. *)
Definition candidate := tm -> Prop.
Definition candidate_env := atom -> candidate.
Definition candidate_env_update (rho : candidate_env) (X : atom)
    (C : candidate) : candidate_env :=
  fun Y => if Nat.eqb X Y then C else rho Y.
Definition candidate_top : candidate := fun t =>
  strongly_normalizing t /\ locally_closed_tm t.
Definition candidate_ok (C : candidate) : Prop :=
  (forall t, C t -> strongly_normalizing t) /\
  (forall t, C t -> locally_closed_tm t) /\
  (forall t u, t --> u -> C u -> C t) /\
  (forall t u, t --> u -> C t -> C u) /\
  (forall t, locally_closed_tm t -> ~ value t ->
     (forall u, t --> u -> C u) -> C t).

Fixpoint reducible (rho : candidate_env) (bs : list candidate)
    (T : ty) : candidate :=
  match T with
  | Ty_BVar i => nth i bs candidate_top
  | Ty_FVar X => rho X
  | Ty_Arrow A B => fun t =>
      strongly_normalizing t /\
      locally_closed_tm t /\
      (forall v, reducible rho bs A v ->
         reducible rho bs B (tm_app t v))
  | Ty_All U => fun t =>
      strongly_normalizing t /\
      locally_closed_tm t /\
      (forall T' (C : candidate), locally_closed_ty T' ->
         candidate_ok C ->
         reducible rho (C :: bs) U (tm_tapp t T'))
  end.

Definition candidate_env_ok (rho : candidate_env) : Prop :=
  forall X, candidate_ok (rho X).

Lemma reducible_sn : forall rho bs T t,
  candidate_env_ok rho -> Forall candidate_ok bs ->
  reducible rho bs T t -> strongly_normalizing t.
Proof.
  intros rho bs T t Hrho Hbs H. destruct T; simpl in H.
  - revert bs Hbs H. induction n; intros bs Hbs H.
    + destruct bs as [|C bs]; simpl in H.
      * destruct H as [Hsn _]. exact Hsn.
      * inversion Hbs; subst. destruct H2 as [Hgood _]. eapply Hgood. exact H.
    + destruct bs as [|C bs]; simpl in H.
      * destruct H as [Hsn _]. exact Hsn.
      * inversion Hbs; subst. eapply IHn; eauto.
  - destruct (Hrho a) as [Hgood _]. eapply Hgood. exact H.
  - tauto.
  - tauto.
Qed.

Lemma sn_step : forall t u,
  strongly_normalizing t -> t --> u -> strongly_normalizing u.
Proof.
  intros t u H. inversion H; subst. eauto.
Qed.

Lemma sn_value : forall v, value v -> strongly_normalizing v.
Proof.
  intros v Hv. constructor. intros u Hs.
  exfalso. eapply value_no_step; eauto.
Qed.

Lemma sn_abs : forall T t, locally_closed_tm (tm_abs T t) ->
  strongly_normalizing (tm_abs T t).
Proof. intros; apply sn_value; constructor; assumption. Qed.

Lemma sn_tabs : forall t, locally_closed_tm (tm_tabs t) ->
  strongly_normalizing (tm_tabs t).
Proof. intros; apply sn_value; constructor; assumption. Qed.

Lemma step_deterministic : forall t u v,
  t --> u -> t --> v -> u = v.
Proof.
  intros t u v Hstep. generalize dependent v.
  induction Hstep; intros w H2; inversion H2; subst; try reflexivity;
    eauto 8 using value_no_step, v_abs, v_tabs.
  all: try solve [exfalso; eapply value_no_step; [eauto using v_abs, v_tabs|eassumption]].
  all: try solve [f_equal; eapply IHHstep; eassumption].
  - exfalso. eapply value_no_step with (v:=tm_abs T t) (t:=t1');
      [constructor; exact H|exact H4].
  - exfalso. eapply value_no_step with (v:=v) (t:=t2'); eauto.
  - exfalso. eapply value_no_step with (v:=tm_abs T t) (t:=t1');
      [constructor; exact H3|exact Hstep].
Qed.

Lemma sn_predecessor : forall t u,
  t --> u -> strongly_normalizing u -> strongly_normalizing t.
Proof.
  intros t u Hstep Hsn. constructor. intros v Hv.
  assert (v = u) by (eapply step_deterministic; eauto).
  subst. exact Hsn.
Qed.

Lemma step_lc_backward : forall t u,
  t --> u -> locally_closed_tm u -> locally_closed_tm t.
Proof.
  intros t u Hstep. induction Hstep; intros Hlc.
  - apply lc_tm_app; [exact H|apply value_regular; exact H0].
  - inversion Hlc; subst. apply lc_tm_app.
    + eapply IHHstep; eassumption.
    + assumption.
  - inversion Hlc; subst. apply lc_tm_app.
    + apply value_regular. assumption.
    + eapply IHHstep; eassumption.
  - apply lc_tm_tapp; assumption.
  - inversion Hlc; subst. apply lc_tm_tapp.
    + eapply IHHstep; eassumption.
    + assumption.
Qed.

Lemma step_lc_forward : forall t u,
  t --> u -> locally_closed_tm t -> locally_closed_tm u.
Proof.
  intros t u Hstep. induction Hstep; intros Hlc.
  - inversion Hlc; subst.
    apply open_tm_preserves_lc_at with (K:=0) (k:=0).
    + inversion H; assumption.
    + apply value_regular. assumption.
  - inversion Hlc; subst. apply lc_tm_app.
    + eapply IHHstep; eassumption.
    + assumption.
  - inversion Hlc; subst. apply lc_tm_app.
    + apply value_regular. assumption.
    + eapply IHHstep; eassumption.
  - inversion Hlc; subst.
    apply open_tm_ty_preserves_lc_at with (K:=0) (k:=0).
    + inversion H; assumption.
    + assumption.
  - inversion Hlc; subst. apply lc_tm_tapp.
    + eapply IHHstep; eassumption.
    + assumption.
Qed.

Lemma step_app_neutral : forall t v w,
  ~ value t -> tm_app t v --> w ->
  exists t', t --> t' /\ w = tm_app t' v.
Proof.
  intros t v w Hnv Hstep. inversion Hstep; subst.
  - exfalso. apply Hnv. constructor. assumption.
  - eexists; split; eauto.
  - exfalso. apply Hnv. assumption.
Qed.

Lemma step_tapp_neutral : forall t T w,
  ~ value t -> tm_tapp t T --> w ->
  exists t', t --> t' /\ w = tm_tapp t' T.
Proof.
  intros t T w Hnv Hstep. inversion Hstep; subst.
  - exfalso. apply Hnv. constructor. assumption.
  - eexists; split; eauto.
Qed.

Lemma candidate_top_ok : candidate_ok candidate_top.
Proof.
  unfold candidate_top, candidate_ok.
  split.
  - intros t [Hsn _]. exact Hsn.
  - split.
    + intros t [_ Hlc]. exact Hlc.
    + split.
      * intros t u Hstep [Hsn Hlc]. split.
        -- eapply sn_predecessor; eauto.
        -- eapply step_lc_backward; eauto.
      * split.
        -- intros t u Hstep [Hsn Hlc]. split.
           ++ eapply sn_step; eauto.
           ++ eapply step_lc_forward; eauto.
        -- intros t Hlc Hnv Hall. split.
           ++ constructor. intros u Hstep. exact (proj1 (Hall u Hstep)).
           ++ exact Hlc.
Qed.

Lemma lc_value_or_not : forall t,
  locally_closed_tm t -> value t \/ ~ value t.
Proof.
  intros t Hlc. destruct t.
  - right. intros Hv. inversion Hv.
  - right. intros Hv. inversion Hv.
  - inversion Hlc; subst. left. constructor. assumption.
  - right. intros Hv. inversion Hv.
  - inversion Hlc; subst. left. constructor. assumption.
  - right. intros Hv. inversion Hv.
Qed.

Lemma nth_candidate_ok : forall n bs,
  Forall candidate_ok bs -> candidate_ok (nth n bs candidate_top).
Proof.
  induction n; intros bs Hbs.
  - destruct bs as [|C bs]; simpl.
    + apply candidate_top_ok.
    + inversion Hbs; assumption.
  - destruct bs as [|C bs]; simpl.
    + apply candidate_top_ok.
    + inversion Hbs; subst. eapply IHn. assumption.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T Hwf. induction Hwf.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; assumption.
  - unfold locally_closed_ty.
    assert (Hfresh : ~ In (fresh L) L) by apply fresh_notin.
    specialize (H0 (fresh L) Hfresh).
    unfold locally_closed_ty in H0.
    apply lc_ty_at_open_inv in H0. apply lc_ty_all. exact H0.
Qed.

Lemma has_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T Hty. induction Hty.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + exact (wf_ty_lc _ _ H).
    + assert (Hfresh : ~ In (fresh L) L) by apply fresh_notin.
      specialize (H1 (fresh L) Hfresh).
      apply lc_tm_at_open_tm_inv in H1. exact H1.
  - apply lc_tm_app; assumption.
  - apply lc_tm_tabs.
    assert (Hfresh : ~ In (fresh L) L) by apply fresh_notin.
    specialize (H0 (fresh L) Hfresh).
    apply lc_tm_at_open_ty_inv in H0. exact H0.
  - apply lc_tm_tapp.
    + assumption.
    + exact (wf_ty_lc _ _ H).
Qed.

Lemma has_type_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_ty T.
Proof.
  intros Delta Gamma t T Hty. induction Hty.
  - exact (wf_ty_lc _ _ H0).
  - apply lc_ty_arrow.
    + exact (wf_ty_lc _ _ H).
    + assert (Hfresh : ~ In (fresh L) L) by apply fresh_notin.
      exact (H1 (fresh L) Hfresh).
  - inversion IHHty1; subst. assumption.
  - unfold locally_closed_ty.
    assert (Hfresh : ~ In (fresh L) L) by apply fresh_notin.
    specialize (H0 (fresh L) Hfresh).
    unfold locally_closed_ty in H0.
    apply lc_ty_at_open_inv in H0. apply lc_ty_all. exact H0.
  - apply lc_ty_at_open.
    + inversion IHHty; subst. assumption.
    + exact (wf_ty_lc _ _ H).
Qed.

Lemma instantiate_ty_lc_at : forall T k theta,
  lc_ty_at k T -> type_substitution_closed theta ->
  lc_ty_at k (instantiate_ty theta T).
Proof.
  induction T; intros k theta Hlc Htheta; inversion Hlc; subst; simpl.
  - apply lc_ty_bvar. assumption.
  - eapply lc_ty_at_monotone; [apply Htheta|lia].
  - apply lc_ty_arrow; eauto.
  - apply lc_ty_all. eapply IHT; eauto.
Qed.

Lemma instantiate_lc_tm_at : forall t K k theta gamma,
  lc_tm_at K k t -> type_substitution_closed theta ->
  term_substitution_closed gamma ->
  lc_tm_at K k (instantiate theta gamma t).
Proof.
  induction t; intros K k theta gamma Hlc Htheta Hgamma;
    inversion Hlc; subst; simpl.
  - apply lc_tm_bvar. assumption.
  - eapply (lc_tm_at_monotone 0 0 K k (gamma a)); [apply Hgamma|lia|lia].
  - apply lc_tm_abs.
    + eapply instantiate_ty_lc_at; eauto.
    + eapply IHt; eauto.
  - apply lc_tm_app; eauto.
  - apply lc_tm_tabs. eapply IHt; eauto.
  - apply lc_tm_tapp.
    + eapply IHt; eauto.
    + eapply instantiate_ty_lc_at; eauto.
Qed.

Lemma instantiate_lc_tm : forall t theta gamma,
  locally_closed_tm t -> type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm (instantiate theta gamma t).
Proof. intros; eapply instantiate_lc_tm_at; eauto. Qed.

Lemma reducible_lc : forall rho bs T t,
  candidate_env_ok rho -> Forall candidate_ok bs ->
  reducible rho bs T t -> locally_closed_tm t.
Proof.
  intros rho bs T t Hrho Hbs H. destruct T; simpl in H.
  - revert bs Hbs H. induction n; intros bs Hbs H.
    + destruct bs as [|C bs]; simpl in H.
      * destruct H as [_ Hlc]. exact Hlc.
      * inversion Hbs; subst. destruct H2 as [_ [Hlc _]]. eapply Hlc; exact H.
    + destruct bs as [|C bs]; simpl in H.
      * destruct H as [_ Hlc]. exact Hlc.
      * inversion Hbs; subst. eapply IHn; eauto.
  - destruct (Hrho a) as [_ [Hlc _]]. eapply Hlc; exact H.
  - tauto.
  - tauto.
Qed.

Lemma reducible_candidate_ok : forall T rho bs,
  candidate_env_ok rho -> Forall candidate_ok bs ->
  candidate_ok (reducible rho bs T).
Proof.
  induction T; intros rho bs Hrho Hbs; simpl.
  - apply nth_candidate_ok. exact Hbs.
  - apply Hrho.
  - split.
    + intros t Hred. exact (reducible_sn rho bs (Ty_Arrow T1 T2) t Hrho Hbs Hred).
    + split.
      * intros t Hred. exact (reducible_lc rho bs (Ty_Arrow T1 T2) t Hrho Hbs Hred).
      * split.
        -- intros t u Hstep [Hsn [Hlc Happ]]. split.
           ++ eapply sn_predecessor; eauto.
           ++ split.
              ** eapply step_lc_backward; eauto.
              ** intros v HAv.
                 pose proof (IHT2 rho bs Hrho Hbs) as HokB.
                 destruct HokB as [_ [_ [Hback _]]].
                 eapply Hback.
                 --- apply ST_App1; [exact Hstep|].
                     eapply reducible_lc; eauto.
                 --- apply Happ; exact HAv.
        -- split.
           ++ intros t u Hstep [Hsn [Hlc Happ]]. split.
              ** eapply sn_step; eauto.
              ** split.
                 --- eapply step_lc_forward; eauto.
                 --- intros v HAv.
                     pose proof (IHT2 rho bs Hrho Hbs) as HokB.
                     destruct HokB as [_ [_ [_ [Hforward _]]]].
                     eapply Hforward.
                     +++ apply ST_App1; [exact Hstep|].
                         eapply reducible_lc; eauto.
                     +++ apply Happ; exact HAv.
           ++ intros t Hlc Hnv Hall. split.
              ** constructor. intros u Hstep.
                 exact (reducible_sn rho bs (Ty_Arrow T1 T2) u Hrho Hbs (Hall u Hstep)).
              ** split; [exact Hlc|]. intros v HAv.
                 pose proof (IHT2 rho bs Hrho Hbs) as HokB.
                 destruct HokB as [_ [_ [_ [_ HsatB]]]].
                 apply HsatB.
                 --- apply lc_tm_app; [exact Hlc|].
                     eapply reducible_lc; eauto.
                 --- intro Hv. inversion Hv.
                 --- intros w Hstep.
                     destruct (step_app_neutral t v w Hnv Hstep)
                       as [t' [Ht' ->]].
                     pose proof (Hall t' Ht') as Hfun.
                     exact (proj2 (proj2 Hfun) v HAv).
  - split.
    + intros t Hred. exact (reducible_sn rho bs (Ty_All T) t Hrho Hbs Hred).
    + split.
      * intros t Hred. exact (reducible_lc rho bs (Ty_All T) t Hrho Hbs Hred).
      * split.
        -- intros t u Hstep [Hsn [Hlc Hall]]. split.
           ++ eapply sn_predecessor; eauto.
           ++ split.
              ** eapply step_lc_backward; eauto.
              ** intros T' C HT' HC.
                 assert (Hbs' : Forall candidate_ok (C :: bs)) by (constructor; assumption).
                 pose proof (IHT rho (C :: bs) Hrho Hbs') as HokBody.
                 destruct HokBody as [_ [_ [Hback _]]].
                 eapply Hback.
                 --- apply ST_TApp; [exact Hstep|exact HT'].
                 --- exact (Hall T' C HT' HC).
        -- split.
           ++ intros t u Hstep [Hsn [Hlc Hall]]. split.
              ** eapply sn_step; eauto.
              ** split.
                 --- eapply step_lc_forward; eauto.
                 --- intros T' C HT' HC.
                     assert (Hbs' : Forall candidate_ok (C :: bs)) by (constructor; assumption).
                     pose proof (IHT rho (C :: bs) Hrho Hbs') as HokBody.
                     destruct HokBody as [_ [_ [_ [Hforward _]]]].
                     eapply Hforward.
                     +++ apply ST_TApp; [exact Hstep|exact HT'].
                     +++ exact (Hall T' C HT' HC).
           ++ intros t Hlc Hnv Hall. split.
              ** constructor. intros u Hstep.
                 exact (reducible_sn rho bs (Ty_All T) u Hrho Hbs (Hall u Hstep)).
              ** split; [exact Hlc|].
                 intros T' C HT' HC.
                 assert (Hbs' : Forall candidate_ok (C :: bs)) by (constructor; assumption).
                 pose proof (IHT rho (C :: bs) Hrho Hbs') as HokBody.
                 destruct HokBody as [_ [_ [_ [_ HsatBody]]]].
                 apply HsatBody.
                 --- apply lc_tm_tapp; [exact Hlc|exact HT'].
                 --- intro Hv. inversion Hv.
                 --- intros w Hstep.
                     destruct (step_tapp_neutral t T' w Hnv Hstep)
                       as [t' [Ht' ->]].
                     destruct (Hall t' Ht') as [_ [_ Hrel]].
                     exact (Hrel T' C HT' HC).
Qed.

Fixpoint insert_candidate (n : nat) (C : candidate) (bs : list candidate)
    : list candidate :=
  match n, bs with
  | 0, _ => C :: bs
  | S n', [] => [C]
  | S n', b :: bs' => b :: insert_candidate n' C bs'
  end.

Lemma nth_insert_candidate_lt : forall n i C bs d,
  i < n -> n <= length bs ->
  nth i (insert_candidate n C bs) d = nth i bs d.
Proof.
  induction n; intros i C bs d Hlt Hlen; [lia|].
  destruct bs as [|b bs']; simpl in *; [lia|].
  destruct i; simpl.
  - reflexivity.
  - apply IHn; lia.
Qed.

Lemma nth_insert_candidate_eq : forall n C bs d,
  n <= length bs ->
  nth n (insert_candidate n C bs) d = C.
Proof.
  induction n; intros C bs d Hlen.
  - reflexivity.
  - destruct bs as [|b bs']; simpl in *; [lia|].
    simpl. rewrite IHn; [reflexivity|lia].
Qed.

Lemma insert_candidate_head : forall n C D bs,
  insert_candidate (S n) C (D :: bs) = D :: insert_candidate n C bs.
Proof. intros; simpl; reflexivity. Qed.

Lemma reducible_open_ty_rec_sem : forall T k rho bs X C,
  lc_ty_at (S k) T ->
  ~ In X (fv_ty T) ->
  k <= length bs ->
  forall t,
    reducible (candidate_env_update rho X C) bs
      (open_ty_rec k (Ty_FVar X) T) t <->
    reducible rho (insert_candidate k C bs) T t.
Proof.
  induction T; intros k rho bs X C Hlc Hfresh Hlen t; simpl in *.
  - inversion Hlc; subst.
    destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n.
      unfold candidate_env_update.
      destruct (Nat.eqb X X) eqn:E2; [simpl|apply Nat.eqb_neq in E2; contradiction].
      rewrite nth_insert_candidate_eq by exact Hlen.
      rewrite E2. tauto.
    + assert (Hlt : n < k).
      { apply Nat.eqb_neq in E. inversion Hlc; lia. }
      rewrite nth_insert_candidate_lt; [tauto|exact Hlt|exact Hlen].
  - simpl in Hfresh. assert (X <> a) by (intro Heq; subst; apply Hfresh; simpl; auto).
    unfold candidate_env_update. destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E. contradiction.
    + tauto.
  - inversion Hlc; subst. simpl in Hfresh.
    assert (Hf1 : ~ In X (fv_ty T1)).
    { intro Hin. apply Hfresh. apply in_app_iff. left; exact Hin. }
    assert (Hf2 : ~ In X (fv_ty T2)).
    { intro Hin. apply Hfresh. apply in_app_iff. right; exact Hin. }
    split.
    + intros [Hsn [HtermLC Happ]]. split; [exact Hsn|]. split; [exact HtermLC|].
      intros v HAv.
      apply (proj1 (IHT2 k rho bs X C H3 Hf2 Hlen (tm_app t v))).
      * apply Happ.
        apply (proj2 (IHT1 k rho bs X C H2 Hf1 Hlen v)); exact HAv.
    + intros [Hsn [HtermLC Happ]]. split; [exact Hsn|]. split; [exact HtermLC|].
      intros v HAv.
      apply (proj2 (IHT2 k rho bs X C H3 Hf2 Hlen (tm_app t v))).
      * apply Happ.
        apply (proj1 (IHT1 k rho bs X C H2 Hf1 Hlen v)); exact HAv.
  - inversion Hlc; subst.
    split.
    + intros [Hsn [HtermLC Hall]]. split; [exact Hsn|]. split; [exact HtermLC|].
      intros T' D HT' HD.
      rewrite <- insert_candidate_head.
      pose proof (IHT (S k) rho (D :: bs) X C H1 Hfresh ltac:(simpl; lia)
        (tm_tapp t T')) as Heq.
      apply (proj1 Heq). exact (Hall T' D HT' HD).
    + intros [Hsn [HtermLC Hall]]. split; [exact Hsn|]. split; [exact HtermLC|].
      intros T' D HT' HD.
      pose proof (Hall T' D HT' HD) as Hbody.
      rewrite <- insert_candidate_head in Hbody.
      pose proof (IHT (S k) rho (D :: bs) X C H1 Hfresh ltac:(simpl; lia)
        (tm_tapp t T')) as Heq.
      apply (proj2 Heq). exact Hbody.
Qed.

Lemma reducible_weaken : forall T k rho bs C t,
  lc_ty_at k T ->
  k <= length bs ->
  reducible rho bs T t <->
  reducible rho (insert_candidate k C bs) T t.
Proof.
  induction T; intros k rho bs C t Hlc Hlen; simpl.
  - inversion Hlc; subst.
    rewrite nth_insert_candidate_lt; [tauto|lia|exact Hlen].
  - tauto.
  - inversion Hlc; subst.
    split.
    + intros [Hsn [HtermLC Happ]]. split; [exact Hsn|]. split; [exact HtermLC|].
      intros v HAv.
      apply (proj1 (IHT2 k rho bs C (tm_app t v) H3 Hlen)).
      apply Happ.
      apply (proj2 (IHT1 k rho bs C v H2 Hlen)); exact HAv.
    + intros [Hsn [HtermLC Happ]]. split; [exact Hsn|]. split; [exact HtermLC|].
      intros v HAv.
      apply (proj2 (IHT2 k rho bs C (tm_app t v) H3 Hlen)).
      apply Happ.
      apply (proj1 (IHT1 k rho bs C v H2 Hlen)); exact HAv.
  - inversion Hlc; subst. split.
    + intros [Hsn [HtermLC Hall]]. split; [exact Hsn|]. split; [exact HtermLC|].
      intros T' D HT' HD.
      pose proof (IHT (S k) rho (D :: bs) C (tm_tapp t T') H1 ltac:(simpl; lia)) as Heq.
      rewrite insert_candidate_head in Heq.
      apply (proj1 Heq). apply Hall; assumption.
    + intros [Hsn [HtermLC Hall]]. split; [exact Hsn|]. split; [exact HtermLC|].
      intros T' D HT' HD.
      pose proof (IHT (S k) rho (D :: bs) C (tm_tapp t T') H1 ltac:(simpl; lia)) as Heq.
      pose proof (Hall T' D HT' HD) as Hbody.
      rewrite <- insert_candidate_head in Hbody.
      apply (proj2 Heq). exact Hbody.
Qed.

Lemma reducible_open_ty_rec_subst : forall T k rho bs U C,
  lc_ty_at (S k) T ->
  k <= length bs ->
  locally_closed_ty U ->
  (forall t, C t <-> reducible rho bs U t) ->
  forall t,
    reducible rho bs (open_ty_rec k U T) t <->
    reducible rho (insert_candidate k C bs) T t.
Proof.
  induction T; intros k rho bs U C Hlc Hlen HU Hrel t; simpl.
  - inversion Hlc; subst. destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n.
      rewrite nth_insert_candidate_eq by exact Hlen.
      symmetry. apply Hrel.
    + assert (Hlt : n < k).
      { apply Nat.eqb_neq in E. inversion Hlc; lia. }
      rewrite nth_insert_candidate_lt; [tauto|exact Hlt|exact Hlen].
  - tauto.
  - inversion Hlc; subst.
    split.
    + intros [Hsn [HtermLC Happ]]. split; [exact Hsn|]. split; [exact HtermLC|].
      intros v HAv.
      apply (proj1 (IHT2 k rho bs U C H3 Hlen HU Hrel (tm_app t v))).
      apply Happ.
      apply (proj2 (IHT1 k rho bs U C H2 Hlen HU Hrel v)); exact HAv.
    + intros [Hsn [HtermLC Happ]]. split; [exact Hsn|]. split; [exact HtermLC|].
      intros v HAv.
      apply (proj2 (IHT2 k rho bs U C H3 Hlen HU Hrel (tm_app t v))).
      apply Happ.
      apply (proj1 (IHT1 k rho bs U C H2 Hlen HU Hrel v)); exact HAv.
  - inversion Hlc; subst. split.
    + intros [Hsn [HtermLC Hall]]. split; [exact Hsn|]. split; [exact HtermLC|].
      intros T' D HT' HD.
      pose proof (IHT (S k) rho (D :: bs) U C H1 ltac:(simpl; lia) HU) as Heq.
      assert (Hrel' : forall z, C z <-> reducible rho (D :: bs) U z).
      { intro z. specialize (Hrel z).
        pose proof (reducible_weaken U 0 rho bs D z HU ltac:(lia)) as Hw.
        tauto. }
      specialize (Heq Hrel' (tm_tapp t T')).
      rewrite insert_candidate_head in Heq.
      apply (proj1 Heq). apply Hall; assumption.
    + intros [Hsn [HtermLC Hall]]. split; [exact Hsn|]. split; [exact HtermLC|].
      intros T' D HT' HD.
      pose proof (IHT (S k) rho (D :: bs) U C H1 ltac:(simpl; lia) HU) as Heq.
      assert (Hrel' : forall z, C z <-> reducible rho (D :: bs) U z).
      { intro z. specialize (Hrel z).
        pose proof (reducible_weaken U 0 rho bs D z HU ltac:(lia)) as Hw.
        tauto. }
      specialize (Heq Hrel' (tm_tapp t T')).
      pose proof (Hall T' D HT' HD) as Hbody.
      rewrite <- insert_candidate_head in Hbody.
      apply (proj2 Heq). exact Hbody.
Qed.

Lemma instantiate_open_tm_rec : forall t k theta gamma u,
  term_substitution_closed gamma ->
  instantiate theta gamma (open_tm_rec k u t) =
  open_tm_rec k (instantiate theta gamma u) (instantiate theta gamma t).
Proof.
  induction t; intros k theta gamma u Hgamma; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - unfold locally_closed_tm in Hgamma.
    erewrite open_tm_rec_lc_at; [reflexivity|].
    eapply (lc_tm_at_monotone 0 0 0 k (gamma a)); [apply Hgamma|lia|lia].
  - rewrite IHt by assumption. reflexivity.
  - rewrite IHt1, IHt2 by assumption. reflexivity.
  - rewrite IHt by assumption. reflexivity.
  - rewrite IHt by assumption. reflexivity.
Qed.

Lemma instantiate_open_tm : forall t theta gamma u,
  term_substitution_closed gamma ->
  instantiate theta gamma (open_tm t u) =
  open_tm (instantiate theta gamma t) (instantiate theta gamma u).
Proof. intros; apply instantiate_open_tm_rec; assumption. Qed.

Lemma open_ty_rec_closed : forall k U,
  locally_closed_ty U -> open_ty_rec k U U = U.
Proof.
  intros k U HU. eapply open_ty_rec_lc_at.
  eapply lc_ty_at_monotone; [exact HU|lia].
Qed.

Lemma instantiate_ty_open_ty_rec : forall T k theta X U,
  type_substitution_closed theta ->
  locally_closed_ty U ->
  instantiate_ty (type_subst_update theta X U)
    (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k U (instantiate_ty (type_subst_update theta X U) T).
Proof.
  induction T; intros k theta X U Htheta HU; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + unfold type_subst_update.
      destruct (Nat.eqb X X) eqn:E2.
      * simpl. rewrite E2. reflexivity.
      * apply Nat.eqb_neq in E2. contradiction.
    + reflexivity.
  - unfold type_subst_update. destruct (Nat.eqb X a) eqn:E.
    + symmetry. apply open_ty_rec_closed. exact HU.
    + erewrite open_ty_rec_lc_at; [reflexivity|].
      eapply lc_ty_at_monotone.
      * apply Htheta.
      * lia.
  - rewrite (IHT1 k theta X U Htheta HU),
      (IHT2 k theta X U Htheta HU). reflexivity.
  - rewrite (IHT (S k) theta X U Htheta HU). reflexivity.
Qed.

Lemma instantiate_ty_open_ty : forall T theta X U,
  type_substitution_closed theta ->
  locally_closed_ty U ->
  instantiate_ty (type_subst_update theta X U)
    (open_ty T (Ty_FVar X)) =
  open_ty (instantiate_ty (type_subst_update theta X U) T) U.
Proof. intros; apply instantiate_ty_open_ty_rec; assumption. Qed.

Lemma instantiate_open_tm_ty_rec : forall t k theta gamma X U,
  type_substitution_closed theta ->
  locally_closed_ty U ->
  term_substitution_closed gamma ->
  instantiate (type_subst_update theta X U) gamma
    (open_tm_ty_rec k (Ty_FVar X) t) =
  open_tm_ty_rec k U
    (instantiate (type_subst_update theta X U) gamma t).
Proof.
  induction t; intros k theta gamma X U Htheta HU Hgamma; simpl.
  - reflexivity.
  - rewrite (open_tm_ty_rec_lc_at (gamma a) k 0 U).
    + reflexivity.
    + eapply (lc_tm_at_monotone 0 0 k 0 (gamma a)); [apply Hgamma|lia|lia].
  - rewrite (instantiate_ty_open_ty_rec t k theta X U Htheta HU).
    rewrite (IHt k theta gamma X U Htheta HU Hgamma); reflexivity.
  - rewrite (IHt1 k theta gamma X U Htheta HU Hgamma),
      (IHt2 k theta gamma X U Htheta HU Hgamma); reflexivity.
  - rewrite (IHt (S k) theta gamma X U Htheta HU Hgamma); reflexivity.
  - rewrite (IHt k theta gamma X U Htheta HU Hgamma).
    rewrite (instantiate_ty_open_ty_rec t0 k theta X U Htheta HU).
    reflexivity.
Qed.

Lemma instantiate_term_update_fresh : forall t theta gamma x u,
  ~ In x (fv_tm t) ->
  instantiate theta (term_subst_update gamma x u) t =
  instantiate theta gamma t.
Proof.
  induction t; intros theta gamma x u Hfresh; simpl in *.
  - reflexivity.
  - destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply Hfresh. simpl; auto.
    + unfold term_subst_update. rewrite E. reflexivity.
  - f_equal. apply IHt. exact Hfresh.
  - assert (H1 : ~ In x (fv_tm t1)).
    { intro Hin. apply Hfresh. apply in_app_iff. left; exact Hin. }
    assert (H2 : ~ In x (fv_tm t2)).
    { intro Hin. apply Hfresh. apply in_app_iff. right; exact Hin. }
    rewrite IHt1 by exact H1. rewrite IHt2 by exact H2. reflexivity.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal. apply IHt. exact Hfresh.
Qed.

Lemma instantiate_ty_update_fresh : forall T theta X U,
  ~ In X (fv_ty T) ->
  instantiate_ty (type_subst_update theta X U) T = instantiate_ty theta T.
Proof.
  induction T; intros theta X U Hfresh; simpl in *.
  - reflexivity.
  - destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply Hfresh. simpl; auto.
    + unfold type_subst_update. rewrite E. reflexivity.
  - assert (H1 : ~ In X (fv_ty T1)).
    { intro Hin. apply Hfresh. apply in_app_iff. left; exact Hin. }
    assert (H2 : ~ In X (fv_ty T2)).
    { intro Hin. apply Hfresh. apply in_app_iff. right; exact Hin. }
    rewrite IHT1 by exact H1. rewrite IHT2 by exact H2. reflexivity.
  - f_equal. apply IHT. exact Hfresh.
Qed.

Lemma instantiate_type_update_fresh_tm : forall t theta gamma X U,
  ~ In X (ftv_tm t) ->
  instantiate (type_subst_update theta X U) gamma t =
  instantiate theta gamma t.
Proof.
  induction t; intros theta gamma X U Hfresh; simpl in *.
  - reflexivity.
  - reflexivity.
  - assert (Hty : ~ In X (fv_ty t)).
    { intro Hin. apply Hfresh. apply in_app_iff. left; exact Hin. }
    assert (Htm : ~ In X (ftv_tm t0)).
    { intro Hin. apply Hfresh. apply in_app_iff. right; exact Hin. }
    rewrite instantiate_ty_update_fresh by exact Hty.
    f_equal. apply IHt. exact Htm.
  - assert (H1 : ~ In X (ftv_tm t1)).
    { intro Hin. apply Hfresh. apply in_app_iff. left; exact Hin. }
    assert (H2 : ~ In X (ftv_tm t2)).
    { intro Hin. apply Hfresh. apply in_app_iff. right; exact Hin. }
    rewrite (IHt1 theta gamma X U H1), (IHt2 theta gamma X U H2). reflexivity.
  - f_equal. apply IHt. exact Hfresh.
  - assert (Htm : ~ In X (ftv_tm t)).
    { intro Hin. apply Hfresh. apply in_app_iff. left; exact Hin. }
    assert (Hty : ~ In X (fv_ty t0)).
    { intro Hin. apply Hfresh. apply in_app_iff. right; exact Hin. }
    rewrite (IHt theta gamma X U Htm).
    rewrite instantiate_ty_update_fresh by exact Hty.
    reflexivity.
Qed.

Definition context_reducible (rho : candidate_env) (bs : list candidate)
    (gamma : term_substitution) (Gamma : context) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    reducible rho bs T (gamma x).

Lemma candidate_env_update_ok : forall rho X C,
  candidate_env_ok rho -> candidate_ok C ->
  candidate_env_ok (candidate_env_update rho X C).
Proof.
  intros rho X C Hrho HC Y. unfold candidate_env_update.
  destruct (Nat.eqb X Y); [exact HC|apply Hrho].
Qed.

Lemma strongly_normalizing_induction : forall (P : tm -> Prop),
  (forall t, (forall u, t --> u -> P u) -> P t) ->
  forall t, strongly_normalizing t -> P t.
Proof.
  intros P HP t Hsn. induction Hsn. apply HP. exact H0.
Qed.

Lemma step_app_abs_shape : forall T body u w,
  locally_closed_tm (tm_abs T body) ->
  tm_app (tm_abs T body) u --> w ->
  (value u /\ w = open_tm body u) \/
  exists u', u --> u' /\ w = tm_app (tm_abs T body) u'.
Proof.
  intros T body u w Habs Hstep. inversion Hstep; subst.
  - left. auto.
  - exfalso. eapply value_no_step.
    + constructor. exact Habs.
    + eassumption.
  - right. eexists. split; eauto.
Qed.

Lemma reducible_abs_application : forall rho bs A B T body u,
  candidate_env_ok rho -> Forall candidate_ok bs ->
  locally_closed_tm (tm_abs T body) ->
  reducible rho bs A u ->
  (forall v, value v -> reducible rho bs A v ->
     reducible rho bs B (open_tm body v)) ->
  reducible rho bs B (tm_app (tm_abs T body) u).
Proof.
  intros rho bs A B T body u Hrho Hbs Habs HAu Hbody.
  pose proof (reducible_sn rho bs A u Hrho Hbs HAu) as Hsn.
  pose proof (reducible_lc rho bs A u Hrho Hbs HAu) as Hulc.
  pose proof (reducible_candidate_ok B rho bs Hrho Hbs) as HokB.
  pose proof (reducible_candidate_ok A rho bs Hrho Hbs) as HokA.
  apply (strongly_normalizing_induction
    (fun q => reducible rho bs A q ->
       reducible rho bs B (tm_app (tm_abs T body) q))).
  - intros q IH Hq.
    pose proof (reducible_lc rho bs A q Hrho Hbs Hq) as Hqlc.
    destruct (lc_value_or_not q Hqlc) as [Hv|Hnv].
    + pose proof (Hbody q Hv Hq) as Hbeta.
      destruct HokB as [_ [_ [Hback _]]].
      eapply Hback.
      * apply ST_AppAbs; assumption.
      * exact Hbeta.
    + destruct HokB as [_ [_ [_ [_ Hsat]]]].
      apply Hsat.
      * apply lc_tm_app; assumption.
      * intro Hval. inversion Hval.
      * intros w Hstep.
        destruct (step_app_abs_shape T body q w Habs Hstep)
          as [[Hval _]|[q' [Hqstep Heq]]].
        -- contradiction.
        -- subst w.
           eapply IH.
           ++ exact Hqstep.
           ++ destruct HokA as [_ [_ [_ [HforwardA _]]]].
              exact (HforwardA q q' Hqstep Hq).
  - exact Hsn.
  - exact HAu.
Qed.

Lemma context_reducible_update : forall rho bs gamma Gamma x A v,
  context_reducible rho bs gamma Gamma ->
  reducible rho bs A v ->
  context_reducible rho bs (term_subst_update gamma x v) (update Gamma x A).
Proof.
  intros rho bs gamma Gamma x A v Hctx Hv y T Hlookup.
  unfold update in Hlookup. simpl in Hlookup.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y.
    inversion Hlookup; subst T.
    unfold term_subst_update. rewrite Nat.eqb_refl. exact Hv.
  - apply Nat.eqb_neq in E.
    specialize (Hctx y T Hlookup).
    unfold term_subst_update. destruct (Nat.eqb x y) eqn:E'.
    + apply Nat.eqb_eq in E'. exfalso. apply E. symmetry. exact E'.
    + exact Hctx.
Qed.

Lemma lookup_context_fv : forall Gamma x T,
  lookup_context x Gamma = Some T ->
  forall X, In X (fv_ty T) -> In X (ftv_context Gamma).
Proof.
  induction Gamma as [|[y U] Gamma IH]; intros x T Hlookup X HX; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + inversion Hlookup; subst. apply in_or_app. left. exact HX.
    + apply in_or_app. right. eapply IH; eauto.
Qed.

Lemma reducible_env_update_fresh : forall T rho bs X C,
  ~ In X (fv_ty T) ->
  forall t,
    reducible (candidate_env_update rho X C) bs T t <->
    reducible rho bs T t.
Proof.
  induction T; intros rho bs X C Hfresh t; simpl in *.
  - tauto.
  - simpl in Hfresh. assert (X <> a) by (intro Heq; subst; apply Hfresh; simpl; auto).
    unfold candidate_env_update. destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E. contradiction.
    + tauto.
  - assert (H1 : ~ In X (fv_ty T1)).
    { intro Hin. apply Hfresh. apply in_app_iff. left; exact Hin. }
    assert (H2 : ~ In X (fv_ty T2)).
    { intro Hin. apply Hfresh. apply in_app_iff. right; exact Hin. }
    specialize (IHT1 rho bs X C H1).
    specialize (IHT2 rho bs X C H2).
    simpl. split.
    + intros [Hs [Hl Happ]]. split; [exact Hs|]. split; [exact Hl|].
      intros v Hv. apply (proj1 (IHT2 (tm_app t v))).
      apply Happ. apply (proj2 (IHT1 v)); exact Hv.
    + intros [Hs [Hl Happ]]. split; [exact Hs|]. split; [exact Hl|].
      intros v Hv. apply (proj2 (IHT2 (tm_app t v))).
      apply Happ. apply (proj1 (IHT1 v)); exact Hv.
  - simpl. split.
    + intros [Hs [Hl Hall]]. split; [exact Hs|]. split; [exact Hl|].
      intros T' D HT' HD.
      apply (proj1 (IHT rho (D :: bs) X C Hfresh (tm_tapp t T'))).
      apply Hall; assumption.
    + intros [Hs [Hl Hall]]. split; [exact Hs|]. split; [exact Hl|].
      intros T' D HT' HD.
      apply (proj2 (IHT rho (D :: bs) X C Hfresh (tm_tapp t T'))).
      apply Hall; assumption.
Qed.

Lemma context_reducible_env_update_fresh : forall rho bs gamma Gamma X C,
  ~ In X (ftv_context Gamma) ->
  context_reducible rho bs gamma Gamma ->
  context_reducible (candidate_env_update rho X C) bs gamma Gamma.
Proof.
  intros rho bs gamma Gamma X C Hfresh Hctx y T Hlookup.
  pose proof (reducible_env_update_fresh T rho bs X C
    ltac:(intro Hin; apply Hfresh; eapply lookup_context_fv; eauto)
    (gamma y)) as Hiff.
  apply (proj2 Hiff). apply Hctx. exact Hlookup.
Qed.

Lemma fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall rho bs theta gamma,
    candidate_env_ok rho ->
    Forall candidate_ok bs ->
    type_substitution_closed theta ->
    term_substitution_closed gamma ->
    context_reducible rho bs gamma Gamma ->
    reducible rho bs T (instantiate theta gamma t).
Proof.
  intros Delta Gamma t T Hty.
  induction Hty; intros rho bs theta gamma Hrho Hbs Htheta Hgamma Hctx.
  - simpl. eapply Hctx. exact H.
  - simpl.
    assert (Hlcabs : locally_closed_tm (tm_abs (instantiate_ty theta T1)
        (instantiate theta gamma t2))).
    { change (locally_closed_tm (instantiate theta gamma (tm_abs T1 t2))).
      eapply instantiate_lc_tm.
      - exact (has_type_lc Delta Gamma (tm_abs T1 t2)
          (Ty_Arrow T1 T2) (T_Abs L Delta Gamma T1 t2 T2 H H0)).
      - exact Htheta.
      - exact Hgamma. }
    split.
    + eapply sn_abs; exact Hlcabs.
    + split; [exact Hlcabs|].
      intros u HAu.
      apply reducible_abs_application with (rho:=rho) (bs:=bs)
        (A:=T1) (B:=T2) (T:=instantiate_ty theta T1)
        (body:=instantiate theta gamma t2).
      * exact Hrho.
      * exact Hbs.
      * exact Hlcabs.
      * exact HAu.
      * intros v Hv HAv.
        set (x := fresh (L ++ fv_tm t2)).
        assert (Hfreshall : ~ In x (L ++ fv_tm t2)).
        { unfold x. apply fresh_notin. }
        assert (HfreshL : ~ In x L).
        { intro Hin. apply Hfreshall. apply in_app_iff. left; exact Hin. }
        assert (HfreshTm : ~ In x (fv_tm t2)).
        { intro Hin. apply Hfreshall. apply in_app_iff. right; exact Hin. }
        set (gamma' := term_subst_update gamma x v).
        assert (Hgamma' : term_substitution_closed gamma').
        { unfold gamma'. eapply term_subst_update_closed; eauto using value_regular. }
        assert (Hctx' : context_reducible rho bs gamma' (update Gamma x T1)).
        { unfold gamma'. eapply context_reducible_update; eauto. }
        pose proof (H1 x HfreshL rho bs theta gamma'
          Hrho Hbs Htheta Hgamma' Hctx') as Hbody.
        unfold gamma' in Hbody.
        rewrite instantiate_open_tm in Hbody by exact Hgamma'.
        rewrite instantiate_term_update_fresh in Hbody by exact HfreshTm.
        simpl in Hbody.
        unfold term_subst_update in Hbody.
        rewrite Nat.eqb_refl in Hbody.
        exact Hbody.
  - simpl.
    pose proof (IHHty1 rho bs theta gamma Hrho Hbs Htheta Hgamma Hctx) as HF.
    pose proof (IHHty2 rho bs theta gamma Hrho Hbs Htheta Hgamma Hctx) as HA.
    simpl in HF.
    destruct HF as [_ [_ Happ]].
    apply Happ. exact HA.
  - simpl.
    assert (HlcTabs : locally_closed_tm (tm_tabs (instantiate theta gamma t))).
    { change (locally_closed_tm (instantiate theta gamma (tm_tabs t))).
      eapply instantiate_lc_tm.
      - exact (has_type_lc Delta Gamma (tm_tabs t) (Ty_All T)
          (T_TAbs L Delta Gamma t T H)).
      - exact Htheta.
      - exact Hgamma. }
    split.
    + eapply sn_tabs. exact HlcTabs.
    + split; [exact HlcTabs|].
      intros U C HU HC.
      set (X := fresh (L ++ ftv_tm t ++ fv_ty T ++ ftv_context Gamma)).
      assert (HXall : ~ In X (L ++ ftv_tm t ++ fv_ty T ++ ftv_context Gamma)).
      { unfold X. apply fresh_notin. }
      assert (HXL : ~ In X L).
      { intro Hin. apply HXall. apply in_app_iff. left. exact Hin. }
      assert (HXftv : ~ In X (ftv_tm t)).
      { intro Hin. apply HXall. apply in_app_iff. right.
        apply in_app_iff. left. exact Hin. }
      assert (HXty : ~ In X (fv_ty T)).
      { intro Hin. apply HXall. apply in_app_iff. right.
        apply in_app_iff. right. apply in_app_iff. left. exact Hin. }
      assert (HXctx : ~ In X (ftv_context Gamma)).
      { intro Hin. apply HXall. apply in_app_iff. right.
        apply in_app_iff. right. apply in_app_iff. right. exact Hin. }
      set (theta' := type_subst_update theta X U).
      set (rho' := candidate_env_update rho X C).
      assert (Htheta' : type_substitution_closed theta').
      { unfold theta'. eapply type_subst_update_closed; eauto. }
      assert (Hrho' : candidate_env_ok rho').
      { unfold rho'. eapply candidate_env_update_ok; eauto. }
      assert (Hctx' : context_reducible rho' bs gamma Gamma).
      { unfold rho'. eapply context_reducible_env_update_fresh; eauto. }
      pose proof (H0 X HXL rho' bs theta' gamma
        Hrho' Hbs Htheta' Hgamma Hctx') as Hbody.
      unfold theta', rho' in Hbody.
      unfold open_tm_ty in Hbody.
      rewrite instantiate_open_tm_ty_rec in Hbody by assumption.
      rewrite instantiate_type_update_fresh_tm in Hbody by exact HXftv.
      pose proof (has_type_type_lc _ _ _ _ (T_TAbs L Delta Gamma t T H)) as Halllc.
      unfold locally_closed_ty in Halllc. inversion Halllc; subst.
      pose proof (reducible_open_ty_rec_sem T 0 rho bs X C H3 HXty ltac:(lia)
        (open_tm_ty (instantiate theta gamma t) U)) as Hsem.
      assert (HredBody : reducible rho (C :: bs) T
        (open_tm_ty (instantiate theta gamma t) U)).
      { apply (proj1 Hsem). exact Hbody. }
      pose proof (reducible_candidate_ok T rho (C :: bs) Hrho
        ltac:(constructor; assumption)) as HokT.
      destruct HokT as [_ [_ [Hback _]]].
      eapply Hback.
      * apply ST_TAppTabs; assumption.
      * exact HredBody.
  - simpl.
    pose proof (IHHty rho bs theta gamma Hrho Hbs Htheta Hgamma Hctx) as Hallred.
    destruct Hallred as [_ [_ Hall]].
    pose proof (wf_ty_lc _ _ H) as HU.
    pose proof (instantiate_ty_lc_at U 0 theta HU Htheta) as HU'.
    set (C := reducible rho bs U).
    pose proof (reducible_candidate_ok U rho bs Hrho Hbs) as HC.
    pose proof (has_type_type_lc Delta Gamma t (Ty_All T) Hty) as Htype.
    unfold locally_closed_ty in Htype. inversion Htype; subst.
    pose proof (Hall (instantiate_ty theta U) C HU' HC) as Hbody.
    pose proof (reducible_open_ty_rec_subst T 0 rho bs
      U C H2 ltac:(lia) HU ltac:(intro z; unfold C; tauto)
      (tm_tapp (instantiate theta gamma t) (instantiate_ty theta U))) as Hsem.
    apply (proj2 Hsem). exact Hbody.
Qed.

Lemma instantiate_ty_identity : forall T,
  instantiate_ty identity_type_substitution T = T.
Proof.
  induction T; simpl; try rewrite IHT1; try rewrite IHT2; try rewrite IHT;
    reflexivity.
Qed.

Lemma instantiate_identity : forall t,
  instantiate identity_type_substitution identity_term_substitution t = t.
Proof.
  induction t; simpl; try rewrite instantiate_ty_identity;
    try rewrite IHt1; try rewrite IHt2; try rewrite IHt; reflexivity.
Qed.

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  intros t T Hty.
  set (rho := fun _ : atom => candidate_top).
  pose proof (fundamental [] [] t T Hty rho [] identity_type_substitution
    identity_term_substitution
    ltac:(intro X; apply candidate_top_ok)
    (Forall_nil _)
    identity_type_substitution_closed
    identity_term_substitution_closed
    ltac:(intros x S Hlookup; discriminate)) as Hred.
  rewrite instantiate_identity in Hred.
  eapply reducible_sn.
  - intros X. apply candidate_top_ok.
  - constructor.
  - exact Hred.
Qed.

End SystemFNormalizationNoneEasyTask.
