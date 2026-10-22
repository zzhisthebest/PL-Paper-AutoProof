(** System F parametricity benchmark, Easy variant.
    Features: none. *)

From Stdlib Require Import Arith.PeanoNat Arith.Wf_nat Lists.List Lia.
Import ListNotations.

Module SystemFParametricityNoneEasyTask.

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

Inductive evaluates : tm -> tm -> Prop :=
  | EvalValue : forall v, value v -> evaluates v v
  | EvalApp : forall f arg U body v result,
      evaluates f (tm_abs U body) -> evaluates arg v ->
      evaluates (open_tm body v) result -> evaluates (tm_app f arg) result
  | EvalTApp : forall f U body result,
      evaluates f (tm_tabs body) -> locally_closed_ty U ->
      evaluates (open_tm_ty body U) result -> evaluates (tm_tapp f U) result.

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

(* The value part of the relational interpretation.  Type variables are
   interpreted by a pair of closed types and an arbitrary relation on their
   values. *)
Definition value_relation := tm -> tm -> Prop.
Definition evaluated_by (R : value_relation) (t u : tm) : Prop :=
  exists v w, t -->* v /\ u -->* w /\ value v /\ value w /\ R v w.

Record type_relation_entry : Type := mk_type_relation_entry {
  tr_left : ty;
  tr_right : ty;
  tr_values : value_relation
}.
Definition relation_env := list type_relation_entry.
Definition default_relation_entry : type_relation_entry :=
  mk_type_relation_entry (Ty_FVar 0) (Ty_FVar 0) (fun _ _ => False).

Fixpoint logical_relation (xi : atom -> type_relation_entry)
    (rho : relation_env) (T : ty) : value_relation :=
  match T with
  | Ty_BVar n => tr_values (nth n rho default_relation_entry)
  | Ty_FVar X => tr_values (xi X)
  | Ty_Arrow A B =>
      fun f g => value f /\ value g /\
        forall a b, value a -> value b -> logical_relation xi rho A a b ->
          evaluated_by (logical_relation xi rho B) (tm_app f a) (tm_app g b)
  | Ty_All B =>
      fun f g => value f /\ value g /\
        exists fbody gbody,
          f = tm_tabs fbody /\ g = tm_tabs gbody /\
          forall A C R,
            locally_closed_ty A -> locally_closed_ty C ->
            (forall a b, R a b -> value a /\ value b) ->
            evaluated_by (logical_relation xi (mk_type_relation_entry A C R :: rho) B)
              (tm_tapp f A) (tm_tapp g C)
  end.

Definition relation_env_update (xi : atom -> type_relation_entry)
    (X : atom) (e : type_relation_entry) : atom -> type_relation_entry :=
  fun Y => if Nat.eqb X Y then e else xi Y.

Definition related_context_substitutions (xi : atom -> type_relation_entry)
    (Gamma : context) (g1 g2 : term_substitution) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    evaluated_by (logical_relation xi [] T) (g1 x) (g2 x).

Definition matching_type_substitutions (xi : atom -> type_relation_entry)
    (theta1 theta2 : type_substitution) : Prop :=
  forall X, theta1 X = tr_left (xi X) /\ theta2 X = tr_right (xi X).

Definition relation_entry_good (e : type_relation_entry) : Prop :=
  locally_closed_ty (tr_left e) /\ locally_closed_ty (tr_right e) /\
  forall a b, tr_values e a b -> value a /\ value b.
Definition relation_environment_good (xi : atom -> type_relation_entry) : Prop :=
  forall X, relation_entry_good (xi X).
Definition bound_environment_good (rho : relation_env) : Prop :=
  forall e, In e rho -> relation_entry_good e.

Lemma relation_env_update_good : forall xi X e,
  relation_environment_good xi -> relation_entry_good e ->
  relation_environment_good (relation_env_update xi X e).
Proof.
  intros xi X e Hxi He Y. unfold relation_env_update.
  destruct (Nat.eqb X Y); [exact He|apply Hxi].
Qed.

Lemma logical_relation_good : forall T xi rho,
  lc_ty_at (length rho) T ->
  relation_environment_good xi -> bound_environment_good rho ->
  forall a b, logical_relation xi rho T a b -> value a /\ value b.
Proof.
  intros T xi rho Hlc Hxi Hr a b Hrel.
  destruct T; simpl in Hrel.
  - inversion Hlc; subst.
    pose proof (nth_In rho default_relation_entry H1) as Hmem.
    exact (proj2 (proj2 (Hr (nth n rho default_relation_entry) Hmem)) a b Hrel).
  - exact (proj2 (proj2 (Hxi a0)) a b Hrel).
  - tauto.
  - tauto.
Qed.

Lemma nth_app_last : forall (A : Type) (l : list A) e d n,
  nth n (l ++ [e]) d =
  if Nat.eqb n (length l) then e else nth n l d.
Proof.
  intros A l. induction l as [|x l IH]; intros e d [|n]; simpl.
  - reflexivity.
  - destruct n; reflexivity.
  - reflexivity.
  - rewrite IH. destruct (Nat.eqb n (length l)); reflexivity.
Qed.

Lemma evaluated_by_morphism : forall R S t u,
  (forall a b, R a b <-> S a b) ->
  evaluated_by R t u -> evaluated_by S t u.
Proof.
  intros R S t u Heq [a [b [Hta [Hub [Hva [Hvb HR]]]]]].
  exists a,b. repeat split; try assumption. apply Heq. exact HR.
Qed.

Lemma relation_env_update_other : forall xi X e Y,
  X <> Y -> relation_env_update xi X e Y = xi Y.
Proof.
  intros. unfold relation_env_update. apply Nat.eqb_neq in H. now rewrite H.
Qed.

Lemma logical_relation_open : forall T k rho xi X e,
  length rho = k -> ~ In X (fv_ty T) ->
  forall a b,
    logical_relation (relation_env_update xi X e) rho
      (open_ty_rec k (Ty_FVar X) T) a b <->
    logical_relation xi (rho ++ [e]) T a b.
Proof.
  intros T k rho xi X e Hlen Hfresh a b.
  revert k rho xi X e Hlen Hfresh a b.
  induction T; intros k rho xi X e Hlen Hfresh u1 u2; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n.
      unfold relation_env_update. cbn [logical_relation].
      rewrite Nat.eqb_refl.
      rewrite nth_app_last, Hlen, Nat.eqb_refl. tauto.
    + assert (En : Nat.eqb n (length rho) = false).
      { apply Nat.eqb_neq. intro Heq. rewrite Hlen in Heq. apply Nat.eqb_neq in E. lia. }
      rewrite nth_app_last, En. split; intro H; exact H.
  - assert (Hneq : X <> a).
    { intro Heq. apply Hfresh. simpl. left. symmetry. exact Heq. }
    rewrite relation_env_update_other by congruence. tauto.
  - assert (HA : ~ In X (fv_ty T1)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (HB : ~ In X (fv_ty T2)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    specialize (IHT1 k rho xi X e Hlen HA).
    specialize (IHT2 k rho xi X e Hlen HB).
    split.
    + intros [Hfv [Hgv Hfun]]. repeat split; try assumption.
      intros x y Hx Hy Hxy. eapply evaluated_by_morphism.
      * exact IHT2.
      * apply Hfun; [exact Hx|exact Hy|apply IHT1; exact Hxy].
    + intros [Hfv [Hgv Hfun]]. repeat split; try assumption.
      intros x y Hx Hy Hxy. eapply evaluated_by_morphism.
      * intros p q. apply iff_sym. apply IHT2.
      * apply Hfun; [exact Hx|exact Hy|apply IHT1; exact Hxy].
  - assert (HB : ~ In X (fv_ty T)).
    { exact Hfresh. }
    split.
    + intros [Hfv [Hgv [body1 [body2 [Hfb [Hgb Hforall]]]]]].
      subst u1. subst u2.
      repeat split; try assumption. exists body1, body2. repeat split; try assumption.
      intros A C R HA HC HRgood.
      specialize (Hforall A C R HA HC HRgood) as Hrun.
      apply (evaluated_by_morphism
        (logical_relation (relation_env_update xi X e)
          (mk_type_relation_entry A C R :: rho)
          (open_ty_rec (S k) (Ty_FVar X) T))
        (logical_relation xi ((mk_type_relation_entry A C R :: rho) ++ [e]) T)
        (tm_tapp (tm_tabs body1) A) (tm_tapp (tm_tabs body2) C)).
      * apply IHT with (k := S k) (rho := mk_type_relation_entry A C R :: rho)
          (xi := xi) (X := X) (e := e).
        -- simpl. lia.
        -- exact HB.
      * exact Hrun.
    + intros [Hfv [Hgv [body1 [body2 [Hfb [Hgb Hforall]]]]]].
      subst u1. subst u2.
      repeat split; try assumption. exists body1, body2. repeat split; try assumption.
      intros A C R HA HC HRgood.
      specialize (Hforall A C R HA HC HRgood) as Hrun.
      apply (evaluated_by_morphism
        (logical_relation xi ((mk_type_relation_entry A C R :: rho) ++ [e]) T)
        (logical_relation (relation_env_update xi X e)
          (mk_type_relation_entry A C R :: rho)
          (open_ty_rec (S k) (Ty_FVar X) T))
        (tm_tapp (tm_tabs body1) A) (tm_tapp (tm_tabs body2) C)).
      * intro p. intro q. apply iff_sym.
        apply IHT with (k := S k) (rho := mk_type_relation_entry A C R :: rho)
          (xi := xi) (X := X) (e := e).
        -- simpl. lia.
        -- exact HB.
      * exact Hrun.
Qed.

Lemma logical_relation_fresh_update : forall T rho xi X e,
  ~ In X (fv_ty T) -> forall a b,
    logical_relation (relation_env_update xi X e) rho T a b <->
    logical_relation xi rho T a b.
Proof.
  intros T rho xi X e Hfresh a b.
  revert rho xi X e Hfresh a b.
  induction T; intros rho xi X e Hfresh u1 u2; simpl.
  - tauto.
  - assert (Hneq : X <> a).
    { intro Heq. apply Hfresh. simpl. left. symmetry. exact Heq. }
    rewrite relation_env_update_other by congruence. tauto.
  - assert (HA : ~ In X (fv_ty T1)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (HB : ~ In X (fv_ty T2)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    specialize (IHT1 rho xi X e HA).
    specialize (IHT2 rho xi X e HB).
    split.
    + intros [Hfv [Hgv Hfun]]. repeat split; try assumption.
      intros x y Hx Hy Hxy. eapply evaluated_by_morphism.
      * exact IHT2.
      * apply Hfun; [exact Hx|exact Hy|apply IHT1; exact Hxy].
    + intros [Hfv [Hgv Hfun]]. repeat split; try assumption.
      intros x y Hx Hy Hxy. eapply evaluated_by_morphism.
      * intros p q. apply iff_sym. apply IHT2.
      * apply Hfun; [exact Hx|exact Hy|apply IHT1; exact Hxy].
  - 
    split.
    + intros [Hfv [Hgv [body1 [body2 [Hfb [Hgb Hforall]]]]]].
      subst u1. subst u2. repeat split; try assumption. exists body1, body2.
      repeat split; try assumption. intros A C R HA HC HRgood.
      specialize (IHT (mk_type_relation_entry A C R :: rho) xi X e Hfresh).
      specialize (Hforall A C R HA HC HRgood).
      eapply evaluated_by_morphism.
      * apply IHT.
      * exact Hforall.
    + intros [Hfv [Hgv [body1 [body2 [Hfb [Hgb Hforall]]]]]].
      subst u1. subst u2. repeat split; try assumption. exists body1, body2.
      repeat split; try assumption. intros A C R HA HC HRgood.
      specialize (IHT (mk_type_relation_entry A C R :: rho) xi X e Hfresh).
      specialize (Hforall A C R HA HC HRgood).
      eapply evaluated_by_morphism.
      * intros p q. apply iff_sym. apply IHT.
      * exact Hforall.
Qed.

Definition bound_env_prefix (rho1 rho2 : relation_env) (k : nat) : Prop :=
  forall n, n < k ->
    nth n rho1 default_relation_entry = nth n rho2 default_relation_entry.

Lemma bound_env_prefix_extend : forall rho1 rho2 k e,
  bound_env_prefix rho1 rho2 k ->
  bound_env_prefix (e :: rho1) (e :: rho2) (S k).
Proof.
  intros rho1 rho2 k e H n Hn. destruct n.
  - reflexivity.
  - simpl. apply H. lia.
Qed.

Lemma logical_relation_bound_irrelevant : forall T k rho1 rho2 xi,
  lc_ty_at k T -> bound_env_prefix rho1 rho2 k ->
  forall a b,
    logical_relation xi rho1 T a b <-> logical_relation xi rho2 T a b.
Proof.
  intros T k rho1 rho2 xi Hlc Hpre a b.
  revert k rho1 rho2 xi Hlc Hpre a b.
  induction T; intros k rho1 rho2 xi Hlc Hpre u1 u2; simpl.
  - inversion Hlc; subst. rewrite Hpre by assumption. tauto.
  - tauto.
  - inversion Hlc; subst.
    specialize (IHT1 k rho1 rho2 xi H2 Hpre).
    specialize (IHT2 k rho1 rho2 xi H3 Hpre).
    split.
    + intros [Hfv [Hgv Hfun]]. repeat split; try assumption.
      intros x y Hx Hy Hxy. eapply evaluated_by_morphism.
      * exact IHT2.
      * apply Hfun; [exact Hx|exact Hy|apply IHT1; exact Hxy].
    + intros [Hfv [Hgv Hfun]]. repeat split; try assumption.
      intros x y Hx Hy Hxy. eapply evaluated_by_morphism.
      * intros p q. apply iff_sym. apply IHT2.
      * apply Hfun; [exact Hx|exact Hy|apply IHT1; exact Hxy].
  - inversion Hlc; subst.
    split.
    + intros [Hfv [Hgv [body1 [body2 [Hfb [Hgb Hforall]]]]]].
      subst u1. subst u2. repeat split; try assumption. exists body1, body2.
      repeat split; try assumption. intros A C R HA HC HRgood.
      specialize (Hforall A C R HA HC HRgood).
      eapply evaluated_by_morphism.
      * apply IHT with (k := S k) (rho1 := mk_type_relation_entry A C R :: rho1)
          (rho2 := mk_type_relation_entry A C R :: rho2) (xi := xi).
        -- assumption.
        -- eapply bound_env_prefix_extend. exact Hpre.
      * exact Hforall.
    + intros [Hfv [Hgv [body1 [body2 [Hfb [Hgb Hforall]]]]]].
      subst u1. subst u2. repeat split; try assumption. exists body1, body2.
      repeat split; try assumption. intros A C R HA HC HRgood.
      specialize (Hforall A C R HA HC HRgood).
      eapply evaluated_by_morphism.
      * intros p q. apply iff_sym.
        apply IHT with (k := S k) (rho1 := mk_type_relation_entry A C R :: rho1)
          (rho2 := mk_type_relation_entry A C R :: rho2) (xi := xi).
        -- assumption.
        -- eapply bound_env_prefix_extend. exact Hpre.
      * exact Hforall.
Qed.

Lemma logical_relation_type_open : forall T k rho xi U e,
  length rho = k -> locally_closed_ty U ->
  (forall a b, tr_values e a b <-> logical_relation xi [] U a b) ->
  forall a b,
    logical_relation xi rho (open_ty_rec k U T) a b <->
    logical_relation xi (rho ++ [e]) T a b.
Proof.
  intros T k rho xi U e Hlen HU He a b.
  revert k rho xi U e Hlen HU He a b.
  induction T; intros k rho xi U e Hlen HU He u1 u2; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n.
      rewrite nth_app_last, Hlen, Nat.eqb_refl.
      pose proof (logical_relation_bound_irrelevant U 0 rho [] xi HU) as Hirr.
      assert (Hp : bound_env_prefix rho [] 0).
      { intros m Hm. lia. }
      specialize (Hirr Hp u1 u2).
      split.
      * intro Hrel. apply He. apply Hirr. exact Hrel.
      * intro Hrel. apply Hirr. apply He. exact Hrel.
    + assert (En : Nat.eqb n (length rho) = false).
      { apply Nat.eqb_neq. intro Heq. rewrite Hlen in Heq.
        apply Nat.eqb_neq in E. lia. }
      rewrite nth_app_last, En. tauto.
  - tauto.
  - specialize (IHT1 k rho xi U e Hlen HU He).
    specialize (IHT2 k rho xi U e Hlen HU He).
    split.
    + intros [Hfv [Hgv Hfun]]. repeat split; try assumption.
      intros x y Hx Hy Hxy. eapply evaluated_by_morphism.
      * exact IHT2.
      * apply Hfun; [exact Hx|exact Hy|apply IHT1; exact Hxy].
    + intros [Hfv [Hgv Hfun]]. repeat split; try assumption.
      intros x y Hx Hy Hxy. eapply evaluated_by_morphism.
      * intros p q. apply iff_sym. apply IHT2.
      * apply Hfun; [exact Hx|exact Hy|apply IHT1; exact Hxy].
  - inversion Hlen; subst.
    split.
    + intros [Hfv [Hgv [body1 [body2 [Hfb [Hgb Hforall]]]]]].
      subst u1. subst u2. repeat split; try assumption. exists body1, body2.
      repeat split; try assumption. intros A C R HA HC HRgood.
      specialize (Hforall A C R HA HC HRgood).
      eapply evaluated_by_morphism.
      * apply IHT with (k := S (length rho)) (rho := mk_type_relation_entry A C R :: rho)
          (xi := xi) (U := U) (e := e).
        -- simpl. lia.
        -- exact HU.
        -- exact He.
      * exact Hforall.
    + intros [Hfv [Hgv [body1 [body2 [Hfb [Hgb Hforall]]]]]].
      subst u1. subst u2. repeat split; try assumption. exists body1, body2.
      repeat split; try assumption. intros A C R HA HC HRgood.
      specialize (Hforall A C R HA HC HRgood).
      eapply evaluated_by_morphism.
      * intros p q. apply iff_sym.
        apply IHT with (k := S (length rho)) (rho := mk_type_relation_entry A C R :: rho)
          (xi := xi) (U := U) (e := e).
        -- simpl. lia.
        -- exact HU.
        -- exact He.
      * exact Hforall.
Qed.

Lemma evaluated_by_application : forall xi rho A B f g a b,
  evaluated_by (logical_relation xi rho (Ty_Arrow A B)) f g ->
  evaluated_by (logical_relation xi rho A) a b ->
  locally_closed_tm a -> locally_closed_tm b ->
  evaluated_by (logical_relation xi rho B)
    (tm_app f a) (tm_app g b).
Proof.
  intros xi rho A B f g a b [fv [gv [Hff [Hgg [Hfv [Hgv Hfun]]]]]]
    [av [bv [Hfa [Hgb [Hav [Hbv Hab]]]]]] Hla Hlb.
  destruct Hfun as [_ [_ Happly]].
  specialize (Happly av bv Hav Hbv Hab) as
    [out1 [out2 [H1 [H2 [Hv1 [Hv2 Hrel]]]]]].
  exists out1, out2. repeat split; try assumption.
  - eapply multi_trans.
    + eapply multi_trans.
      * eapply multi_app_left; [exact Hff|exact Hla].
      * apply multi_app_right; [exact Hfv|exact Hfa].
    + exact H1.
  - eapply multi_trans.
    + eapply multi_trans.
      * eapply multi_app_left; [exact Hgg|exact Hlb].
      * apply multi_app_right; [exact Hgv|exact Hgb].
    + exact H2.
Qed.

Lemma evaluated_by_singleton : forall v t,
  evaluated_by (fun x y => x = v /\ y = v) t t -> t -->* v.
Proof.
  intros v t [x [y [Htx [Hty [_ [_ [-> ->]]]]]]]. exact Htx.
Qed.

Fixpoint ty_size (T : ty) : nat :=
  match T with
  | Ty_BVar _ | Ty_FVar _ => 1
  | Ty_Arrow A B => S (ty_size A + ty_size B)
  | Ty_All A => S (ty_size A)
  end.

Lemma open_ty_fvar_size : forall T k X,
  ty_size (open_ty_rec k (Ty_FVar X) T) = ty_size T.
Proof.
  induction T; intros; simpl; try reflexivity.
  - destruct (Nat.eqb k n); reflexivity.
  - rewrite IHT1, IHT2. reflexivity.
  - rewrite IHT. reflexivity.
Qed.

Lemma wf_ty_locally_closed : forall Delta T,
  wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T Hwf.
  assert (Hmain : forall n, forall Delta T, ty_size T = n ->
      wf_ty Delta T -> locally_closed_ty T).
  { intro n. induction n using lt_wf_ind.
    intros Delta0 T0 Hsize Hwf0.
  inversion Hwf0; subst.
  - apply lc_ty_fvar.
  - constructor.
    + eapply (H (ty_size T1)); [simpl; lia|reflexivity|eassumption].
    + eapply (H (ty_size T2)); [simpl; lia|reflexivity|eassumption].
  - apply lc_ty_all.
    pose (X := fresh L).
    assert (Hnot : ~ In X L) by (unfold X; apply fresh_notin).
    pose proof (H0 X Hnot) as Hopened.
    assert (Hopen : ty_size (open_ty T1 (Ty_FVar X)) = ty_size T1).
    { unfold open_ty. apply open_ty_fvar_size. }
    assert (Hsmall : ty_size T1 < ty_size (Ty_All T1)).
    { simpl. lia. }
    pose proof (H (ty_size T1) Hsmall (X :: Delta0)
      (open_ty T1 (Ty_FVar X)) Hopen Hopened) as Hlc.
    eapply lc_ty_at_open_inv. exact Hlc.
  }
  eapply Hmain; eauto.
Qed.

Lemma wf_ty_empty_lc : forall T,
  wf_ty [] T -> locally_closed_ty T.
Proof. intros; eapply wf_ty_locally_closed; eauto. Qed.

Lemma identity_from_logical_relation : forall xi t U v,
  wf_ty [] U -> value v ->
  evaluated_by (logical_relation xi []
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0)))) t t ->
  tm_app (tm_tapp t U) v -->* v.
Proof.
  intros xi t U v HU Hv [f [g [Htf [Htg [Hf [Hg Hrel]]]]]].
  destruct Hrel as [_ [_ [body1 [body2 [Hf' [Hg' Hforall]]]]]].
  subst f. subst g.
  assert (Hsinggood : forall a b, (a = v /\ b = v) -> value a /\ value b).
  { intros a b [-> ->]. split; exact Hv. }
  specialize (Hforall U U (fun a b => a = v /\ b = v)
    (wf_ty_empty_lc U HU) (wf_ty_empty_lc U HU) Hsinggood).
  simpl in Hforall.
  assert (Harg : evaluated_by (fun a b => a = v /\ b = v) v v).
  { exists v, v. repeat split; try assumption; constructor. }
  pose proof (evaluated_by_application xi
    [mk_type_relation_entry U U (fun a b => a = v /\ b = v)]
    (Ty_BVar 0) (Ty_BVar 0) (tm_tapp (tm_tabs body1) U)
    (tm_tapp (tm_tabs body2) U) v v Hforall Harg
    (value_regular _ Hv) (value_regular _ Hv)) as Happ.
  destruct Happ as [out1 [out2 [Hleft [Hright [Hout1 [Hout2 Hsame]]]]]].
  destruct Hsame as [-> _].
  eapply multi_trans.
  - apply multi_app_left.
    + apply multi_tapp; [exact Htf|apply wf_ty_empty_lc; exact HU].
    + apply value_regular. exact Hv.
  - exact Hleft.
Qed.

Lemma instantiate_ty_lc_at : forall T k theta,
  lc_ty_at k T -> type_substitution_closed theta ->
  lc_ty_at k (instantiate_ty theta T).
Proof.
  intros T k theta Hlc. induction Hlc; intros Htheta; simpl.
  - constructor. assumption.
  - eapply lc_ty_at_monotone; [apply Htheta|lia].
  - constructor; [apply IHHlc1|apply IHHlc2]; assumption.
  - constructor. apply IHHlc. assumption.
Qed.

Lemma instantiate_lc_tm_at : forall t K k theta gamma,
  lc_tm_at K k t -> type_substitution_closed theta ->
  term_substitution_closed gamma ->
  lc_tm_at K k (instantiate theta gamma t).
Proof.
  intros t K k theta gamma Hlc. induction Hlc; intros Htheta Hgamma; simpl.
  - constructor. assumption.
  - eapply lc_tm_at_monotone; [apply Hgamma|lia|lia].
  - apply lc_tm_abs.
    + eapply instantiate_ty_lc_at; eauto.
    + apply IHHlc; assumption.
  - apply lc_tm_app; [apply IHHlc1|apply IHHlc2]; assumption.
  - apply lc_tm_tabs. apply IHHlc; assumption.
  - apply lc_tm_tapp.
    + apply IHHlc; assumption.
    + eapply instantiate_ty_lc_at; eauto.
Qed.

Fixpoint tm_size (t : tm) : nat :=
  match t with
  | tm_bvar _ | tm_fvar _ => 1
  | tm_abs _ t1 | tm_tabs t1 => S (tm_size t1)
  | tm_app t1 t2 => S (tm_size t1 + tm_size t2)
  | tm_tapp t1 _ => S (tm_size t1)
  end.

Lemma open_tm_fvar_size : forall t k x,
  tm_size (open_tm_rec k (tm_fvar x) t) = tm_size t.
Proof.
  induction t; intros; simpl; try reflexivity.
  - destruct (Nat.eqb k n); simpl; reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
Qed.

Lemma open_tm_ty_size : forall t k U,
  tm_size (open_tm_ty_rec k U t) = tm_size t.
Proof.
  induction t; intros; simpl; try reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
Qed.

Lemma has_type_locally_closed : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T Hty.
  assert (Hmain : forall n Delta Gamma t T,
      tm_size t = n -> has_type Delta Gamma t T -> locally_closed_tm t).
  { intro n. induction n using lt_wf_ind.
    intros Delta0 Gamma0 t0 T0 Hsize Htyping.
    inversion Htyping; subst.
    - constructor.
    - assert (Hfreshnot : ~ In (fresh (L ++ dom_context Gamma0))
        (L ++ dom_context Gamma0)).
      { apply fresh_notin. }
      assert (HxnotL : ~ In (fresh (L ++ dom_context Gamma0)) L).
      { intro Hin. apply Hfreshnot. apply in_or_app. left. exact Hin. }
      pose proof (H1 (fresh (L ++ dom_context Gamma0)) HxnotL) as Hbody.
      assert (Hsmall : tm_size t2 < tm_size (tm_abs T1 t2)).
      { simpl. lia. }
      assert (Hbodylc : locally_closed_tm (open_tm t2 (tm_fvar (fresh (L ++ dom_context Gamma0))))).
      { eapply H with (m := tm_size t2).
        - exact Hsmall.
        - unfold open_tm. apply open_tm_fvar_size.
        - exact Hbody. }
      apply lc_tm_abs.
      + eapply wf_ty_locally_closed. eassumption.
      + eapply lc_tm_at_open_tm_inv. exact Hbodylc.
    - apply lc_tm_app.
      + eapply H with (m := tm_size t1); [simpl; lia|reflexivity|eassumption].
      + eapply H with (m := tm_size t2); [simpl; lia|reflexivity|eassumption].
    - assert (HXfreshnot : ~ In (fresh (L ++ ftv_tm t1 ++ ftv_context Gamma0))
        (L ++ ftv_tm t1 ++ ftv_context Gamma0)).
      { apply fresh_notin. }
      assert (HXnotL : ~ In (fresh (L ++ ftv_tm t1 ++ ftv_context Gamma0)) L).
      { intro Hin. apply HXfreshnot. apply in_or_app. left. exact Hin. }
      pose proof (H0 (fresh (L ++ ftv_tm t1 ++ ftv_context Gamma0)) HXnotL) as Hbody.
      assert (Hsmall : tm_size t1 < tm_size (tm_tabs t1)).
      { simpl. lia. }
      assert (Hbodylc : locally_closed_tm
        (open_tm_ty t1 (Ty_FVar (fresh (L ++ ftv_tm t1 ++ ftv_context Gamma0))))).
      { eapply H with (m := tm_size t1).
        - exact Hsmall.
        - unfold open_tm_ty. apply open_tm_ty_size.
        - exact Hbody. }
      apply lc_tm_tabs. eapply lc_tm_at_open_ty_inv. exact Hbodylc.
    - apply lc_tm_tapp.
      + eapply H with (m := tm_size t1).
        * simpl. apply Nat.lt_succ_diag_r.
        * reflexivity.
        * exact H0.
      + eapply wf_ty_locally_closed. eassumption.
  }
  eapply Hmain; eauto.
Qed.

Lemma instantiate_ty_open_update : forall T k theta X A,
  type_substitution_closed theta -> locally_closed_ty A ->
  instantiate_ty (type_subst_update theta X A)
      (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k A (instantiate_ty (type_subst_update theta X A) T).
Proof.
  intros T k theta X A Htheta HA. revert k.
  induction T; intros k; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + change (type_subst_update theta X A X = A).
      unfold type_subst_update. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - unfold type_subst_update. destruct (Nat.eqb X a) eqn:E; simpl.
    + rewrite open_ty_rec_lc_at.
      * reflexivity.
      * eapply lc_ty_at_monotone; [exact HA|lia].
    + rewrite open_ty_rec_lc_at.
      * reflexivity.
      * eapply lc_ty_at_monotone; [apply Htheta|lia].
  - rewrite IHT1, IHT2; try assumption. reflexivity.
  - rewrite IHT; try assumption. reflexivity.
Qed.

Lemma instantiate_open_tm_ty_rec : forall t k theta gamma X A,
  type_substitution_closed theta -> locally_closed_ty A ->
  term_substitution_closed gamma ->
  instantiate (type_subst_update theta X A) gamma
      (open_tm_ty_rec k (Ty_FVar X) t) =
  open_tm_ty_rec k A
      (instantiate (type_subst_update theta X A) gamma t).
Proof.
  intros t. induction t; intros k theta gamma X A Htheta HA Hgamma; simpl.
  - reflexivity.
  - rewrite (open_tm_ty_rec_lc_at (gamma a) k 0 A).
    + reflexivity.
    + eapply lc_tm_at_monotone; [apply Hgamma|lia|lia].
  - rewrite instantiate_ty_open_update by assumption.
    rewrite IHt by assumption. reflexivity.
  - rewrite IHt1, IHt2; try assumption. reflexivity.
  - rewrite IHt by assumption. reflexivity.
  - rewrite IHt by assumption.
    rewrite instantiate_ty_open_update by assumption. reflexivity.
Qed.

Lemma instantiate_open_tm_rec : forall t k theta gamma x,
  term_substitution_closed gamma ->
  instantiate theta gamma (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k (gamma x) (instantiate theta gamma t).
Proof.
  induction t; intros k theta gamma x Hgamma; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - rewrite (open_tm_rec_lc_at (gamma a) 0 k (gamma x)).
    + reflexivity.
    + eapply lc_tm_at_monotone; [apply Hgamma|lia|lia].
  - rewrite IHt with (gamma := gamma); [reflexivity|exact Hgamma].
  - rewrite IHt1 with (gamma := gamma), IHt2 with (gamma := gamma).
    + reflexivity.
    + exact Hgamma.
    + exact Hgamma.
  - rewrite IHt with (gamma := gamma); [reflexivity|exact Hgamma].
  - rewrite IHt with (gamma := gamma); [reflexivity|exact Hgamma].
Qed.

Lemma lookup_context_ftv : forall Gamma x T,
  lookup_context x Gamma = Some T ->
  forall X, In X (fv_ty T) -> In X (ftv_context Gamma).
Proof.
  induction Gamma as [|[y S] Gamma IH]; intros x T Hlook X Hfv; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + inversion Hlook; subst. apply in_or_app. left. exact Hfv.
    + apply in_or_app. right. eapply IH; eauto.
Qed.

Lemma related_context_type_update : forall xi X e Gamma g1 g2,
  ~ In X (ftv_context Gamma) ->
  related_context_substitutions xi Gamma g1 g2 ->
  related_context_substitutions (relation_env_update xi X e) Gamma g1 g2.
Proof.
  intros xi X e Gamma g1 g2 Hfresh Hctx x T Hlook.
  specialize (Hctx x T Hlook).
  assert (Htyfresh : ~ In X (fv_ty T)).
  { intro Hin. apply Hfresh. eapply lookup_context_ftv; eauto. }
  eapply evaluated_by_morphism.
  - intros a b. apply iff_sym. apply logical_relation_fresh_update. exact Htyfresh.
  - exact Hctx.
Qed.

Lemma related_context_term_update : forall xi Gamma g1 g2 x T a b,
  ~ In x (dom_context Gamma) ->
  related_context_substitutions xi Gamma g1 g2 ->
  evaluated_by (logical_relation xi [] T) a b ->
  related_context_substitutions xi (update Gamma x T)
    (term_subst_update g1 x a) (term_subst_update g2 x b).
Proof.
  intros xi Gamma g1 g2 x T a b Hfresh Hctx Hnew y S Hlook.
  destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. subst y.
    rewrite lookup_context_update_eq in Hlook. inversion Hlook; subst S.
    unfold term_subst_update. rewrite Nat.eqb_refl. exact Hnew.
  - assert (Hxy : x <> y) by (apply Nat.eqb_neq; exact E).
    rewrite lookup_context_update_neq in Hlook by exact Hxy.
    unfold term_subst_update. rewrite E.
    eapply Hctx. exact Hlook.
Qed.

Lemma type_subst_update_matching : forall xi X e theta1 theta2 A C,
  matching_type_substitutions xi theta1 theta2 ->
  tr_left e = A -> tr_right e = C ->
  matching_type_substitutions (relation_env_update xi X e)
    (type_subst_update theta1 X A) (type_subst_update theta2 X C).
Proof.
  intros xi X e theta1 theta2 A C Hmatch Hleft Hright Y.
  unfold matching_type_substitutions, relation_env_update,
    type_subst_update in *.
  specialize (Hmatch Y).
  destruct (Nat.eqb X Y) eqn:E.
  - apply Nat.eqb_eq in E. subst Y. split; symmetry; assumption.
  - exact Hmatch.
Qed.

Lemma not_in_app : forall (A : Type) (x : A) l1 l2,
  ~ In x (l1 ++ l2) -> ~ In x l1 /\ ~ In x l2.
Proof.
  intros A x l1 l2 H. split; intro Hin; apply H; apply in_or_app; auto.
Qed.

Lemma instantiate_ty_update_fresh : forall T theta X A,
  ~ In X (fv_ty T) ->
  instantiate_ty (type_subst_update theta X A) T = instantiate_ty theta T.
Proof.
  induction T; intros theta X A Hfresh; simpl.
  - reflexivity.
  - simpl in Hfresh. assert (Hneq : X <> a).
    { intro Heq. apply Hfresh. simpl. left. symmetry. exact Heq. }
    assert (E : Nat.eqb X a = false) by (apply Nat.eqb_neq; exact Hneq).
    unfold type_subst_update. rewrite E. reflexivity.
  - apply not_in_app in Hfresh as [H1 H2].
    rewrite IHT1 with (theta := theta) (X := X) (A := A),
      IHT2 with (theta := theta) (X := X) (A := A); try assumption.
    reflexivity.
  - rewrite IHT with (theta := theta) (X := X) (A := A) by exact Hfresh.
    reflexivity.
Qed.

Lemma instantiate_update_fresh_type : forall t theta gamma X A,
  ~ In X (ftv_tm t) ->
  instantiate (type_subst_update theta X A) gamma t =
  instantiate theta gamma t.
Proof.
  induction t; intros theta gamma X A Hfresh; simpl in *; try reflexivity.
  - apply not_in_app in Hfresh as [HT Hbody].
    rewrite instantiate_ty_update_fresh by exact HT.
    rewrite IHt with (theta := theta) (gamma := gamma) (X := X) (A := A)
      by exact Hbody. reflexivity.
  - apply not_in_app in Hfresh as [H1 H2].
    rewrite IHt1 with (theta := theta) (gamma := gamma) (X := X) (A := A),
      IHt2 with (theta := theta) (gamma := gamma) (X := X) (A := A);
      try assumption. reflexivity.
  - rewrite IHt with (theta := theta) (gamma := gamma) (X := X) (A := A)
      by exact Hfresh. reflexivity.
  - apply not_in_app in Hfresh as [Hbody HT].
    rewrite IHt with (theta := theta) (gamma := gamma) (X := X) (A := A)
      by exact Hbody.
    rewrite instantiate_ty_update_fresh by exact HT. reflexivity.
Qed.

Lemma instantiate_update_fresh_term : forall t theta gamma x u,
  ~ In x (fv_tm t) ->
  instantiate theta (term_subst_update gamma x u) t =
  instantiate theta gamma t.
Proof.
  induction t; intros theta gamma x u Hfresh; simpl in *.
  - reflexivity.
  - simpl in Hfresh. assert (Hneq : x <> a).
    { intro Heq. apply Hfresh. simpl. left. symmetry. exact Heq. }
    assert (E : Nat.eqb x a = false) by (apply Nat.eqb_neq; exact Hneq).
    unfold term_subst_update. rewrite E. reflexivity.
  - rewrite IHt with (theta := theta) (gamma := gamma) (x := x) (u := u)
      by exact Hfresh. reflexivity.
  - apply not_in_app in Hfresh as [H1 H2].
    rewrite IHt1 with (theta := theta) (gamma := gamma) (x := x) (u := u),
      IHt2 with (theta := theta) (gamma := gamma) (x := x) (u := u);
      try assumption. reflexivity.
  - rewrite IHt with (theta := theta) (gamma := gamma) (x := x) (u := u)
      by exact Hfresh. reflexivity.
  - rewrite IHt with (theta := theta) (gamma := gamma) (x := x) (u := u)
      by exact Hfresh. reflexivity.
Qed.

Lemma fundamental_logical_relation : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall xi theta1 theta2 gamma1 gamma2,
    relation_environment_good xi ->
    matching_type_substitutions xi theta1 theta2 ->
    type_substitution_closed theta1 ->
    type_substitution_closed theta2 ->
    term_substitution_closed gamma1 ->
    term_substitution_closed gamma2 ->
    related_context_substitutions xi Gamma gamma1 gamma2 ->
    evaluated_by (logical_relation xi [] T)
      (instantiate theta1 gamma1 t) (instantiate theta2 gamma2 t).
Proof.
  intros Delta Gamma t T Hty.
  induction Hty; intros xi theta1 theta2 gamma1 gamma2 Hgood Hmatch
    Htheta1 Htheta2 Hgamma1 Hgamma2 Hctx.
  - specialize (Hctx x T H). simpl. exact Hctx.
  - simpl.
    assert (HabsTyping : has_type Delta Gamma (tm_abs T1 t2) (Ty_Arrow T1 T2)).
    { apply T_Abs with (L := L); assumption. }
    pose proof (has_type_locally_closed _ _ _ _ HabsTyping) as HabsLC.
    pose proof (instantiate_lc_tm_at (tm_abs T1 t2) 0 0 theta1 gamma1
      HabsLC Htheta1 Hgamma1) as HabsLC1.
    pose proof (instantiate_lc_tm_at (tm_abs T1 t2) 0 0 theta2 gamma2
      HabsLC Htheta2 Hgamma2) as HabsLC2.
    exists (tm_abs (instantiate_ty theta1 T1) (instantiate theta1 gamma1 t2)),
      (tm_abs (instantiate_ty theta2 T1) (instantiate theta2 gamma2 t2)).
    split; [constructor|].
    split; [constructor|].
    split; [apply v_abs; exact HabsLC1|].
    split; [apply v_abs; exact HabsLC2|].
    split; [apply v_abs; exact HabsLC1|].
    split; [apply v_abs; exact HabsLC2|].
    pose proof (fresh_notin (L ++ dom_context Gamma ++ fv_tm t2)) as Hfreshall.
    apply not_in_app in Hfreshall as [HnotL Hrest].
    apply not_in_app in Hrest as [Hnotdom Hnotfv].
    assert (Hfresh : ~ In (fresh (L ++ dom_context Gamma ++ fv_tm t2)) L).
    { exact HnotL. }
    assert (Hdom : ~ In (fresh (L ++ dom_context Gamma ++ fv_tm t2)) (dom_context Gamma)).
    { exact Hnotdom. }
    assert (Hfv : ~ In (fresh (L ++ dom_context Gamma ++ fv_tm t2)) (fv_tm t2)).
    { exact Hnotfv. }
    intros a b Ha Hb Hab.
    assert (Harg : evaluated_by (logical_relation xi [] T1) a b).
    { exists a,b. repeat split; try assumption; constructor. }
    pose proof (related_context_term_update xi Gamma gamma1 gamma2
      (fresh (L ++ dom_context Gamma ++ fv_tm t2)) T1 a b Hdom Hctx Harg) as Hctx'.
    pose proof (H1 (fresh (L ++ dom_context Gamma ++ fv_tm t2)) Hfresh
      xi theta1 theta2
      (term_subst_update gamma1 (fresh (L ++ dom_context Gamma ++ fv_tm t2)) a)
      (term_subst_update gamma2 (fresh (L ++ dom_context Gamma ++ fv_tm t2)) b)
      Hgood Hmatch Htheta1 Htheta2
      (term_subst_update_closed gamma1 (fresh (L ++ dom_context Gamma ++ fv_tm t2)) a Hgamma1
        (value_regular _ Ha))
      (term_subst_update_closed gamma2 (fresh (L ++ dom_context Gamma ++ fv_tm t2)) b Hgamma2
        (value_regular _ Hb)) Hctx') as Hbody.
    assert (Hbodyeq1 :
      instantiate theta1
        (term_subst_update gamma1 (fresh (L ++ dom_context Gamma ++ fv_tm t2)) a)
        (open_tm t2 (tm_fvar (fresh (L ++ dom_context Gamma ++ fv_tm t2)))) =
      open_tm (instantiate theta1 gamma1 t2) a).
    { unfold open_tm. rewrite instantiate_open_tm_rec with (k := 0)
        (gamma := term_subst_update gamma1 (fresh (L ++ dom_context Gamma ++ fv_tm t2)) a)
        (x := fresh (L ++ dom_context Gamma ++ fv_tm t2)).
      2: { eapply term_subst_update_closed; [exact Hgamma1|apply value_regular; exact Ha]. }
      rewrite instantiate_update_fresh_term with (x := fresh (L ++ dom_context Gamma ++ fv_tm t2))
        (u := a); [|exact Hfv].
      unfold term_subst_update. rewrite Nat.eqb_refl. reflexivity.
    }
    assert (Hbodyeq2 :
      instantiate theta2
        (term_subst_update gamma2 (fresh (L ++ dom_context Gamma ++ fv_tm t2)) b)
        (open_tm t2 (tm_fvar (fresh (L ++ dom_context Gamma ++ fv_tm t2)))) =
      open_tm (instantiate theta2 gamma2 t2) b).
    { unfold open_tm. rewrite instantiate_open_tm_rec with (k := 0)
        (gamma := term_subst_update gamma2 (fresh (L ++ dom_context Gamma ++ fv_tm t2)) b)
        (x := fresh (L ++ dom_context Gamma ++ fv_tm t2)).
      2: { eapply term_subst_update_closed; [exact Hgamma2|apply value_regular; exact Hb]. }
      rewrite instantiate_update_fresh_term with (x := fresh (L ++ dom_context Gamma ++ fv_tm t2))
        (u := b); [|exact Hfv].
      unfold term_subst_update. rewrite Nat.eqb_refl. reflexivity.
    }
    destruct Hbody as [v1 [v2 [Hred1 [Hred2 [Hv1 [Hv2 Hrel]]]]]].
    exists v1,v2. repeat split; try assumption.
    + eapply multi_trans.
      * eapply multi_step with (y := open_tm (instantiate theta1 gamma1 t2) a).
        -- apply ST_AppAbs; [exact HabsLC1|exact Ha].
        -- apply multi_refl.
      * rewrite <- Hbodyeq1. exact Hred1.
    + eapply multi_trans.
      * eapply multi_step with (y := open_tm (instantiate theta2 gamma2 t2) b).
        -- apply ST_AppAbs; [exact HabsLC2|exact Hb].
        -- apply multi_refl.
      * rewrite <- Hbodyeq2. exact Hred2.
  - simpl.
    pose proof (has_type_locally_closed _ _ _ _ Hty2) as Hlc_t2.
    eapply evaluated_by_application.
    + eapply IHHty1; eassumption.
    + eapply IHHty2; eassumption.
    + eapply instantiate_lc_tm_at; [exact Hlc_t2|exact Htheta1|exact Hgamma1].
    + eapply instantiate_lc_tm_at; [exact Hlc_t2|exact Htheta2|exact Hgamma2].
  - (* type abstraction *)
    simpl.
    assert (HtabsTyping : has_type Delta Gamma (tm_tabs t)
      (Ty_All T)).
    { apply T_TAbs with (L := L); assumption. }
    pose proof (has_type_locally_closed _ _ _ _ HtabsTyping) as HtabsLC.
    pose proof (instantiate_lc_tm_at (tm_tabs t) 0 0 theta1 gamma1
      HtabsLC Htheta1 Hgamma1) as HtabsLC1.
    pose proof (instantiate_lc_tm_at (tm_tabs t) 0 0 theta2 gamma2
      HtabsLC Htheta2 Hgamma2) as HtabsLC2.
    exists (tm_tabs (instantiate theta1 gamma1 t)),
      (tm_tabs (instantiate theta2 gamma2 t)).
    split; [constructor|].
    split; [constructor|].
    split; [apply v_tabs; exact HtabsLC1|].
    split; [apply v_tabs; exact HtabsLC2|].
    split; [apply v_tabs; exact HtabsLC1|].
    split; [apply v_tabs; exact HtabsLC2|].
    exists (instantiate theta1 gamma1 t), (instantiate theta2 gamma2 t).
    repeat split; try reflexivity.
    intros A C R HA HC HRgood.
    pose (e := mk_type_relation_entry A C R).
    pose (X := fresh (L ++ ftv_context Gamma ++ fv_ty T ++ ftv_tm t)).
    assert (Hfreshall : ~ In X (L ++ ftv_context Gamma ++ fv_ty T ++ ftv_tm t)).
    { unfold X. apply fresh_notin. }
    apply not_in_app in Hfreshall as [HnotL Hrest].
    apply not_in_app in Hrest as [Hnotctx Hrest].
    apply not_in_app in Hrest as [HnotT Hnotbody].
    assert (Hentry : relation_entry_good e).
    { unfold e, relation_entry_good. simpl. auto. }
    assert (Hgood' : relation_environment_good (relation_env_update xi X e)).
    { apply relation_env_update_good; assumption. }
    assert (Hmatch' : matching_type_substitutions
      (relation_env_update xi X e)
      (type_subst_update theta1 X A) (type_subst_update theta2 X C)).
    { apply type_subst_update_matching with (e := e); try assumption;
        reflexivity. }
    assert (Htheta1' : type_substitution_closed (type_subst_update theta1 X A)).
    { apply type_subst_update_closed; [exact Htheta1|exact HA]. }
    assert (Htheta2' : type_substitution_closed (type_subst_update theta2 X C)).
    { apply type_subst_update_closed; [exact Htheta2|exact HC]. }
    pose proof (related_context_type_update xi X e Gamma gamma1 gamma2
      Hnotctx Hctx) as Hctx'.
    pose proof (H0 X HnotL (relation_env_update xi X e)
      (type_subst_update theta1 X A) (type_subst_update theta2 X C)
      gamma1 gamma2 Hgood' Hmatch' Htheta1' Htheta2'
      Hgamma1 Hgamma2 Hctx') as Hbody.
    assert (Hbodyeq1 :
      instantiate (type_subst_update theta1 X A) gamma1
        (open_tm_ty t (Ty_FVar X)) =
      open_tm_ty (instantiate theta1 gamma1 t) A).
    { unfold open_tm_ty. rewrite instantiate_open_tm_ty_rec
        with (k := 0) (theta := theta1)
          (gamma := gamma1) (X := X) (A := A).
      - rewrite instantiate_update_fresh_type with (X := X) (A := A).
        + reflexivity.
        + exact Hnotbody.
      - exact Htheta1.
      - exact HA.
      - exact Hgamma1. }
    assert (Hbodyeq2 :
      instantiate (type_subst_update theta2 X C) gamma2
        (open_tm_ty t (Ty_FVar X)) =
      open_tm_ty (instantiate theta2 gamma2 t) C).
    { unfold open_tm_ty. rewrite instantiate_open_tm_ty_rec
        with (k := 0) (theta := theta2)
          (gamma := gamma2) (X := X) (A := C).
      - rewrite instantiate_update_fresh_type with (X := X) (A := C).
        + reflexivity.
        + exact Hnotbody.
      - exact Htheta2.
      - exact HC.
      - exact Hgamma2. }
    destruct Hbody as [v1 [v2 [Hred1 [Hred2 [Hv1 [Hv2 Hrel]]]]]].
    eapply evaluated_by_morphism.
    + intros p q. apply logical_relation_open with (k := 0) (rho := [])
        (xi := xi) (X := X) (e := e).
      * reflexivity.
      * exact HnotT.
    + exists v1,v2. repeat split; try assumption.
      * eapply multi_trans.
        -- eapply multi_step with
             (y := open_tm_ty (instantiate theta1 gamma1 t) A).
           ++ apply ST_TAppTabs; [exact HtabsLC1|exact HA].
           ++ apply multi_refl.
        -- rewrite <- Hbodyeq1. exact Hred1.
      * eapply multi_trans.
        -- eapply multi_step with
             (y := open_tm_ty (instantiate theta2 gamma2 t) C).
           ++ apply ST_TAppTabs; [exact HtabsLC2|exact HC].
           ++ apply multi_refl.
        -- rewrite <- Hbodyeq2. exact Hred2.
  - (* type application *)
    simpl.
    pose proof (wf_ty_locally_closed _ _ H) as HUlc.
    pose proof (instantiate_ty_lc_at U 0 theta1
      HUlc Htheta1) as HA.
    pose proof (instantiate_ty_lc_at U 0 theta2
      HUlc Htheta2) as HC.
    pose (R := logical_relation xi [] U).
    assert (HRgood : forall a b, R a b -> value a /\ value b).
    { unfold R. eapply logical_relation_good.
      - exact HUlc.
      - exact Hgood.
      - intros e0 Hin. inversion Hin.
    }
    pose proof (IHHty xi theta1 theta2 gamma1 gamma2 Hgood Hmatch
      Htheta1 Htheta2 Hgamma1 Hgamma2 Hctx) as Hfun.
    destruct Hfun as [f [g [Hf [Hg [Hfv [Hgv Hrel]]]]]].
    destruct Hrel as [Hfv' [Hgv' [fbody [gbody [Hfbody [Hgbody Hforall]]]]]].
    subst f. subst g.
    specialize (Hforall (instantiate_ty theta1 U) (instantiate_ty theta2 U)
      R HA HC HRgood) as Hrun.
    assert (Heq : forall a b,
      tr_values (mk_type_relation_entry (instantiate_ty theta1 U)
        (instantiate_ty theta2 U) R) a b <->
      logical_relation xi [] U a b).
    { intros a b. reflexivity. }
    eapply evaluated_by_morphism.
    + intros a b. apply iff_sym.
      eapply logical_relation_type_open with (k := 0) (rho := [])
        (U := U)
        (e := mk_type_relation_entry (instantiate_ty theta1 U)
          (instantiate_ty theta2 U) R).
      * reflexivity.
      * exact HUlc.
      * exact Heq.
    + destruct Hrun as [out1 [out2 [Hrun1 [Hrun2 [Hvout1 [Hvout2 Houtrel]]]]]].
      exists out1, out2. repeat split; try assumption.
      * eapply multi_trans.
        -- apply multi_tapp; [exact Hf|exact HA].
        -- exact Hrun1.
      * eapply multi_trans.
        -- apply multi_tapp; [exact Hg|exact HC].
        -- exact Hrun2.
Qed.

Definition identity_relation_environment : atom -> type_relation_entry :=
  fun X => mk_type_relation_entry (Ty_FVar X) (Ty_FVar X)
    (fun _ _ => False).

Lemma instantiate_ty_identity : forall T,
  instantiate_ty identity_type_substitution T = T.
Proof.
  induction T; simpl; try rewrite IHT; try rewrite IHT1; try rewrite IHT2;
    reflexivity.
Qed.

Lemma instantiate_identity : forall t,
  instantiate identity_type_substitution identity_term_substitution t = t.
Proof.
  induction t; simpl; try rewrite instantiate_ty_identity;
    try rewrite IHt; try rewrite IHt1; try rewrite IHt2; reflexivity.
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
  intros t Ht U v HU Hv Htv.
  assert (Hgood : relation_environment_good identity_relation_environment).
  { intro X. unfold relation_entry_good, identity_relation_environment.
    simpl. split; [apply lc_ty_fvar|]. split; [apply lc_ty_fvar|].
    intros a b Hfalse. contradiction. }
  assert (Hmatch : matching_type_substitutions identity_relation_environment
      identity_type_substitution identity_type_substitution).
  { intro X. unfold identity_relation_environment,
      identity_type_substitution. simpl. auto. }
  assert (Hctx : related_context_substitutions identity_relation_environment
      [] identity_term_substitution identity_term_substitution).
  { intros x T Hlook. discriminate. }
  pose proof (fundamental_logical_relation [] [] t
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) Ht
    identity_relation_environment identity_type_substitution
    identity_type_substitution identity_term_substitution
    identity_term_substitution Hgood Hmatch
    identity_type_substitution_closed identity_type_substitution_closed
    identity_term_substitution_closed identity_term_substitution_closed Hctx)
    as Hrel.
  rewrite !instantiate_identity in Hrel.
  eapply identity_from_logical_relation; eauto.
Qed.

End SystemFParametricityNoneEasyTask.
