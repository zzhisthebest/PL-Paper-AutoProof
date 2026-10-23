(** System F CBV strong-normalization benchmark, Easy variant.
    Features: if. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
From Stdlib Require Import Logic.FunctionalExtensionality Logic.PropExtensionality.
Import ListNotations.

Module SystemFNormalizationIfEasyTask.

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
  | Ty_Bool : ty.

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
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm.

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

Notation "'Bool'" := Ty_Bool (in custom systemf_ty at level 0) : systemf_scope.
Notation "'true'" := tm_true (in custom systemf_tm at level 0) : systemf_scope.
Notation "'false'" := tm_false (in custom systemf_tm at level 0) : systemf_scope.
Notation "'if' t1 'then' t2 'else' t3" := (tm_if t1 t2 t3)
  (in custom systemf_tm at level 200, t1 custom systemf_tm, t2 custom systemf_tm, t3 custom systemf_tm at level 200) : systemf_scope.

Fixpoint open_ty_rec (k : nat) (U T : ty) : ty :=
  match T with
  | Ty_BVar i => if Nat.eqb k i then U else Ty_BVar i
  | Ty_FVar X => Ty_FVar X
  | Ty_Arrow T1 T2 =>
      Ty_Arrow (open_ty_rec k U T1) (open_ty_rec k U T2)
  | Ty_All T1 => Ty_All (open_ty_rec (S k) U T1)
  | Ty_Bool => Ty_Bool
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
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (open_tm_rec k u t1) (open_tm_rec k u t2) (open_tm_rec k u t3)
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
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (open_tm_ty_rec k U t1) (open_tm_ty_rec k U t2) (open_tm_ty_rec k U t3)
  end.

Definition open_tm_ty (t : tm) (U : ty) : tm :=
  open_tm_ty_rec 0 U t.

Fixpoint ty_subst (X : atom) (U T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar Y => if Nat.eqb X Y then U else Ty_FVar Y
  | Ty_Arrow T1 T2 => Ty_Arrow (ty_subst X U T1) (ty_subst X U T2)
  | Ty_All T1 => Ty_All (ty_subst X U T1)
  | Ty_Bool => Ty_Bool
  end.

Fixpoint tm_ty_subst (X : atom) (U : ty) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T t1 => tm_abs (ty_subst X U T) (tm_ty_subst X U t1)
  | tm_app t1 t2 => tm_app (tm_ty_subst X U t1) (tm_ty_subst X U t2)
  | tm_tabs t1 => tm_tabs (tm_ty_subst X U t1)
  | tm_tapp t1 T => tm_tapp (tm_ty_subst X U t1) (ty_subst X U T)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (tm_ty_subst X U t1) (tm_ty_subst X U t2) (tm_ty_subst X U t3)
  end.

Fixpoint tm_subst (x : atom) (s t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar y => if Nat.eqb x y then s else tm_fvar y
  | tm_abs T t1 => tm_abs T (tm_subst x s t1)
  | tm_app t1 t2 => tm_app (tm_subst x s t1) (tm_subst x s t2)
  | tm_tabs t1 => tm_tabs (tm_subst x s t1)
  | tm_tapp t1 T => tm_tapp (tm_subst x s t1) T
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (tm_subst x s t1) (tm_subst x s t2) (tm_subst x s t3)
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
  | lc_ty_bool : forall k, lc_ty_at k Ty_Bool.

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
  | lc_tm_true : forall K k, lc_tm_at K k tm_true
  | lc_tm_false : forall K k, lc_tm_at K k tm_false
  | lc_tm_if : forall K k t1 t2 t3,
      lc_tm_at K k t1 -> lc_tm_at K k t2 -> lc_tm_at K k t3 -> lc_tm_at K k (tm_if t1 t2 t3).

Definition locally_closed_tm (t : tm) : Prop := lc_tm_at 0 0 t.

Inductive value : tm -> Prop :=
  | v_abs : forall T t,
      locally_closed_tm (tm_abs T t) ->
      value (tm_abs T t)
  | v_tabs : forall t,
      locally_closed_tm (tm_tabs t) ->
      value (tm_tabs t)
  | v_true : value tm_true
  | v_false : value tm_false.

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
  | ST_IfTrue : forall t1 t2,
      locally_closed_tm t1 ->
      locally_closed_tm t2 ->
      tm_if tm_true t1 t2 --> t1
  | ST_IfFalse : forall t1 t2,
      locally_closed_tm t1 ->
      locally_closed_tm t2 ->
      tm_if tm_false t1 t2 --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      locally_closed_tm t2 ->
      locally_closed_tm t3 ->
      tm_if t1 t2 t3 --> tm_if t1' t2 t3
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
  | WF_Bool : forall Delta, wf_ty Delta Ty_Bool.

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
  | T_True : forall Delta Gamma, has_type Delta Gamma tm_true Ty_Bool
  | T_False : forall Delta Gamma, has_type Delta Gamma tm_false Ty_Bool
  | T_If : forall Delta Gamma t1 t2 t3 T,
      has_type Delta Gamma t1 Ty_Bool ->
      has_type Delta Gamma t2 T -> has_type Delta Gamma t3 T ->
      has_type Delta Gamma (tm_if t1 t2 t3) T.

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
  | Ty_Bool => []
  end.

Fixpoint fv_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs _ t1 => fv_tm t1
  | tm_app t1 t2 => fv_tm t1 ++ fv_tm t2
  | tm_tabs t1 => fv_tm t1
  | tm_tapp t1 _ => fv_tm t1
  | tm_true => []
  | tm_false => []
  | tm_if t1 t2 t3 => fv_tm t1 ++ fv_tm t2 ++ fv_tm t3
  end.

Fixpoint ftv_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_fvar _ => []
  | tm_abs T t1 => fv_ty T ++ ftv_tm t1
  | tm_app t1 t2 => ftv_tm t1 ++ ftv_tm t2
  | tm_tabs t1 => ftv_tm t1
  | tm_tapp t1 T => ftv_tm t1 ++ fv_ty T
  | tm_true => []
  | tm_false => []
  | tm_if t1 t2 t3 => ftv_tm t1 ++ ftv_tm t2 ++ ftv_tm t3
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
  - apply lc_ty_bool.

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
  - apply lc_tm_true.
  - apply lc_tm_false.
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
  - apply lc_ty_bool.

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
  - apply lc_ty_bool.

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
  - apply lc_tm_true.
  - apply lc_tm_false.
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
  - apply lc_tm_true.
  - apply lc_tm_false.
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
  | Ty_Bool => Ty_Bool
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
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (instantiate theta gamma t1) (instantiate theta gamma t2) (instantiate theta gamma t3)
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

(* Reducibility candidates are indexed by free type variables and by the
   de Bruijn stack of candidates bound by [forall]. *)
Definition candidate := tm -> Prop.
Definition candidate_env := atom -> candidate.
Definition bound_candidate_env := nat -> candidate.
Definition candidate_good (P : candidate) : Prop :=
  forall t, P t -> strongly_normalizing t.

Definition sn_candidate : candidate := strongly_normalizing.

Definition bound_update (bs : bound_candidate_env) (Q : candidate)
    : bound_candidate_env :=
  fun i => match i with O => Q | S j => bs j end.

Lemma bound_update_ext : forall bs bs' Q Q',
  (forall i, bs i = bs' i) -> (forall t, Q t <-> Q' t) ->
  forall i, bound_update bs Q i = bound_update bs' Q' i.
Proof.
  intros bs bs' Q Q' Hbs HQ i. destruct i; simpl.
  - apply functional_extensionality. intros t. apply propositional_extensionality.
    apply HQ.
  - apply Hbs.
Qed.

Definition good_candidate_env (rho : candidate_env) : Prop :=
  forall X t, rho X t -> strongly_normalizing t.

Fixpoint red (rho : candidate_env) (bs : bound_candidate_env) (T : ty)
    (t : tm) {struct T} : Prop :=
  strongly_normalizing t /\
  (forall v, multi t v -> value v ->
    match T with
    | Ty_BVar i => bs i v
    | Ty_FVar X => rho X v
    | Ty_Arrow A B =>
        exists S body, v = tm_abs S body /\
          (forall u, locally_closed_tm u -> red rho bs A u ->
            red rho bs B (open_tm body u))
    | Ty_All A =>
        exists body, v = tm_tabs body /\
          (forall U Q, locally_closed_ty U -> candidate_good Q ->
            red rho (bound_update bs Q) A (open_tm_ty body U))
    | Ty_Bool => v = tm_true \/ v = tm_false
    end).

Lemma red_sn : forall rho bs T t,
  red rho bs T t -> strongly_normalizing t.
Proof. intros rho bs T. destruct T; intros t H; simpl in H; tauto. Qed.

Lemma sn_value : forall v, value v -> strongly_normalizing v.
Proof.
  intros v Hv. apply SN_intro. intros u Hstep.
  exfalso. eapply value_no_step; eauto.
Qed.

Lemma red_env_equiv : forall rho (bs bs' : bound_candidate_env) T t,
  (forall i x, value x -> bs i x <-> bs' i x) ->
  red rho bs T t <-> red rho bs' T t.
Proof.
  intros rho bs bs' T t Heq. revert bs bs' t Heq.
  induction T; intros bs bs' t Heq; simpl.
  - split.
    + intros [Hs Hterm]. split; [exact Hs|].
      intros v Hpath Hv. apply (proj1 (Heq n v Hv)).
      eapply Hterm; eauto.
    + intros [Hs Hterm]. split; [exact Hs|].
      intros v Hpath Hv. apply (proj2 (Heq n v Hv)).
      eapply Hterm; eauto.
  - tauto.
  - split.
    + intros [Hs Hterm]. split; [exact Hs|]. intros v Hpath Hv.
      destruct (Hterm v Hpath Hv) as [S [body [Ev Hbody]]].
      exists S, body. split; [exact Ev|]. intros u Hlu HuA.
      apply (proj1 (IHT2 bs bs' (open_tm body u) Heq)).
      apply Hbody; [exact Hlu|]. apply (proj2 (IHT1 bs bs' u Heq)). exact HuA.
    + intros [Hs Hterm]. split; [exact Hs|]. intros v Hpath Hv.
      destruct (Hterm v Hpath Hv) as [S [body [Ev Hbody]]].
      exists S, body. split; [exact Ev|]. intros u Hlu HuA.
      apply (proj2 (IHT2 bs bs' (open_tm body u) Heq)).
      apply Hbody; [exact Hlu|]. apply (proj1 (IHT1 bs bs' u Heq)). exact HuA.
  - split.
    + intros [Hs Hterm]. split; [exact Hs|]. intros v Hpath Hv.
      destruct (Hterm v Hpath Hv) as [body [Ev Hbody]].
      exists body. split; [exact Ev|]. intros U Q HU HQ.
      apply (proj1 (IHT (bound_update bs Q) (bound_update bs' Q)
        (open_tm_ty body U) ltac:(intros i x Hval; destruct i; simpl; [tauto|apply Heq; exact Hval]))).
      apply Hbody; assumption.
    + intros [Hs Hterm]. split; [exact Hs|]. intros v Hpath Hv.
      destruct (Hterm v Hpath Hv) as [body [Ev Hbody]].
      exists body. split; [exact Ev|]. intros U Q HU HQ.
      apply (proj2 (IHT (bound_update bs Q) (bound_update bs' Q)
        (open_tm_ty body U) ltac:(intros i x Hval; destruct i; simpl; [tauto|apply Heq; exact Hval]))).
      apply Hbody; assumption.
  - tauto.
Qed.

Definition free_update (rho : candidate_env) (X : atom) (Q : candidate)
    : candidate_env :=
  fun Y => if Nat.eqb X Y then Q else rho Y.

Lemma red_free_env_equiv : forall rho rho' bs T,
  (forall X t, rho X t <-> rho' X t) -> forall t,
  red rho bs T t <-> red rho' bs T t.
Proof.
  intros rho rho' bs T. revert bs. induction T; intros bs Heq t; simpl.
  - tauto.
  - split.
    + intros [Hs Hterm]. split; [exact Hs|]. intros v Hpath Hv.
      apply (proj1 (Heq a v)). eapply Hterm; eauto.
    + intros [Hs Hterm]. split; [exact Hs|]. intros v Hpath Hv.
      apply (proj2 (Heq a v)). eapply Hterm; eauto.
  - split.
    + intros [Hs Hterm]. split; [exact Hs|]. intros v Hpath Hv.
      destruct (Hterm v Hpath Hv) as [S [body [Ev Hbody]]].
      exists S, body. split; [exact Ev|]. intros u Hlu Hu.
      apply (proj1 (IHT2 bs Heq (open_tm body u))).
      apply Hbody; [exact Hlu|]. apply (proj2 (IHT1 bs Heq u)). exact Hu.
    + intros [Hs Hterm]. split; [exact Hs|]. intros v Hpath Hv.
      destruct (Hterm v Hpath Hv) as [S [body [Ev Hbody]]].
      exists S, body. split; [exact Ev|]. intros u Hlu Hu.
      apply (proj2 (IHT2 bs Heq (open_tm body u))).
      apply Hbody; [exact Hlu|]. apply (proj1 (IHT1 bs Heq u)). exact Hu.
  - split.
    + intros [Hs Hterm]. split; [exact Hs|]. intros v Hpath Hv.
      destruct (Hterm v Hpath Hv) as [body [Ev Hbody]].
      exists body. split; [exact Ev|]. intros U Q HU HQ.
      apply (proj1 (IHT (bound_update bs Q) Heq (open_tm_ty body U))). apply Hbody; assumption.
    + intros [Hs Hterm]. split; [exact Hs|]. intros v Hpath Hv.
      destruct (Hterm v Hpath Hv) as [body [Ev Hbody]].
      exists body. split; [exact Ev|]. intros U Q HU HQ.
      apply (proj2 (IHT (bound_update bs Q) Heq (open_tm_ty body U))). apply Hbody; assumption.
  - tauto.
Qed.

Lemma red_fv_irrel : forall rho bs X Q T t,
  ~ In X (fv_ty T) ->
  red (free_update rho X Q) bs T t <-> red rho bs T t.
Proof.
  intros rho bs X Q T. revert bs. induction T; intros bs t Hfresh; simpl in *.
  - tauto.
  - simpl in Hfresh. assert (Hneq : X <> a).
    { intro Heq. subst a. apply Hfresh. simpl. auto. }
    assert (Heq : free_update rho X Q a = rho a).
    { unfold free_update. assert (E : Nat.eqb X a = false).
      { apply Nat.eqb_neq. exact Hneq. } now rewrite E. }
    rewrite Heq. tauto.
  - simpl in Hfresh. split.
    + intros [Hs Hterm]. split; [exact Hs|]. intros v Hpath Hv.
      destruct (Hterm v Hpath Hv) as [S [body [Ev Hbody]]].
      exists S, body. split; [exact Ev|]. intros u Hlu Hu.
      apply (proj1 (IHT2 bs (open_tm body u)
        ltac:(intro Hin; apply Hfresh; apply in_or_app; right; exact Hin))).
      apply Hbody; [exact Hlu|]. apply (proj2 (IHT1 bs u
        ltac:(intro Hin; apply Hfresh; apply in_or_app; left; exact Hin))). exact Hu.
    + intros [Hs Hterm]. split; [exact Hs|]. intros v Hpath Hv.
      destruct (Hterm v Hpath Hv) as [S [body [Ev Hbody]]].
      exists S, body. split; [exact Ev|]. intros u Hlu Hu.
      apply (proj2 (IHT2 bs (open_tm body u)
        ltac:(intro Hin; apply Hfresh; apply in_or_app; right; exact Hin))).
      apply Hbody; [exact Hlu|]. apply (proj1 (IHT1 bs u
        ltac:(intro Hin; apply Hfresh; apply in_or_app; left; exact Hin))). exact Hu.
  - split.
    + intros [Hs Hterm]. split; [exact Hs|]. intros v Hpath Hv.
      destruct (Hterm v Hpath Hv) as [body [Ev Hbody]].
      exists body. split; [exact Ev|]. intros U R HU HR.
      apply (proj1 (IHT (bound_update bs R) (open_tm_ty body U)
        ltac:(intro Hin; apply Hfresh; exact Hin))).
      apply Hbody; assumption.
    + intros [Hs Hterm]. split; [exact Hs|]. intros v Hpath Hv.
      destruct (Hterm v Hpath Hv) as [body [Ev Hbody]].
      exists body. split; [exact Ev|]. intros U R HU HR.
      apply (proj2 (IHT (bound_update bs R) (open_tm_ty body U)
        ltac:(intro Hin; apply Hfresh; exact Hin))).
      apply Hbody; assumption.
  - tauto.
Qed.

Lemma red_lc_env_irrel : forall rho k T,
  lc_ty_at k T -> forall bs bs' t,
  (forall i, i < k -> forall x, bs i x <-> bs' i x) ->
  red rho bs T t <-> red rho bs' T t.
Proof.
  intros rho k T. revert k. induction T; intros k Hlc bs bs' t Hag; simpl.
  - inversion Hlc; subst. split.
    + intros [Hs Hterm]. split; [exact Hs|].
      intros v Hpath Hv. apply (proj1 (Hag n ltac:(lia) v)). eapply Hterm; eauto.
    + intros [Hs Hterm]. split; [exact Hs|].
      intros v Hpath Hv. apply (proj2 (Hag n ltac:(lia) v)). eapply Hterm; eauto.
  - tauto.
  - inversion Hlc as [| |k0 A0 B0 Hleft Hright| |]; subst. split.
    + intros [Hs Hterm]. split; [exact Hs|]. intros v Hpath Hv.
      destruct (Hterm v Hpath Hv) as [S [body [Ev Hbody]]].
      exists S, body. split; [exact Ev|]. intros u Hlu HuA.
      apply (proj1 (IHT2 k Hright bs bs' (open_tm body u) Hag)).
      apply Hbody; [exact Hlu|]. apply (proj2 (IHT1 k Hleft bs bs' u Hag)). exact HuA.
    + intros [Hs Hterm]. split; [exact Hs|]. intros v Hpath Hv.
      destruct (Hterm v Hpath Hv) as [S [body [Ev Hbody]]].
      exists S, body. split; [exact Ev|]. intros u Hlu HuA.
      apply (proj2 (IHT2 k Hright bs bs' (open_tm body u) Hag)).
      apply Hbody; [exact Hlu|]. apply (proj1 (IHT1 k Hleft bs bs' u Hag)). exact HuA.
  - inversion Hlc as [| | |k0 A0 Hbodylc|]; subst. split.
    + intros [Hs Hterm]. split; [exact Hs|]. intros v Hpath Hv.
      destruct (Hterm v Hpath Hv) as [body [Ev Hbody]].
      exists body. split; [exact Ev|]. intros U Q HU HQ.
      apply (proj1 (IHT (S k) Hbodylc (bound_update bs Q) (bound_update bs' Q)
        (open_tm_ty body U)
        ltac:(intros i Hi x; destruct i; simpl; [tauto|apply Hag; lia]))).
      apply Hbody; assumption.
    + intros [Hs Hterm]. split; [exact Hs|]. intros v Hpath Hv.
      destruct (Hterm v Hpath Hv) as [body [Ev Hbody]].
      exists body. split; [exact Ev|]. intros U Q HU HQ.
      apply (proj2 (IHT (S k) Hbodylc (bound_update bs Q) (bound_update bs' Q)
        (open_tm_ty body U)
        ltac:(intros i Hi x; destruct i; simpl; [tauto|apply Hag; lia]))).
      apply Hbody; assumption.
  - tauto.
Qed.

Definition bound_insert (bs : bound_candidate_env) (k : nat) (Q : candidate)
    : bound_candidate_env :=
  fun i => if Nat.ltb i k then bs i else
           if Nat.eqb i k then Q else bs (Nat.pred i).

Lemma bound_insert_update_equiv : forall bs R Q0 Q1 k,
  (forall t, Q0 t <-> Q1 t) ->
  forall i t,
    bound_insert (bound_update bs R) (S k) Q1 i t <->
    bound_update (bound_insert bs k Q0) R i t.
Proof.
  intros bs R Q0 Q1 k HQ i t. destruct i as [|i]; simpl.
  - tauto.
  - simpl. destruct (Nat.ltb i k) eqn:E.
    + unfold bound_insert. rewrite E. destruct (S i <? S k) eqn:E2; simpl.
      * reflexivity.
      * apply Nat.ltb_ge in E2. apply Nat.ltb_lt in E. lia.
    + destruct (Nat.eqb i k) eqn:Eeq.
      * apply Nat.eqb_eq in Eeq. subst i. unfold bound_insert.
        rewrite E. rewrite Nat.ltb_irrefl, Nat.eqb_refl. simpl.
        rewrite Nat.eqb_refl. specialize (HQ t). tauto.
      * apply Nat.ltb_ge in E. apply Nat.eqb_neq in Eeq.
        unfold bound_insert.
        destruct (S i <? S k) eqn:E2.
        { apply Nat.ltb_lt in E2. lia. }
        destruct (S i =? S k) eqn:E3.
        { apply Nat.eqb_eq in E3. lia. }
        assert (Hgt : k < i) by lia. destruct i as [|j]; [lia|].
        assert (E4 : (S j <? k) = false) by (apply Nat.ltb_ge; lia).
        assert (E5 : (S j =? k) = false) by (apply Nat.eqb_neq; lia).
        simpl. rewrite E4. destruct k as [|k']; simpl.
        { reflexivity. }
        { assert (E6 : (j =? k') = false) by (apply Nat.eqb_neq; lia).
          rewrite E6. reflexivity. }
Qed.

Lemma red_value : forall rho bs T v, value v ->
  red rho bs T v <->
  strongly_normalizing v /\
    (match T with
     | Ty_BVar i => bs i v
     | Ty_FVar X => rho X v
     | Ty_Arrow A B => exists S body, v = tm_abs S body /\
         (forall u, locally_closed_tm u -> red rho bs A u ->
           red rho bs B (open_tm body u))
     | Ty_All A => exists body, v = tm_tabs body /\
         (forall U Q, locally_closed_ty U -> candidate_good Q ->
           red rho (bound_update bs Q) A (open_tm_ty body U))
     | Ty_Bool => v = tm_true \/ v = tm_false
     end).
Proof.
  intros rho bs T v Hv. destruct T; simpl.
  - split.
    + intros [Hs Hrel]. split; [exact Hs|exact (Hrel v (multi_refl v) Hv)].
    + intros [Hs Hrel]. split; [exact Hs|]. intros w Hpath Hw.
      pose proof (value_multi_eq v w Hv Hpath) as ->. exact Hrel.
  - split.
    + intros [Hs Hrel]. split; [exact Hs|exact (Hrel v (multi_refl v) Hv)].
    + intros [Hs Hrel]. split; [exact Hs|]. intros w Hpath Hw.
      pose proof (value_multi_eq v w Hv Hpath) as ->. exact Hrel.
  - split.
    + intros [Hs Hterm]. split; [exact Hs|].
      destruct (Hterm v (multi_refl v) Hv) as [S [body [Ev Hbody]]].
      exists S, body. split; assumption.
    + intros [Hs [S [body [Ev Hbody]]]]. split; [exact Hs|].
      intros w Hpath Hw. pose proof (value_multi_eq v w Hv Hpath) as ->.
      exists S, body. split; assumption.
  - split.
    + intros [Hs Hterm]. split; [exact Hs|].
      destruct (Hterm v (multi_refl v) Hv) as [body [Ev Hbody]].
      exists body. split; assumption.
    + intros [Hs [body [Ev Hbody]]]. split; [exact Hs|].
      intros w Hpath Hw. pose proof (value_multi_eq v w Hv Hpath) as ->.
      exists body. split; assumption.
  - split.
    + intros [Hs Hterm]. split; [exact Hs|exact (Hterm v (multi_refl v) Hv)].
    + intros [Hs Hrel]. split; [exact Hs|]. intros w Hpath Hw.
      pose proof (value_multi_eq v w Hv Hpath) as ->. exact Hrel.
Qed.

Lemma red_terminal : forall rho bs T t v,
  red rho bs T t -> t -->* v -> value v ->
  match T with
  | Ty_BVar i => bs i v
  | Ty_FVar X => rho X v
  | Ty_Arrow A B => exists S body, v = tm_abs S body /\
      (forall u, locally_closed_tm u -> red rho bs A u ->
        red rho bs B (open_tm body u))
  | Ty_All A => exists body, v = tm_tabs body /\
      (forall U Q, locally_closed_ty U -> candidate_good Q ->
        red rho (bound_update bs Q) A (open_tm_ty body U))
  | Ty_Bool => v = tm_true \/ v = tm_false
  end.
Proof.
  intros rho bs T. destruct T; intros t v Hred Hpath Hv;
    simpl in *; destruct Hred as [_ Hterm]; eauto.
Qed.

Lemma red_from_terminals : forall rho bs T t,
  strongly_normalizing t ->
  (forall v, multi t v -> value v -> red rho bs T v) ->
  red rho bs T t.
Proof.
  intros rho bs T. destruct T; intros t Hsn Hterm; simpl; split.
  all: try exact Hsn.
  all: intros v Hpath Hv.
  all: destruct (proj1 (red_value rho bs _ v Hv) (Hterm v Hpath Hv)) as [_ Hcl].
  all: exact Hcl.
Qed.

Lemma red_open_ty_rec : forall rho bs k U T t,
  locally_closed_ty U -> lc_ty_at (S k) T ->
  (red rho (bound_insert bs k (red rho bs U)) T t <->
   red rho bs (open_ty_rec k U T) t).
Proof.
  intros rho bs k U T. revert rho bs k U.
  induction T; intros rho bs k U t HU Hlc; simpl.
  - inversion Hlc; subst. assert (Hbound : n < S k) by lia.
    destruct (Nat.eq_dec n k) as [Heq|Hneq].
    + subst n. unfold bound_insert. rewrite Nat.ltb_irrefl, Nat.eqb_refl.
      simpl. split.
      * intros [Hs Hterm]. eapply red_from_terminals; [exact Hs|exact Hterm].
      * intro Hred. split; [eapply red_sn; eauto|]. intros v Hpath Hv.
        pose proof (red_terminal rho bs U t v Hred Hpath Hv) as Hcl.
        apply (proj2 (red_value rho bs U v Hv)). split.
        -- apply sn_value. exact Hv.
        -- exact Hcl.
    + assert (Hlt : n < k) by lia.
      assert (Hins : bound_insert bs k (red rho bs U) n = bs n).
      { unfold bound_insert. assert (E : (n <? k) = true) by (apply Nat.ltb_lt; exact Hlt).
        rewrite E. reflexivity. }
      assert (Heqopen : (k =? n) = false) by (apply Nat.eqb_neq; lia).
      rewrite Hins, Heqopen. reflexivity.
  - tauto.
  - inversion Hlc as [| |k0 A0 B0 Hleft Hright| |]; subst. split.
    + intros [Hs Hterm]. split; [exact Hs|]. intros v Hpath Hv.
      destruct (Hterm v Hpath Hv) as [S [body [Ev Hbody]]].
      exists S, body. split; [exact Ev|]. intros u Hlu HuA.
      apply (proj1 (IHT2 rho bs k U (open_tm body u) HU Hright)).
      apply Hbody; [exact Hlu|]. apply (proj2 (IHT1 rho bs k U u HU Hleft)). exact HuA.
    + intros [Hs Hterm]. split; [exact Hs|]. intros v Hpath Hv.
      destruct (Hterm v Hpath Hv) as [S [body [Ev Hbody]]].
      exists S, body. split; [exact Ev|]. intros u Hlu HuA.
      apply (proj2 (IHT2 rho bs k U (open_tm body u) HU Hright)).
      apply Hbody; [exact Hlu|]. apply (proj1 (IHT1 rho bs k U u HU Hleft)). exact HuA.
  - inversion Hlc as [| | |k0 A0 Hbodylc|]; subst. split.
    + intros [Hs Hterm]. split; [exact Hs|]. intros v Hpath Hv.
      destruct (Hterm v Hpath Hv) as [body [Ev Hbody]].
      exists body. split; [exact Ev|]. intros U' Q HU' HQ.
      assert (Henv : forall i x,
        bound_insert (bound_update bs Q) (S k) (red rho (bound_update bs Q) U) i x <->
        bound_update (bound_insert bs k (red rho bs U)) Q i x).
      { intros i x. eapply bound_insert_update_equiv.
        intros y. apply red_lc_env_irrel with (k:=0); [exact HU|intros; lia]. }
      apply (proj1 (IHT rho (bound_update bs Q) (S k) U
        (open_tm_ty body U') HU Hbodylc)).
      apply (proj2 (red_env_equiv rho
        (bound_insert (bound_update bs Q) (S k) (red rho (bound_update bs Q) U))
        (bound_update (bound_insert bs k (red rho bs U)) Q)
        T (open_tm_ty body U') ltac:(intros i x Hval; apply Henv))).
      apply Hbody; assumption.
    + intros [Hs Hterm]. split; [exact Hs|]. intros v Hpath Hv.
      destruct (Hterm v Hpath Hv) as [body [Ev Hbody]].
      exists body. split; [exact Ev|]. intros U' Q HU' HQ.
      assert (Henv : forall i x,
        bound_insert (bound_update bs Q) (S k) (red rho (bound_update bs Q) U) i x <->
        bound_update (bound_insert bs k (red rho bs U)) Q i x).
      { intros i x. eapply bound_insert_update_equiv.
        intros y. apply red_lc_env_irrel with (k:=0); [exact HU|intros; lia]. }
      apply (proj1 (red_env_equiv rho
        (bound_insert (bound_update bs Q) (S k) (red rho (bound_update bs Q) U))
        (bound_update (bound_insert bs k (red rho bs U)) Q)
        T (open_tm_ty body U') ltac:(intros i x Hval; apply Henv))).
      apply (proj2 (IHT rho (bound_update bs Q) (S k) U
        (open_tm_ty body U') HU Hbodylc)).
      apply Hbody; assumption.
  - tauto.
Qed.

Lemma red_step : forall rho bs T t u,
  red rho bs T t -> t --> u -> red rho bs T u.
Proof.
  intros rho bs T t u Hred Hstep. destruct T; simpl in *;
    destruct Hred as [Hsn Hterm]; split.
  all: try (inversion Hsn; subst; eauto).
  all: intros v Hpath Hv; eapply Hterm;
    [eapply multi_step; eauto|exact Hv].
Qed.

Lemma red_multi : forall rho bs T t u,
  red rho bs T t -> t -->* u -> red rho bs T u.
Proof.
  intros rho bs T t u Hred Hpath. induction Hpath.
  - exact Hred.
  - apply IHHpath. eapply red_step; eauto.
Qed.

Lemma red_expand : forall rho bs T t,
  ~ value t ->
  (forall u, t --> u -> red rho bs T u) ->
  red rho bs T t.
Proof.
  intros rho bs T. destruct T; intros t Hnot Hnext; simpl; split.
  all: try solve [apply SN_intro; intros u Hstep; exact (proj1 (Hnext u Hstep))].
  all: intros v Hpath Hv; induction Hpath.
  all: try solve [exfalso; apply Hnot; exact Hv].
  all: match goal with
       | Hst : ?x --> ?y, Hrest : ?y -->* ?z |- _ =>
           destruct (Hnext y Hst) as [_ Hterm]; exact (Hterm z Hrest Hv)
       end.
Qed.

Lemma sn_step : forall t u,
  strongly_normalizing t -> t --> u -> strongly_normalizing u.
Proof. intros t u H; inversion H; subst; eauto. Qed.

Lemma not_value_app : forall t u, ~ value (tm_app t u).
Proof. intros t u H; inversion H. Qed.

Lemma red_abs : forall rho bs A B S body,
  locally_closed_tm (tm_abs S body) ->
  (forall u, locally_closed_tm u -> red rho bs A u ->
     red rho bs B (open_tm body u)) ->
  red rho bs (Ty_Arrow A B) (tm_abs S body).
Proof.
  intros rho bs A B S body Hlc Hbody. split.
  - apply sn_value. constructor. exact Hlc.
  - intros v Hpath Hv. rewrite (value_multi_eq (tm_abs S body) v
      (v_abs S body Hlc) Hpath).
    exists S, body. split; [reflexivity|exact Hbody].
Qed.

Lemma red_tabs : forall rho bs A body,
  locally_closed_tm (tm_tabs body) ->
  (forall U Q, locally_closed_ty U -> candidate_good Q ->
     red rho (bound_update bs Q) A (open_tm_ty body U)) ->
  red rho bs (Ty_All A) (tm_tabs body).
Proof.
  intros rho bs A body Hlc Hbody. split.
  - apply sn_value. constructor. exact Hlc.
  - intros v Hpath Hv. rewrite (value_multi_eq (tm_tabs body) v
      (v_tabs body Hlc) Hpath).
    exists body. split; [reflexivity|exact Hbody].
Qed.

Lemma red_bool_true : forall rho bs, red rho bs Ty_Bool tm_true.
Proof.
  intros. split; [apply sn_value; constructor|].
  intros v Hpath Hv. rewrite (value_multi_eq tm_true v v_true Hpath). left; reflexivity.
Qed.

Lemma red_bool_false : forall rho bs, red rho bs Ty_Bool tm_false.
Proof.
  intros. split; [apply sn_value; constructor|].
  intros v Hpath Hv. rewrite (value_multi_eq tm_false v v_false Hpath). right; reflexivity.
Qed.

Lemma red_app_abs : forall rho bs A B S body u,
  locally_closed_tm (tm_abs S body) ->
  red rho bs A u ->
  (forall v, red rho bs A v -> red rho bs B (open_tm body v)) ->
  red rho bs B (tm_app (tm_abs S body) u).
Proof.
  intros rho bs A B S body u Hlc Harg Hbody.
  assert (Hval : value (tm_abs S body)) by (constructor; exact Hlc).
  assert (Hgen : forall z, strongly_normalizing z -> red rho bs A z ->
      red rho bs B (tm_app (tm_abs S body) z)).
  {
    intros z Hz. induction Hz as [z Hnext IH]. intros HzA.
    eapply red_expand.
    - apply not_value_app.
    - intros q Hq. inversion Hq; subst.
      + eapply Hbody; exact HzA.
      + exfalso. eapply value_no_step; eauto.
      + eapply IH; [exact H3|eapply red_step; eauto].
  }
  eapply Hgen; [eapply red_sn; eauto|exact Harg].
Qed.

Lemma not_value_if : forall c a b, ~ value (tm_if c a b).
Proof. intros c a b H; inversion H. Qed.

Lemma step_preserves_lc : forall t u,
  t --> u -> locally_closed_tm t -> locally_closed_tm u.
Proof.
  intros t u Hstep. induction Hstep; intros Hlc; inversion Hlc; subst.
  - inversion H; subst. eapply open_tm_preserves_lc_at; eauto using value_regular.
  - constructor; [eapply IHHstep; eassumption|assumption].
  - constructor; [assumption|eapply IHHstep; eassumption].
  - inversion H; subst. eapply open_tm_ty_preserves_lc_at; eauto.
  - constructor; [eapply IHHstep; eassumption|assumption].
  - assumption.
  - assumption.
  - apply lc_tm_if; [apply IHHstep; exact H6|exact H7|exact H8].
Qed.

Lemma red_if : forall rho bs T c a b,
  red rho bs Ty_Bool c -> red rho bs T a -> red rho bs T b ->
  red rho bs T (tm_if c a b).
Proof.
  intros rho bs T c a b Hc Ha Hb.
  assert (Hgen : forall c, strongly_normalizing c -> red rho bs Ty_Bool c ->
      forall a b, red rho bs T a -> red rho bs T b ->
        red rho bs T (tm_if c a b)).
  { intros c0 Hsn. induction Hsn as [c0 Hnext IH].
    intros Hc0 a0 b0 Ha0 Hb0. eapply red_expand.
    - apply not_value_if.
    - intros u Hu. inversion Hu; subst.
      + exact Ha0.
      + exact Hb0.
      + eapply IH; [eassumption|eapply red_step; eauto|exact Ha0|exact Hb0]. }
  apply (Hgen c (red_sn rho bs Ty_Bool c Hc) Hc a b Ha Hb).
Qed.

Lemma red_app : forall rho bs A B f u,
  red rho bs (Ty_Arrow A B) f -> red rho bs A u ->
  locally_closed_tm u -> red rho bs B (tm_app f u).
Proof.
  intros rho bs A B f u Hf Hu Hlu.
  assert (Hgen : forall f, strongly_normalizing f -> red rho bs (Ty_Arrow A B) f ->
      forall u, strongly_normalizing u -> red rho bs A u -> locally_closed_tm u ->
        red rho bs B (tm_app f u)).
  { intros f0 Hsf. induction Hsf as [f0 Hnextf IHf].
    intros Hrf u0 Hsu Hru Hlu0.
    induction Hsu as [u0 Hnextu IHu].
    assert (Hsu0 : strongly_normalizing u0) by (constructor; exact Hnextu).
    eapply red_expand.
    - apply not_value_app.
    - intros q Hq. inversion Hq; subst.
      + match goal with
        | Hrf0 : red rho bs (Ty_Arrow A B) (tm_abs ?S ?body),
          Hlc0 : locally_closed_tm (tm_abs ?S ?body) |- _ =>
            destruct (red_terminal rho bs (Ty_Arrow A B) (tm_abs S body)
              (tm_abs S body) Hrf0 (multi_refl _) (v_abs S body Hlc0))
              as [S0 [body0 [E Hbody]]]; simpl in E; inversion E; subst;
              eapply Hbody; [exact Hlu0|exact Hru]
        end.
      + eapply IHf.
        * exact H1.
        * eapply red_step; eauto.
        * exact Hsu0.
        * exact Hru.
        * exact Hlu0.
      + eapply IHu.
        * match goal with Hst : u0 --> ?u1 |- _ => exact Hst end.
        * eapply red_step; eauto.
        * eapply step_preserves_lc; eauto.
  }
  eapply Hgen; [eapply red_sn; eauto|exact Hf|eapply red_sn; eauto|exact Hu|exact Hlu].
Qed.

Lemma red_tapp : forall rho bs T f U U',
  red rho bs (Ty_All T) f -> locally_closed_ty U -> locally_closed_ty U' -> lc_ty_at 1 T ->
  candidate_good (red rho bs U) ->
  red rho bs (open_ty T U) (tm_tapp f U').
Proof.
  intros rho bs T f U U' Hf HU HU' HlcT HQ.
  assert (Hgen : forall f, strongly_normalizing f -> red rho bs (Ty_All T) f ->
      red rho bs (open_ty T U) (tm_tapp f U')).
  { intros f0 Hsf. induction Hsf as [f0 Hnextf IHf]. intros Hrf.
    eapply red_expand.
    - intros Hv. inversion Hv.
    - intros q Hq. inversion Hq; subst.
      + destruct (red_terminal rho bs (Ty_All T) (tm_tabs t) (tm_tabs t)
          Hrf (multi_refl _) (v_tabs t H1)) as [body [E Hbody]].
        simpl in E. inversion E; subst body.
        specialize (Hbody U' (red rho bs U) HU' HQ).
        assert (Heqenv : forall i z,
          bound_insert bs 0 (red rho bs U) i z <->
          bound_update bs (red rho bs U) i z).
        { intros i z. destruct i; simpl; unfold bound_insert, bound_update; simpl; tauto. }
        apply (proj1 (red_open_ty_rec rho bs 0 U T (open_tm_ty t U') HU HlcT)).
        apply (proj2 (red_env_equiv rho
          (bound_insert bs 0 (red rho bs U))
          (bound_update bs (red rho bs U)) T (open_tm_ty t U')
          ltac:(intros i z Hv; apply Heqenv))).
        exact Hbody.
      + eapply IHf.
        * match goal with Hst : f0 --> ?f1 |- _ => exact Hst end.
        * eapply red_step; eauto.
  }
  eapply Hgen; [eapply red_sn; eauto|exact Hf].
Qed.

Lemma multi_trans : forall t u v,
  t -->* u -> u -->* v -> t -->* v.
Proof.
  intros t u v H. induction H; intros Huv.
  - exact Huv.
  - eapply multi_step; eauto.
Qed.

Lemma open_tm_rec_lc_closed : forall t k u,
  locally_closed_tm t -> open_tm_rec k u t = t.
Proof.
  intros t k u Hlc. apply (open_tm_rec_lc_at t 0 k u).
  eapply lc_tm_at_monotone; [exact Hlc|lia|lia].
Qed.

Lemma instantiate_open_tm_rec : forall t theta gamma x u k,
  ~ In x (fv_tm t) -> term_substitution_closed gamma -> locally_closed_tm u ->
  instantiate theta (term_subst_update gamma x u)
    (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k u (instantiate theta gamma t).
Proof.
  induction t; intros theta gamma x u k Hfresh Hgamma Hu; simpl in *.
  - destruct (Nat.eqb k n) eqn:E; simpl.
    + unfold term_subst_update. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - simpl in Hfresh. destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E. subst x. exfalso. apply Hfresh. simpl. auto.
    + unfold term_subst_update. rewrite E.
      symmetry. apply open_tm_rec_lc_closed. apply Hgamma.
  - f_equal. apply IHt; simpl in Hfresh; assumption.
  - f_equal.
    + eapply IHt1.
      * intro Hin. apply Hfresh. simpl. apply in_app_iff. left. exact Hin.
      * exact Hgamma.
      * exact Hu.
    + eapply IHt2.
      * intro Hin. apply Hfresh. simpl. apply in_app_iff. right. exact Hin.
      * exact Hgamma.
      * exact Hu.
  - f_equal. apply IHt; assumption.
  - f_equal. apply IHt; assumption.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + eapply IHt1.
      * intro Hin. apply Hfresh. simpl. apply in_app_iff. left. exact Hin.
      * exact Hgamma.
      * exact Hu.
    + eapply IHt2.
      * intro Hin. apply Hfresh. simpl. apply in_app_iff. right. apply in_app_iff. left. exact Hin.
      * exact Hgamma.
      * exact Hu.
    + eapply IHt3.
      * intro Hin. apply Hfresh. simpl. apply in_app_iff. right. apply in_app_iff. right. exact Hin.
      * exact Hgamma.
      * exact Hu.
Qed.

Lemma instantiate_ty_open_rec : forall T theta X U k,
  type_substitution_closed theta -> ~ In X (fv_ty T) ->
  instantiate_ty (type_subst_update theta X U)
    (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k U (instantiate_ty theta T).
Proof.
  induction T; intros theta X U k Htheta Hfresh; simpl in *.
  - destruct (Nat.eqb k n); simpl.
    + unfold type_subst_update. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - simpl in Hfresh. destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E. subst X. exfalso. apply Hfresh. simpl. auto.
    + unfold type_subst_update. rewrite E. symmetry.
      apply open_ty_rec_lc_at. eapply lc_ty_at_monotone.
      * apply Htheta.
      * lia.
  - f_equal.
    + apply IHT1; [exact Htheta|]. simpl in Hfresh. intro H. apply Hfresh. apply in_or_app. left. exact H.
    + apply IHT2; [exact Htheta|]. simpl in Hfresh. intro H. apply Hfresh. apply in_or_app. right. exact H.
  - f_equal. apply IHT; assumption.
  - reflexivity.
Qed.

Lemma instantiate_open_tm_ty_rec : forall t theta gamma X U k,
  type_substitution_closed theta -> locally_closed_ty U ->
  term_substitution_closed gamma -> ~ In X (ftv_tm t) ->
  instantiate (type_subst_update theta X U) gamma
    (open_tm_ty_rec k (Ty_FVar X) t) =
  open_tm_ty_rec k U (instantiate theta gamma t).
Proof.
  induction t; intros theta gamma X U k Htheta HU Hgamma Hfresh; simpl in *.
  - reflexivity.
  - symmetry. apply (open_tm_ty_rec_lc_at (gamma a) k 0 U).
    eapply lc_tm_at_monotone; [apply Hgamma|lia|lia].
  - f_equal.
    + apply instantiate_ty_open_rec; [exact Htheta|].
      simpl in Hfresh. intro Hin. apply Hfresh. apply in_or_app. left. exact Hin.
    + apply IHt; try assumption.
      simpl in Hfresh. intro Hin. apply Hfresh. apply in_or_app. right. exact Hin.
  - f_equal.
    + apply IHt1; try assumption.
      intro Hin. apply Hfresh. simpl. apply in_app_iff. left. exact Hin.
    + apply IHt2; try assumption.
      intro Hin. apply Hfresh. simpl. apply in_app_iff. right. exact Hin.
  - f_equal. apply IHt; assumption.
  - f_equal.
    + apply IHt; try assumption.
      intro Hin. apply Hfresh. simpl. apply in_app_iff. left. exact Hin.
    + apply instantiate_ty_open_rec; [exact Htheta|].
      intro Hin. apply Hfresh. simpl. apply in_app_iff. right. exact Hin.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply IHt1; try assumption.
      intro Hin. apply Hfresh. simpl. apply in_app_iff. left. exact Hin.
    + apply IHt2; try assumption.
      intro Hin. apply Hfresh. simpl. apply in_app_iff. right. apply in_app_iff. left. exact Hin.
    + apply IHt3; try assumption.
      intro Hin. apply Hfresh. simpl. apply in_app_iff. right. apply in_app_iff. right. exact Hin.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T Hwf. induction Hwf.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; assumption.
  - apply lc_ty_all. pose (X := fresh L).
    apply lc_ty_at_open_inv with (X:=X).
    apply H0. apply fresh_notin.
  - constructor.
Qed.

Lemma has_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T Hty. induction Hty.
  - constructor.
  - assert (Htype : locally_closed_ty T1) by (eapply wf_ty_lc; eauto).
    pose (x := fresh L).
    pose proof (lc_tm_at_open_tm_inv _ 0 0 x (H1 x (fresh_notin L))) as Hbody.
    apply lc_tm_abs; assumption.
  - constructor; assumption.
  - pose (X := fresh L).
    pose proof (lc_tm_at_open_ty_inv _ 0 0 X (H0 X (fresh_notin L))) as Hbody.
    apply lc_tm_tabs. exact Hbody.
  - constructor.
    + eapply IHHty.
    + eapply wf_ty_lc; eauto.
  - constructor.
  - constructor.
  - constructor; assumption.
Qed.

Lemma instantiate_ty_lc_at : forall T K theta,
  lc_ty_at K T -> type_substitution_closed theta ->
  lc_ty_at K (instantiate_ty theta T).
Proof.
  intros T K theta Hlc. induction Hlc; intros Htheta; simpl.
  - apply lc_ty_bvar. assumption.
  - eapply lc_ty_at_monotone; [apply Htheta|lia].
  - apply lc_ty_arrow; eauto.
  - apply lc_ty_all. apply IHHlc. exact Htheta.
  - constructor.
Qed.

Lemma instantiate_lc_at : forall t K k theta gamma,
  lc_tm_at K k t -> type_substitution_closed theta ->
  term_substitution_closed gamma ->
  lc_tm_at K k (instantiate theta gamma t).
Proof.
  intros t K k theta gamma Hlc. induction Hlc; intros Htheta Hgamma; simpl.
  - apply lc_tm_bvar. assumption.
  - eapply lc_tm_at_monotone; [apply Hgamma|lia|lia].
  - apply lc_tm_abs.
    + eapply instantiate_ty_lc_at; eauto.
    + eapply IHHlc; eauto.
  - apply lc_tm_app; eauto.
  - apply lc_tm_tabs. eapply IHHlc; eauto.
  - apply lc_tm_tapp.
    + eapply IHHlc; eauto.
    + eapply instantiate_ty_lc_at; eauto.
  - constructor.
  - constructor.
  - apply lc_tm_if; eauto.
Qed.

Lemma lookup_fv_context : forall Gamma x S Y,
  lookup_context x Gamma = Some S -> In Y (fv_ty S) -> In Y (ftv_context Gamma).
Proof.
  induction Gamma as [|[z A] Gamma IH]; intros x S Y Hlook Hin; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x z) eqn:E.
    + inversion Hlook; subst. apply in_or_app. left. exact Hin.
    + apply in_or_app. right. eapply IH; eauto.
Qed.

Lemma has_type_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_ty T.
Proof.
  intros Delta Gamma t T Hty. induction Hty.
  - eapply wf_ty_lc; eauto.
  - apply lc_ty_arrow.
    + eapply wf_ty_lc; eauto.
    + pose (x := fresh L). apply (H1 x (fresh_notin L)).
  - inversion IHHty1; assumption.
  - pose (X := fresh L).
    pose proof (H0 X (fresh_notin L)) as Hopen.
    eapply lc_ty_all. eapply lc_ty_at_open_inv with (X:=X). exact Hopen.
  - inversion IHHty; subst. apply lc_ty_at_open.
    + assumption.
    + eapply wf_ty_lc; eauto.
  - constructor.
  - constructor.
  - exact IHHty2.
Qed.

Lemma sn_if : forall c a b,
  strongly_normalizing c -> strongly_normalizing a ->
  strongly_normalizing b -> strongly_normalizing (tm_if c a b).
Proof.
  intros c a b Hc. revert a b.
  induction Hc as [c Hc IH]; intros a b Ha Hb.
  apply SN_intro. intros u Hstep. inversion Hstep; subst.
  - assumption.
  - assumption.
  - apply IH; assumption.
Qed.

Definition sem_context (rho : candidate_env) (bs : bound_candidate_env)
    (Gamma : context) (gamma : term_substitution) : Prop :=
  forall x T, lookup_context x Gamma = Some T -> red rho bs T (gamma x).

Lemma red_free_update_value : forall rho bs X Q v,
  value v ->
  (red (free_update rho X Q) bs (Ty_FVar X) v <-> Q v).
Proof.
  intros rho bs X Q v Hv.
  rewrite (red_value (free_update rho X Q) bs (Ty_FVar X) v Hv).
  simpl. unfold free_update. rewrite Nat.eqb_refl. split.
  - intros [_ HQ]. exact HQ.
  - intro HQ. split; [apply sn_value; exact Hv|exact HQ].
Qed.

Lemma fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall rho bs theta gamma,
    type_substitution_closed theta -> term_substitution_closed gamma ->
    sem_context rho bs Gamma gamma ->
    red rho bs T (instantiate theta gamma t).
Proof.
  intros Delta Gamma t T Hty. induction Hty;
    intros rho bs theta gamma Htheta Hgamma Hsem; simpl.
  - eapply Hsem; eauto.
  - eapply red_abs.
    + eapply instantiate_lc_at with (t:=tm_abs T1 t2) (K:=0) (k:=0)
        (theta:=theta) (gamma:=gamma).
      * eapply has_type_lc. econstructor; eauto.
      * exact Htheta.
      * exact Hgamma.
    + intros u Hu Hru.
      set (x := fresh (L ++ fv_tm t2 ++ dom_context Gamma)).
      assert (HxL : ~ In x L).
      { unfold x. intro Hin. apply (fresh_notin (L ++ fv_tm t2 ++ dom_context Gamma)).
        apply in_or_app. left. exact Hin. }
      assert (Hxbody : ~ In x (fv_tm t2)).
      { unfold x. intro Hin. apply (fresh_notin (L ++ fv_tm t2 ++ dom_context Gamma)).
        apply in_or_app. right. apply in_or_app. left. exact Hin. }
      assert (Hxdom : ~ In x (dom_context Gamma)).
      { unfold x. intro Hin. apply (fresh_notin (L ++ fv_tm t2 ++ dom_context Gamma)).
        apply in_or_app. right. apply in_or_app. right. exact Hin. }
      assert (Hsemx : sem_context rho bs (update Gamma x T1)
          (term_subst_update gamma x u)).
      { intros y S Hlook. unfold update in Hlook. simpl in Hlook.
        destruct (Nat.eqb y x) eqn:E.
        - apply Nat.eqb_eq in E. subst y.
          inversion Hlook; subst. unfold term_subst_update. rewrite Nat.eqb_refl. exact Hru.
        - apply Nat.eqb_neq in E.
          unfold term_subst_update.
          assert (E' : Nat.eqb x y = false) by (apply Nat.eqb_neq; congruence).
          rewrite E'. eapply Hsem; eauto. }
      specialize (H1 x HxL rho bs theta (term_subst_update gamma x u)
        Htheta (term_subst_update_closed gamma x u Hgamma Hu) Hsemx).
      unfold open_tm in H1 |- *.
      rewrite (instantiate_open_tm_rec t2 theta gamma x u 0
        Hxbody Hgamma Hu) in H1.
      exact H1.
  - eapply red_app.
    + exact (IHHty1 rho bs theta gamma Htheta Hgamma Hsem).
    + exact (IHHty2 rho bs theta gamma Htheta Hgamma Hsem).
    + eapply instantiate_lc_at with (t:=t2) (K:=0) (k:=0)
        (theta:=theta) (gamma:=gamma).
      * eapply has_type_lc; exact Hty2.
      * exact Htheta.
      * exact Hgamma.
  - eapply red_tabs.
    + eapply instantiate_lc_at with (t:=tm_tabs t) (K:=0) (k:=0)
        (theta:=theta) (gamma:=gamma).
      * eapply has_type_lc. econstructor; eauto.
      * exact Htheta.
      * exact Hgamma.
    + intros U Q HU HQ.
      set (X := fresh (L ++ ftv_context Gamma ++ ftv_tm t ++ fv_ty T)).
      assert (HX_L : ~ In X L).
      { unfold X. intro Hin. apply (fresh_notin (L ++ ftv_context Gamma ++ ftv_tm t ++ fv_ty T)).
        apply in_or_app. left. exact Hin. }
      assert (HX_ctx : ~ In X (ftv_context Gamma)).
      { unfold X. intro Hin. apply (fresh_notin (L ++ ftv_context Gamma ++ ftv_tm t ++ fv_ty T)).
        apply in_or_app. right. apply in_or_app. left. exact Hin. }
      assert (HX_tm : ~ In X (ftv_tm t)).
      { unfold X. intro Hin. apply (fresh_notin (L ++ ftv_context Gamma ++ ftv_tm t ++ fv_ty T)).
        apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hin. }
      assert (HX_ty : ~ In X (fv_ty T)).
      { unfold X. intro Hin. apply (fresh_notin (L ++ ftv_context Gamma ++ ftv_tm t ++ fv_ty T)).
        apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact Hin. }
      assert (Hsem' : sem_context (free_update rho X Q) bs Gamma gamma).
      { intros y S Hlook.
        apply (proj2 (red_fv_irrel rho bs X Q S (gamma y)
          ltac:(intro Hin; apply HX_ctx; eapply lookup_fv_context; eauto))).
        eapply Hsem; eauto. }
      specialize (H0 X HX_L (free_update rho X Q) bs
        (type_subst_update theta X U) gamma
        (type_subst_update_closed theta X U Htheta HU) Hgamma Hsem').
      unfold open_tm_ty in H0.
      rewrite (instantiate_open_tm_ty_rec t theta gamma X U 0
        Htheta HU Hgamma HX_tm) in H0.
      pose proof (has_type_type_lc _ _ _ _ (H X HX_L)) as Hopenlc.
      pose proof (lc_ty_at_open_inv T 0 X Hopenlc) as Hbodylc.
      apply (proj1 (red_fv_irrel rho (bound_update bs Q) X Q T
        (open_tm_ty (instantiate theta gamma t) U) HX_ty)).
      apply (proj1 (red_env_equiv (free_update rho X Q)
        (bound_insert bs 0 (red (free_update rho X Q) bs (Ty_FVar X)))
        (bound_update bs Q) T (open_tm_ty (instantiate theta gamma t) U)
        ltac:(intros i z Hv; destruct i; simpl; unfold bound_insert, bound_update;
          simpl; [apply red_free_update_value with (rho:=rho) (bs:=bs) (X:=X) (Q:=Q); exact Hv|tauto]))).
      apply (proj2 (red_open_ty_rec (free_update rho X Q) bs 0
        (Ty_FVar X) T (open_tm_ty (instantiate theta gamma t) U)
        (lc_ty_fvar 0 X) Hbodylc)).
      exact H0.
  - pose proof (has_type_type_lc _ _ _ _ Hty) as Halllc.
    assert (Hbodylc : lc_ty_at 1 T).
    { inversion Halllc; subst; assumption. }
    eapply red_tapp with (U:=U) (U':=instantiate_ty theta U).
    + exact (IHHty rho bs theta gamma Htheta Hgamma Hsem).
    + eapply wf_ty_lc; eauto.
    + eapply instantiate_ty_lc_at with (K:=0).
      * eapply wf_ty_lc; exact H.
      * exact Htheta.
    + exact Hbodylc.
    + intros z Hz. exact (red_sn rho bs U z Hz).
  - exact (red_bool_true rho bs).
  - exact (red_bool_false rho bs).
  - eapply red_if; eauto.
Qed.

Lemma instantiate_ty_id : forall T,
  instantiate_ty (fun X => Ty_FVar X) T = T.
Proof.
  induction T; simpl; try rewrite IHT1; try rewrite IHT2; try rewrite IHT; reflexivity.
Qed.

Lemma instantiate_tm_id : forall t,
  instantiate (fun X => Ty_FVar X) (fun x => tm_fvar x) t = t.
Proof.
  induction t; simpl; try rewrite instantiate_ty_id;
    try rewrite IHt; try rewrite IHt1; try rewrite IHt2; try rewrite IHt3; reflexivity.
Qed.

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  intros t T Hty.
  assert (Htheta : type_substitution_closed (fun X => Ty_FVar X)).
  { intros X. constructor. }
  assert (Hgamma : term_substitution_closed (fun x => tm_fvar x)).
  { intros x. constructor. }
  assert (Hsem : sem_context (fun _ => sn_candidate) (fun _ => sn_candidate)
      empty (fun x => tm_fvar x)).
  { intros x U Hlookup. discriminate. }
  pose proof (fundamental [] empty t T Hty
    (fun _ => sn_candidate) (fun _ => sn_candidate)
    (fun X => Ty_FVar X) (fun x => tm_fvar x) Htheta Hgamma Hsem) as Hred.
  rewrite instantiate_tm_id in Hred.
  eapply red_sn. exact Hred.
Qed.

End SystemFNormalizationIfEasyTask.
