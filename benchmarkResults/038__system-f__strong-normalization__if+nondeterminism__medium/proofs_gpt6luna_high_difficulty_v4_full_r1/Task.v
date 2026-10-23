(** System F CBV strong-normalization benchmark, Easy variant.
    Features: if-nondeterminism. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFNormalizationIfNondeterminismEasyTask.

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
  | tm_if : tm -> tm -> tm -> tm
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

Notation "'Bool'" := Ty_Bool (in custom systemf_ty at level 0) : systemf_scope.
Notation "'true'" := tm_true (in custom systemf_tm at level 0) : systemf_scope.
Notation "'false'" := tm_false (in custom systemf_tm at level 0) : systemf_scope.
Notation "'if' t1 'then' t2 'else' t3" := (tm_if t1 t2 t3)
  (in custom systemf_tm at level 200, t1 custom systemf_tm, t2 custom systemf_tm, t3 custom systemf_tm at level 200) : systemf_scope.
Notation "'choice' t1 'or' t2" := (tm_choice t1 t2)
  (in custom systemf_tm at level 200, t1 custom systemf_tm, t2 custom systemf_tm at level 200) : systemf_scope.

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
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (open_tm_ty_rec k U t1) (open_tm_ty_rec k U t2) (open_tm_ty_rec k U t3)
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
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (tm_subst x s t1) (tm_subst x s t2) (tm_subst x s t3)
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
      lc_tm_at K k t1 -> lc_tm_at K k t2 -> lc_tm_at K k t3 -> lc_tm_at K k (tm_if t1 t2 t3)
  | lc_tm_choice : forall K k t1 t2,
      lc_tm_at K k t1 -> lc_tm_at K k t2 -> lc_tm_at K k (tm_choice t1 t2).

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
      has_type Delta Gamma (tm_if t1 t2 t3) T
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
  | tm_choice t1 t2 => fv_tm t1 ++ fv_tm t2
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

Lemma multi_trans : forall t u v,
  t -->* u -> u -->* v -> t -->* v.
Proof.
  intros t u v H. induction H; intros Huv.
  - exact Huv.
  - econstructor; eauto.
Qed.

Lemma multi_step_left : forall t u v,
  t --> u -> u -->* v -> t -->* v.
Proof. intros. econstructor; eauto. Qed.

Lemma lc_step : forall t u,
  locally_closed_tm t -> t --> u -> locally_closed_tm u.
Proof.
  intros t u Hlc Hs. revert Hlc. induction Hs; intros Hlc;
    inversion Hlc; subst.
  - unfold locally_closed_tm in H5. inversion H5; subst.
    eapply open_tm_preserves_lc_at; eauto using value_regular.
  - apply lc_tm_app; [eapply IHHs; eauto|assumption].
  - apply lc_tm_app; [assumption|eapply IHHs; eauto].
  - unfold locally_closed_tm in H5. inversion H5; subst.
    eapply open_tm_ty_preserves_lc_at; eauto.
  - apply lc_tm_tapp; [eapply IHHs; eauto|assumption].
  - assumption.
  - assumption.
  - apply lc_tm_if; [eapply IHHs; eauto|assumption|assumption].
  - assumption.
  - assumption.
Qed.

Record reducibility_candidate : Type := mk_candidate {
  candidate_pred : tm -> Prop;
  candidate_sn : forall t, candidate_pred t -> strongly_normalizing t;
  candidate_lc : forall t, candidate_pred t -> locally_closed_tm t;
  candidate_step : forall t u, candidate_pred t -> t --> u -> candidate_pred u;
  candidate_expand : forall t,
    locally_closed_tm t -> ~ value t ->
    (forall u, t --> u -> candidate_pred u) -> candidate_pred t
}.

Definition bool_sat_candidate : reducibility_candidate.
Proof.
  refine (mk_candidate
    (fun t => locally_closed_tm t /\ strongly_normalizing t /\
      (forall v, value v -> t -->* v -> v = tm_true \/ v = tm_false)) _ _ _ _).
  - intros t [_ [Hsn _]]. exact Hsn.
  - intros t [Hlc _]. exact Hlc.
  - intros t u [Hlc [Hsn Hcan]] Hs. split.
    + eapply lc_step; eauto.
    + split.
      * inversion Hsn; eauto.
      * intros v Hv Huv. apply Hcan; [exact Hv|].
        eapply multi_step_left; eauto.
  - intros t Hlc Hnot Hsteps. split; [exact Hlc|]. split.
    + constructor. intros u Hs. destruct (Hsteps u Hs) as [_ [Hsn _]]. exact Hsn.
    + intros v Hv Hmulti. inversion Hmulti; subst.
      * exfalso. apply Hnot. exact Hv.
      * destruct (Hsteps y H) as [_ [_ Hcan]]. eapply Hcan; eauto.
Defined.

Definition xi_update (xi : atom -> reducibility_candidate)
    (X : atom) (C : reducibility_candidate) : atom -> reducibility_candidate :=
  fun Y => if Nat.eqb X Y then C else xi Y.

Fixpoint reducible (xi : atom -> reducibility_candidate)
    (beta : list reducibility_candidate) (T : ty) (t : tm) : Prop :=
  match T with
  | Ty_BVar i =>
      match nth_error beta i with
      | Some C => candidate_pred C t
      | None => candidate_pred bool_sat_candidate t
      end
  | Ty_FVar X => candidate_pred (xi X) t
  | Ty_Arrow A B =>
      locally_closed_tm t /\ strongly_normalizing t /\
      (forall v, value v -> t -->* v ->
        exists U body, v = tm_abs U body /\
          forall u, reducible xi beta A u ->
            reducible xi beta B (tm_app v u))
  | Ty_All T1 =>
      locally_closed_tm t /\ strongly_normalizing t /\
      (forall v, value v -> t -->* v ->
        exists body, v = tm_tabs body /\
          forall U, locally_closed_ty U ->
          forall C : reducibility_candidate,
            reducible xi (C :: beta) T1 (tm_tapp v U))
  | Ty_Bool =>
      locally_closed_tm t /\ strongly_normalizing t /\
      (forall v, value v -> t -->* v -> v = tm_true \/ v = tm_false)
  end.

Lemma bool_reducible_candidate : forall (xi : atom -> reducibility_candidate)
    (beta : list reducibility_candidate),
  reducibility_candidate.
Proof.
  intros xi beta. refine (mk_candidate
    (fun t => locally_closed_tm t /\ strongly_normalizing t /\
      (forall v, value v -> t -->* v -> v = tm_true \/ v = tm_false)) _ _ _ _).
  - intros t [_ [Hsn _]]. exact Hsn.
  - intros t [Hlc _]. exact Hlc.
  - intros t u [Hlc [Hsn Hcan]] Hs. split.
    + eapply lc_step; eauto.
    + split.
      * inversion Hsn; eauto.
      * intros v Hv Huv. apply Hcan; [exact Hv|].
        eapply multi_step_left; eauto.
  - intros t Hlc Hnot Hsteps. split; [exact Hlc|].
    split.
    + constructor. intros u Hs. destruct (Hsteps u Hs) as [_ [Hsn _]]. exact Hsn.
    + intros v Hv Hmulti.
      inversion Hmulti; subst.
      * exfalso. apply Hnot. exact Hv.
      * destruct (Hsteps y H) as [_ [_ Hcan]].
        eapply Hcan; eauto.
Qed.

Lemma reducible_candidate : forall (xi : atom -> reducibility_candidate)
    (beta : list reducibility_candidate) (T : ty),
  reducibility_candidate.
Proof.
  intros xi beta T. revert beta.
  induction T as [n|X|A IHA B IHB|A IHA|]; intros beta.
  - destruct (nth_error beta n) as [C|] eqn:E.
    + exact C.
    + exact bool_sat_candidate.
  - exact (xi X).
  - refine (mk_candidate
      (fun t => locally_closed_tm t /\ strongly_normalizing t /\
        (forall v, value v -> t -->* v ->
          exists U body, v = tm_abs U body /\
            forall u, reducible xi beta A u ->
              reducible xi beta B (tm_app v u))) _ _ _ _).
    + intros t [_ [Hsn _]]. exact Hsn.
    + intros t [Hlc _]. exact Hlc.
    + intros t u [Hlc [Hsn Hcan]] Hs. split.
      * eapply lc_step; eauto.
      * split; [inversion Hsn; eauto|].
        intros v Hv Huv. apply Hcan; [exact Hv|].
        eapply multi_step_left; eauto.
    + intros t Hlc Hnot Hsteps. split; [exact Hlc|].
      split; [constructor; intros u Hs; destruct (Hsteps u Hs) as [_ [Hsn _]]; exact Hsn|].
      intros v Hv Hmulti. inversion Hmulti; subst.
      * exfalso. apply Hnot. exact Hv.
      * destruct (Hsteps y H) as [_ [_ Hcan]].
        eapply Hcan; eauto.
  - refine (mk_candidate
      (fun t => locally_closed_tm t /\ strongly_normalizing t /\
        (forall v, value v -> t -->* v ->
          exists body, v = tm_tabs body /\
            forall U, locally_closed_ty U -> forall C : reducibility_candidate,
              reducible xi (C :: beta) A (tm_tapp v U))) _ _ _ _).
    + intros t [_ [Hsn _]]. exact Hsn.
    + intros t [Hlc _]. exact Hlc.
    + intros t u [Hlc [Hsn Hcan]] Hs. split.
      * eapply lc_step; eauto.
      * split; [inversion Hsn; eauto|].
        intros v Hv Huv. apply Hcan; [exact Hv|].
        eapply multi_step_left; eauto.
    + intros t Hlc Hnot Hsteps. split; [exact Hlc|].
      split; [constructor; intros u Hs; destruct (Hsteps u Hs) as [_ [Hsn _]]; exact Hsn|].
      intros v Hv Hmulti. inversion Hmulti; subst.
      * exfalso. apply Hnot. exact Hv.
      * destruct (Hsteps y H) as [_ [_ Hcan]].
        eapply Hcan; eauto.
  - exact bool_sat_candidate.
Defined.

Lemma reducible_regular : forall xi beta T t,
  reducible xi beta T t -> locally_closed_tm t /\ strongly_normalizing t.
Proof.
  intros xi beta T. induction T as [n|X|A IHA B IHB|A IHA|]; intros t H; simpl in H.
  - destruct (nth_error beta n) as [C|] eqn:E; simpl in H.
    + split; [exact (candidate_lc C t H)|exact (candidate_sn C t H)].
    + split; [exact (candidate_lc bool_sat_candidate t H)|
        exact (candidate_sn bool_sat_candidate t H)].
  - split; [exact (candidate_lc (xi X) t H)|exact (candidate_sn (xi X) t H)].
  - tauto.
  - tauto.
  - tauto.
Qed.

Lemma reducible_step : forall xi beta T t u,
  reducible xi beta T t -> t --> u -> reducible xi beta T u.
Proof.
  intros xi beta T. induction T as [n|X|A IHA B IHB|A IHA|];
    intros t u Hr Hs; simpl in *.
  - destruct (nth_error beta n) as [C|] eqn:E.
    + exact (candidate_step C t u Hr Hs).
    + exact (candidate_step bool_sat_candidate t u Hr Hs).
  - eapply candidate_step; eauto.
  - destruct Hr as [Hlc [Hsn Hcan]]. split.
    + eapply lc_step; eauto.
    + split.
      * inversion Hsn; eauto.
      * intros v Hv Huv. eapply Hcan; [exact Hv|].
        eapply multi_step_left; eauto.
  - destruct Hr as [Hlc [Hsn Hcan]]. split.
    + eapply lc_step; eauto.
    + split.
      * inversion Hsn; eauto.
      * intros v Hv Huv. eapply Hcan; [exact Hv|].
        eapply multi_step_left; eauto.
  - destruct Hr as [Hlc [Hsn Hcan]]. split.
    + eapply lc_step; eauto.
    + split.
      * inversion Hsn; eauto.
      * intros v Hv Huv. eapply Hcan; [exact Hv|].
        eapply multi_step_left; eauto.
Qed.

Lemma reducible_expand : forall xi beta T t,
  locally_closed_tm t -> ~ value t ->
  (forall u, t --> u -> reducible xi beta T u) ->
  reducible xi beta T t.
Proof.
  intros xi beta T. induction T as [n|X|A IHA B IHB|A IHA|];
    intros t Hlc Hnv Hsteps; simpl.
  - destruct (nth_error beta n) as [C|] eqn:E.
    + apply (candidate_expand C t Hlc Hnv). intros u Hs.
      specialize (Hsteps u Hs). simpl in Hsteps. rewrite E in Hsteps. exact Hsteps.
    + apply (candidate_expand bool_sat_candidate t Hlc Hnv). intros u Hs.
      pose proof (Hsteps u Hs) as Hru. cbn [reducible] in Hru.
      rewrite E in Hru. exact Hru.
  - eapply candidate_expand; eauto.
  - split; [exact Hlc|]. split.
    + constructor. intros u Hs.
      destruct (reducible_regular xi beta (Ty_Arrow A B) u (Hsteps u Hs)) as [_ Hsn].
      exact Hsn.
    + intros v Hv Hmulti. inversion Hmulti; subst.
      * exfalso. apply Hnv. exact Hv.
      * destruct (Hsteps y H) as [_ [_ Hcan]].
        eapply Hcan; eauto.
  - split; [exact Hlc|]. split.
    + constructor. intros u Hs.
      destruct (reducible_regular xi beta (Ty_All A) u (Hsteps u Hs)) as [_ Hsn].
      exact Hsn.
    + intros v Hv Hmulti. inversion Hmulti; subst.
      * exfalso. apply Hnv. exact Hv.
      * destruct (Hsteps y H) as [_ [_ Hcan]].
        eapply Hcan; eauto.
  - split; [exact Hlc|]. split.
    + constructor. intros u Hs.
      destruct (reducible_regular xi beta Ty_Bool u (Hsteps u Hs)) as [_ Hsn].
      exact Hsn.
    + intros v Hv Hmulti. inversion Hmulti; subst.
      * exfalso. apply Hnv. exact Hv.
      * destruct (Hsteps y H) as [_ [_ Hcan]].
        eapply Hcan; eauto.
Qed.

Lemma reducible_as_candidate : forall xi beta T t,
  reducible xi beta T t <->
  candidate_pred (reducible_candidate xi beta T) t.
Proof.
  intros xi beta T. revert beta. induction T as [n|X|A IHA B IHB|A IHA|]; intros beta t; simpl.
  - destruct (nth_error beta n); simpl; tauto.
  - reflexivity.
  - cbn [reducible_candidate]. reflexivity.
  - cbn [reducible_candidate]. reflexivity.
  - cbn [reducible_candidate]. reflexivity.
Qed.

Lemma reducible_beta_append : forall xi beta T gamma t,
  lc_ty_at (length beta) T ->
  (reducible xi (beta ++ gamma) T t <-> reducible xi beta T t).
Proof.
  intros xi beta T. revert beta. induction T as [n|X|A IHA B IHB|A IHA|];
    intros beta gamma t Hlc; simpl in *.
  - inversion Hlc; subst. destruct (nth_error beta n) as [C|] eqn:E.
    + assert (E': nth_error (beta ++ gamma) n = Some C).
      { rewrite nth_error_app1; [exact E|lia]. }
      rewrite E'. tauto.
    + assert (n < length beta) as Hbound by lia.
      assert (nth_error beta n <> None) as Hne.
      { apply nth_error_Some. exact Hbound. }
      contradiction.
  - tauto.
  - inversion Hlc; subst.
    split.
    + intros [Hclosed [Hsn Hcan]]. split; [exact Hclosed|]. split; [exact Hsn|].
      intros v Hv Hmulti. destruct (Hcan v Hv Hmulti) as [U [body [E Hfun]]].
      exists U, body. split; [exact E|]. intros u Hu.
      apply (proj1 (IHB beta gamma (tm_app v u) H3)).
      apply Hfun. apply (proj2 (IHA beta gamma u H2)). exact Hu.
    + intros [Hclosed [Hsn Hcan]]. split; [exact Hclosed|]. split; [exact Hsn|].
      intros v Hv Hmulti. destruct (Hcan v Hv Hmulti) as [U [body [E Hfun]]].
      exists U, body. split; [exact E|]. intros u Hu.
      apply (proj2 (IHB beta gamma (tm_app v u) H3)).
      apply Hfun. apply (proj1 (IHA beta gamma u H2)). exact Hu.
  - inversion Hlc; subst. split.
    + intros [Hclosed [Hsn Hcan]]. split; [exact Hclosed|]. split; [exact Hsn|].
      intros v Hv Hmulti. destruct (Hcan v Hv Hmulti) as [body [E Hfun]].
      exists body. split; [exact E|]. intros U HU C.
      apply (proj1 (IHA (C :: beta) gamma (tm_tapp v U) H1)).
      apply Hfun; assumption.
    + intros [Hclosed [Hsn Hcan]]. split; [exact Hclosed|]. split; [exact Hsn|].
      intros v Hv Hmulti. destruct (Hcan v Hv Hmulti) as [body [E Hfun]].
      exists body. split; [exact E|]. intros U HU C.
      apply (proj2 (IHA (C :: beta) gamma (tm_tapp v U) H1)).
      apply Hfun; assumption.
  - tauto.
Qed.

Lemma reducible_xi_update_irrelevant : forall xi X C beta T t,
  ~ In X (fv_ty T) ->
  (reducible (xi_update xi X C) beta T t <-> reducible xi beta T t).
Proof.
  intros xi X C beta T. revert beta. induction T as [n|Y|A IHA B IHB|A IHA|];
    intros beta t Hnot; simpl in *.
  - tauto.
  - destruct (Nat.eqb X Y) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply Hnot. simpl. auto.
    + unfold xi_update. rewrite E. reflexivity.
  - assert (HA : ~ In X (fv_ty A)).
    { intro Hin. apply Hnot. apply in_or_app. left. exact Hin. }
    assert (HB : ~ In X (fv_ty B)).
    { intro Hin. apply Hnot. apply in_or_app. right. exact Hin. }
    split.
    + intros [Hlc [Hsn Hcan]]. split; [exact Hlc|]. split; [exact Hsn|].
      intros v Hv Hmulti. destruct (Hcan v Hv Hmulti) as [U [body [E Hfun]]].
      exists U, body. split; [exact E|]. intros u Hu.
      apply (proj1 (IHB beta (tm_app v u) HB)).
      apply Hfun. apply (proj2 (IHA beta u HA)). exact Hu.
    + intros [Hlc [Hsn Hcan]]. split; [exact Hlc|]. split; [exact Hsn|].
      intros v Hv Hmulti. destruct (Hcan v Hv Hmulti) as [U [body [E Hfun]]].
      exists U, body. split; [exact E|]. intros u Hu.
      apply (proj2 (IHB beta (tm_app v u) HB)).
      apply Hfun. apply (proj1 (IHA beta u HA)). exact Hu.
  - split.
    + intros [Hlc [Hsn Hcan]]. split; [exact Hlc|]. split; [exact Hsn|].
      intros v Hv Hmulti. destruct (Hcan v Hv Hmulti) as [body [E Hfun]].
      exists body. split; [exact E|]. intros U HU D.
      apply (proj1 (IHA (D :: beta) (tm_tapp v U) Hnot)).
      apply Hfun; assumption.
    + intros [Hlc [Hsn Hcan]]. split; [exact Hlc|]. split; [exact Hsn|].
      intros v Hv Hmulti. destruct (Hcan v Hv Hmulti) as [body [E Hfun]].
      exists body. split; [exact E|]. intros U HU D.
      apply (proj2 (IHA (D :: beta) (tm_tapp v U) Hnot)).
      apply Hfun; assumption.
  - tauto.
Qed.

Lemma reducible_open_ty_rec : forall xi k beta T U t,
  length beta = k -> locally_closed_ty U ->
  (reducible xi beta (open_ty_rec k U T) t <->
   reducible xi (beta ++ [reducible_candidate xi [] U]) T t).
Proof.
  intros xi k beta T. revert k beta.
  induction T as [i|X|A IHA B IHB|A IHA|];
    intros k beta U t Hlen HU; simpl in *.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst i.
      assert (Hnth : nth_error (beta ++ [reducible_candidate xi [] U]) k =
          Some (reducible_candidate xi [] U)).
      { rewrite nth_error_app2; [|lia]. rewrite Hlen. rewrite Nat.sub_diag. simpl. reflexivity. }
      rewrite Hnth.
      pose proof (reducible_beta_append xi [] U beta t HU) as Hb.
      pose proof (reducible_as_candidate xi [] U t) as Hc. tauto.
    + apply Nat.eqb_neq in E. destruct (Nat.lt_ge_cases i k) as [Hbound|Hge].
      * assert (Hnth : nth_error (beta ++ [reducible_candidate xi [] U]) i = nth_error beta i).
        { rewrite nth_error_app1; [reflexivity|]. rewrite Hlen. exact Hbound. }
        rewrite Hnth. destruct (nth_error beta i) as [D|] eqn:Ebeta;
          cbn [reducible]; rewrite Ebeta; reflexivity.
      * assert (Hgt : k < i) by lia.
        assert (Enone : nth_error beta i = None).
        { apply nth_error_None. rewrite Hlen. lia. }
        assert (Eapp : nth_error (beta ++ [reducible_candidate xi [] U]) i = None).
        { apply nth_error_None. rewrite app_length, Hlen. simpl. lia. }
        rewrite Eapp. cbn [reducible]. rewrite Enone. reflexivity.
  - tauto.
  - split.
    + intros [Hlc [Hsn Hcan]]. split; [exact Hlc|]. split; [exact Hsn|].
      intros v Hv Hmulti. destruct (Hcan v Hv Hmulti) as [V [body [E Hfun]]].
      exists V, body. split; [exact E|]. intros u Hu.
      apply (proj1 (IHB k beta U (tm_app v u) Hlen HU)).
      apply Hfun. apply (proj2 (IHA k beta U u Hlen HU)). exact Hu.
    + intros [Hlc [Hsn Hcan]]. split; [exact Hlc|]. split; [exact Hsn|].
      intros v Hv Hmulti. destruct (Hcan v Hv Hmulti) as [V [body [E Hfun]]].
      exists V, body. split; [exact E|]. intros u Hu.
      apply (proj2 (IHB k beta U (tm_app v u) Hlen HU)).
      apply Hfun. apply (proj1 (IHA k beta U u Hlen HU)). exact Hu.
  - split.
    + intros [Hlc [Hsn Hcan]]. split; [exact Hlc|]. split; [exact Hsn|].
      intros v Hv Hmulti. destruct (Hcan v Hv Hmulti) as [body [E Hfun]].
      exists body. split; [exact E|]. intros V HV D.
      assert (Hlen' : length (D :: beta) = S k) by (simpl; lia).
      apply (proj1 (IHA (S k) (D :: beta) U (tm_tapp v V) Hlen' HU)).
      apply Hfun; assumption.
    + intros [Hlc [Hsn Hcan]]. split; [exact Hlc|]. split; [exact Hsn|].
      intros v Hv Hmulti. destruct (Hcan v Hv Hmulti) as [body [E Hfun]].
      exists body. split; [exact E|]. intros V HV D.
      assert (Hlen' : length (D :: beta) = S k) by (simpl; lia).
      apply (proj2 (IHA (S k) (D :: beta) U (tm_tapp v V) Hlen' HU)).
      apply Hfun; assumption.
  - tauto.
Qed.

Lemma wf_ty_lc : forall Delta T,
  wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T Hwf. induction Hwf.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; assumption.
  - apply lc_ty_all. specialize (H0 (fresh L) (fresh_notin L)).
    eapply lc_ty_at_open_inv with (k:=0) (X:=fresh L). exact H0.
  - apply lc_ty_bool.
Qed.

Lemma has_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T Hty. induction Hty.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + eapply wf_ty_lc; eauto.
    + specialize (H1 (fresh L) (fresh_notin L)).
      eapply lc_tm_at_open_tm_inv with (K:=0) (k:=0) (x:=fresh L). exact H1.
  - apply lc_tm_app; assumption.
  - apply lc_tm_tabs.
    specialize (H0 (fresh L) (fresh_notin L)).
    eapply lc_tm_at_open_ty_inv with (K:=0) (k:=0) (X:=fresh L). exact H0.
  - apply lc_tm_tapp; [assumption|eapply wf_ty_lc; eauto].
  - apply lc_tm_true.
  - apply lc_tm_false.
  - apply lc_tm_if; assumption.
  - apply lc_tm_choice; assumption.
Qed.

Lemma instantiate_ty_lc_at : forall theta K T,
  type_substitution_closed theta -> lc_ty_at K T ->
  lc_ty_at K (instantiate_ty theta T).
Proof.
  intros theta K T Htheta Hlc. revert K Hlc.
  induction T; intros K Hlc; simpl in *.
  - inversion Hlc; subst. apply lc_ty_bvar. assumption.
  - apply lc_ty_at_monotone with (k:=0); [apply Htheta|lia].
  - inversion Hlc; subst. apply lc_ty_arrow; eauto.
  - inversion Hlc; subst. apply lc_ty_all. eapply IHT. eassumption.
  - apply lc_ty_bool.
Qed.

Lemma instantiate_lc_at : forall theta gamma K k t,
  type_substitution_closed theta -> term_substitution_closed gamma ->
  lc_tm_at K k t -> lc_tm_at K k (instantiate theta gamma t).
Proof.
  intros theta gamma K k t Htheta Hgamma Hlc.
  revert theta gamma Htheta Hgamma.
  induction Hlc; intros theta gamma Htheta Hgamma; simpl.
  - apply lc_tm_bvar. assumption.
  - unfold term_substitution_closed in Hgamma.
    eapply lc_tm_at_monotone; [apply Hgamma|lia|lia].
  - apply lc_tm_abs.
    + eapply instantiate_ty_lc_at; eauto.
    + eapply IHHlc; eauto.
  - apply lc_tm_app; eauto.
  - apply lc_tm_tabs. eapply IHHlc; eauto.
  - apply lc_tm_tapp.
    + eapply IHHlc; eauto.
    + eapply instantiate_ty_lc_at; eauto.
  - apply lc_tm_true.
  - apply lc_tm_false.
  - apply lc_tm_if; eauto.
  - apply lc_tm_choice; eauto.
Qed.

Lemma instantiate_ty_open_rec : forall theta X U k T,
  type_substitution_closed theta -> locally_closed_ty U ->
  ~ In X (fv_ty T) ->
  instantiate_ty (type_subst_update theta X U) (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k U (instantiate_ty theta T).
Proof.
  intros theta X U k T Htheta HU. revert k.
  induction T; intros k Hnot; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + cbn [instantiate_ty]. unfold type_subst_update.
      rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply Hnot. simpl. auto.
    + unfold type_subst_update. rewrite E.
      erewrite open_ty_rec_lc_at; [reflexivity|].
      eapply lc_ty_at_monotone; [apply Htheta|lia].
  - assert (H1 : ~ In X (fv_ty T1)).
    { intro Hi. apply Hnot. simpl. apply in_or_app. left. exact Hi. }
    assert (H2 : ~ In X (fv_ty T2)).
    { intro Hi. apply Hnot. simpl. apply in_or_app. right. exact Hi. }
    simpl. rewrite IHT1 by exact H1. rewrite IHT2 by exact H2. reflexivity.
  - simpl. rewrite IHT by exact Hnot. reflexivity.
  - reflexivity.
Qed.

Lemma not_in_app_l : forall (A B : list atom) X,
  ~ In X (A ++ B) -> ~ In X A.
Proof. intros A B X H Hin. apply H. apply in_or_app. auto. Qed.

Lemma not_in_app_r : forall (A B : list atom) X,
  ~ In X (A ++ B) -> ~ In X B.
Proof. intros A B X H Hin. apply H. apply in_or_app. auto. Qed.

Lemma instantiate_open_tm_ty_rec : forall theta gamma k X U t,
  type_substitution_closed theta -> term_substitution_closed gamma ->
  locally_closed_ty U -> ~ In X (ftv_tm t) ->
  instantiate (type_subst_update theta X U) gamma
      (open_tm_ty_rec k (Ty_FVar X) t) =
  open_tm_ty_rec k U (instantiate theta gamma t).
Proof.
  intros theta gamma k X U t Htheta Hgamma HU Hnot.
  revert theta gamma k Htheta Hgamma.
  induction t as [n|a|T b IHb|a IH1 b IH2|b IHb|a IH T| | |
      a IH1 b IH2 c IH3|a IH1 b IH2];
    intros theta gamma k Htheta Hgamma; simpl in *.
  - reflexivity.
  - erewrite open_tm_ty_rec_lc_at with (K:=k) (k:=0) (U:=U).
    + reflexivity.
    + unfold term_substitution_closed in Hgamma.
      eapply lc_tm_at_monotone; [apply Hgamma|lia|lia].
  - assert (Hty : ~ In X (fv_ty T)) by (eapply not_in_app_l; eauto).
    assert (Hbody : ~ In X (ftv_tm b)) by (eapply not_in_app_r; eauto).
    simpl. rewrite (instantiate_ty_open_rec theta X U k T Htheta HU Hty).
    rewrite (IHb Hbody theta gamma k Htheta Hgamma). reflexivity.
  - assert (Hleft : ~ In X (ftv_tm a)) by (eapply not_in_app_l; eauto).
    assert (Hright : ~ In X (ftv_tm b)) by (eapply not_in_app_r; eauto).
    simpl. rewrite (IH1 Hleft theta gamma k Htheta Hgamma).
    rewrite (IH2 Hright theta gamma k Htheta Hgamma). reflexivity.
  - rewrite (IHb Hnot theta gamma (S k) Htheta Hgamma).
    + reflexivity.
  - assert (Hbody : ~ In X (ftv_tm a)) by (eapply not_in_app_l; eauto).
    assert (Hty : ~ In X (fv_ty T)) by (eapply not_in_app_r; eauto).
    simpl. rewrite (IH Hbody theta gamma k Htheta Hgamma).
    rewrite (instantiate_ty_open_rec theta X U k T Htheta HU Hty). reflexivity.
  - reflexivity.
  - reflexivity.
  - assert (H1 : ~ In X (ftv_tm a)) by (eapply not_in_app_l; eauto).
    assert (Hrest : ~ In X (ftv_tm b ++ ftv_tm c)) by (eapply not_in_app_r; eauto).
    assert (H2 : ~ In X (ftv_tm b)) by (eapply not_in_app_l; eauto).
    assert (H3 : ~ In X (ftv_tm c)) by (eapply not_in_app_r; eauto).
    simpl. rewrite (IH1 H1 theta gamma k Htheta Hgamma).
    rewrite (IH2 H2 theta gamma k Htheta Hgamma).
    rewrite (IH3 H3 theta gamma k Htheta Hgamma). reflexivity.
  - assert (H1 : ~ In X (ftv_tm a)) by (eapply not_in_app_l; eauto).
    assert (H2 : ~ In X (ftv_tm b)) by (eapply not_in_app_r; eauto).
    simpl. rewrite (IH1 H1 theta gamma k Htheta Hgamma).
    rewrite (IH2 H2 theta gamma k Htheta Hgamma). reflexivity.
Qed.

Lemma instantiate_open_tm_rec : forall theta gamma x u k t,
  type_substitution_closed theta -> term_substitution_closed gamma ->
  locally_closed_tm u -> ~ In x (fv_tm t) ->
  instantiate theta (term_subst_update gamma x u)
      (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k u (instantiate theta gamma t).
Proof.
  intros theta gamma x u k t Htheta Hgamma Hu Hnot.
  revert theta gamma k Htheta Hgamma.
  induction t as [n|y|T b IHb|a IH1 b IH2|b IHb|a IH V| | |
      a IH1 b IH2 c IH3|a IH1 b IH2];
    intros theta gamma k Htheta Hgamma; simpl in *.
  - destruct (Nat.eqb k n) eqn:E; simpl.
    + unfold term_subst_update. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply Hnot. simpl. auto.
    + unfold term_subst_update. rewrite E.
      assert (Hg : lc_tm_at 0 k (gamma y)).
      { unfold term_substitution_closed in Hgamma.
        eapply lc_tm_at_monotone; [apply Hgamma|lia|lia]. }
      rewrite (open_tm_rec_lc_at (gamma y) 0 k u Hg). reflexivity.
  - assert (Hbody : ~ In x (fv_tm b)) by exact Hnot.
    simpl. rewrite (IHb Hbody theta gamma (S k) Htheta Hgamma). reflexivity.
  - assert (H1 : ~ In x (fv_tm a)) by (eapply not_in_app_l; eauto).
    assert (H2 : ~ In x (fv_tm b)) by (eapply not_in_app_r; eauto).
    simpl. rewrite (IH1 H1 theta gamma k Htheta Hgamma).
    rewrite (IH2 H2 theta gamma k Htheta Hgamma). reflexivity.
  - rewrite (IHb Hnot theta gamma k Htheta Hgamma). reflexivity.
  - simpl. rewrite (IH Hnot theta gamma k Htheta Hgamma). reflexivity.
  - reflexivity.
  - reflexivity.
  - assert (H1 : ~ In x (fv_tm a)) by (eapply not_in_app_l; eauto).
    assert (Hrest : ~ In x (fv_tm b ++ fv_tm c)) by (eapply not_in_app_r; eauto).
    assert (H2 : ~ In x (fv_tm b)) by (eapply not_in_app_l; eauto).
    assert (H3 : ~ In x (fv_tm c)) by (eapply not_in_app_r; eauto).
    simpl. rewrite (IH1 H1 theta gamma k Htheta Hgamma).
    rewrite (IH2 H2 theta gamma k Htheta Hgamma).
    rewrite (IH3 H3 theta gamma k Htheta Hgamma). reflexivity.
  - assert (H1 : ~ In x (fv_tm a)) by (eapply not_in_app_l; eauto).
    assert (H2 : ~ In x (fv_tm b)) by (eapply not_in_app_r; eauto).
    simpl. rewrite (IH1 H1 theta gamma k Htheta Hgamma).
    rewrite (IH2 H2 theta gamma k Htheta Hgamma). reflexivity.
Qed.

Definition env_reducible (xi : atom -> reducibility_candidate)
    (Gamma : context) (gamma : term_substitution) : Prop :=
  forall x T, lookup_context x Gamma = Some T -> reducible xi [] T (gamma x).

Lemma lookup_ftv_context : forall Gamma x T X,
  lookup_context x Gamma = Some T -> In X (fv_ty T) -> In X (ftv_context Gamma).
Proof.
  induction Gamma as [|[y U] Gamma IH]; intros x T X Hlook Hin; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + inversion Hlook; subst. apply in_or_app. left. exact Hin.
    + apply in_or_app. right. eapply IH; eauto.
Qed.

Lemma env_reducible_xi_update : forall xi X C Gamma gamma,
  env_reducible xi Gamma gamma -> ~ In X (ftv_context Gamma) ->
  env_reducible (xi_update xi X C) Gamma gamma.
Proof.
  intros xi X C Gamma gamma Henv Hfresh y T Hlook.
  assert (Hnot : ~ In X (fv_ty T)).
  { intro Hin. apply Hfresh. eapply lookup_ftv_context; eauto. }
  apply (proj2 (reducible_xi_update_irrelevant xi X C [] T (gamma y) Hnot)).
  apply Henv with (x:=y); exact Hlook.
Qed.

Lemma env_reducible_term_update : forall xi Gamma gamma x A u,
  env_reducible xi Gamma gamma -> ~ In x (dom_context Gamma) ->
  reducible xi [] A u ->
  env_reducible xi (update Gamma x A) (term_subst_update gamma x u).
Proof.
  intros xi Gamma gamma x A u Henv Hfresh Hu y T Hlook.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y. rewrite lookup_context_update_eq in Hlook.
    inversion Hlook; subst T. unfold term_subst_update. rewrite Nat.eqb_refl. exact Hu.
  - assert (Hxy : x <> y).
    { intro Heq. subst y. rewrite Nat.eqb_refl in E. discriminate. }
    rewrite lookup_context_update_neq in Hlook by exact Hxy.
    assert (Hupd : Nat.eqb x y = false).
    { apply Nat.eqb_neq. congruence. }
    unfold term_subst_update. rewrite Hupd. eapply Henv; eauto.
Qed.

Lemma fresh_app_left : forall A B,
  ~ In (fresh (A ++ B)) A.
Proof. intros. eapply not_in_app_l. apply fresh_notin. Qed.

Lemma fresh_app_right : forall A B,
  ~ In (fresh (A ++ B)) B.
Proof. intros. eapply not_in_app_r. apply fresh_notin. Qed.

Lemma app_not_value : forall t u, ~ value (tm_app t u).
Proof. intros t u Hv. inversion Hv. Qed.

Lemma tapp_not_value : forall t T, ~ value (tm_tapp t T).
Proof. intros t T Hv. inversion Hv. Qed.

Lemma value_dec_lc : forall t,
  locally_closed_tm t -> {value t} + {~ value t}.
Proof.
  intros t Hlc. destruct t.
  - right. intro Hv. inversion Hv.
  - right. intro Hv. inversion Hv.
  - left. apply v_abs. exact Hlc.
  - right. intro Hv. inversion Hv.
  - left. apply v_tabs. exact Hlc.
  - right. intro Hv. inversion Hv.
  - left. constructor.
  - left. constructor.
  - right. intro Hv. inversion Hv.
  - right. intro Hv. inversion Hv.
Qed.

Lemma reducible_arrow_step : forall xi beta A B f f',
  reducible xi beta (Ty_Arrow A B) f -> f --> f' ->
  reducible xi beta (Ty_Arrow A B) f'.
Proof.
  intros xi beta A B f f' [Hlc [Hsn Hcan]] Hstep.
  split; [eapply lc_step; eauto|]. split.
  - inversion Hsn; eauto.
  - intros v Hv Hfv. eapply Hcan; [exact Hv|].
    eapply multi_step_left; eauto.
Qed.

Lemma reducible_all_step : forall xi beta T f f',
  reducible xi beta (Ty_All T) f -> f --> f' ->
  reducible xi beta (Ty_All T) f'.
Proof.
  intros xi beta T f f' [Hlc [Hsn Hcan]] Hstep.
  split; [eapply lc_step; eauto|]. split.
  - inversion Hsn; eauto.
  - intros v Hv Hfv. eapply Hcan; [exact Hv|].
    eapply multi_step_left; eauto.
Qed.

Lemma reducible_tapp : forall xi T f U V,
  reducible xi [] (Ty_All T) f -> locally_closed_ty U ->
  locally_closed_ty V ->
  reducible xi [] (open_ty T V) (tm_tapp f U).
Proof.
  intros xi T f U V Hf HU HV.
  pose proof (proj2 (reducible_regular xi [] (Ty_All T) f Hf)) as Hsn.
  revert Hf. induction Hsn as [f Hsteps IH]; intros Hf.
  destruct Hf as [Hlc [Hsn Hcan]].
  destruct (value_dec_lc f Hlc) as [Hv|Hnv].
  - destruct (Hcan f Hv (multi_refl f)) as [b [E Hpoly]].
    subst f. specialize (Hpoly U HU (reducible_candidate xi [] V)).
    apply (proj2 (reducible_open_ty_rec xi 0 [] T V
      (tm_tapp (tm_tabs b) U) eq_refl HV)).
    exact Hpoly.
  - eapply reducible_expand.
    + apply lc_tm_tapp; [exact Hlc|exact HU].
    + apply tapp_not_value.
    + intros w Hstep. inversion Hstep; subst.
      * exfalso. apply Hnv. apply v_tabs. assumption.
      * assert (Hfr : reducible xi [] (Ty_All T) f).
        { exact (conj Hlc (conj Hsn Hcan)). }
        exact (IH t' H1 (reducible_all_step xi [] T f t' Hfr H1)).
Qed.

Lemma reducible_choice : forall xi beta T t1 t2,
  locally_closed_tm t1 -> locally_closed_tm t2 ->
  reducible xi beta T t1 -> reducible xi beta T t2 ->
  reducible xi beta T (tm_choice t1 t2).
Proof.
  intros xi beta T t1 t2 L1 L2 H1 H2.
  eapply reducible_expand.
  - apply lc_tm_choice; assumption.
  - intro Hv. inversion Hv.
  - intros u Hstep. inversion Hstep; subst; assumption.
Qed.

Lemma reducible_if : forall xi beta T c t1 t2,
  reducible xi beta Ty_Bool c ->
  reducible xi beta T t1 -> reducible xi beta T t2 ->
  reducible xi beta T (tm_if c t1 t2).
Proof.
  intros xi beta T c t1 t2 Hc H1 H2.
  pose proof (proj2 (reducible_regular xi beta Ty_Bool c Hc)) as Hsn.
  revert Hc. induction Hsn as [c Hsteps IH]; intros Hc.
  destruct Hc as [Hlc [Hsn Hcan]].
  destruct (value_dec_lc c Hlc) as [Hv|Hnv].
  - destruct (Hcan c Hv (multi_refl c)) as [E|E]; subst c.
    + eapply reducible_expand.
      * apply lc_tm_if; [exact Hlc|apply (proj1 (reducible_regular xi beta T t1 H1))|apply (proj1 (reducible_regular xi beta T t2 H2))].
      * intro Hval. inversion Hval.
      * intros u Hstep. inversion Hstep; subst; try assumption; try congruence.
        exfalso. eapply value_no_step; eauto.
    + eapply reducible_expand.
      * apply lc_tm_if; [exact Hlc|apply (proj1 (reducible_regular xi beta T t1 H1))|apply (proj1 (reducible_regular xi beta T t2 H2))].
      * intro Hval. inversion Hval.
      * intros u Hstep. inversion Hstep; subst; try assumption; try congruence.
        exfalso. eapply value_no_step; eauto.
  - eapply reducible_expand.
    + apply lc_tm_if; [exact Hlc|apply (proj1 (reducible_regular xi beta T t1 H1))|apply (proj1 (reducible_regular xi beta T t2 H2))].
    + intro Hval. inversion Hval.
    + intros u Hstep. inversion Hstep; subst.
      * exfalso. apply Hnv. constructor.
      * exfalso. apply Hnv. constructor.
      * assert (Hcr : reducible xi beta Ty_Bool c).
        { exact (conj Hlc (conj Hsn Hcan)). }
        exact (IH t1' H4 (reducible_step xi beta Ty_Bool c t1' Hcr H4)).
Qed.

Lemma value_strongly_normalizing : forall v,
  value v -> strongly_normalizing v.
Proof.
  intros v Hv. constructor. intros u Hstep. exfalso.
  eapply value_no_step; eauto.
Qed.

Lemma reducible_app_abs_fund : forall xi beta A B T b u,
  locally_closed_tm (tm_abs T b) ->
  (forall v, reducible xi beta A v -> reducible xi beta B (open_tm b v)) ->
  reducible xi beta A u ->
  reducible xi beta B (tm_app (tm_abs T b) u).
Proof.
  intros xi beta A B T b u Habs Hbody Hu.
  pose proof (proj2 (reducible_regular xi beta A u Hu)) as Hsn.
  revert Hu. induction Hsn as [u Hnext IH]; intros Hu.
  eapply reducible_expand.
  - apply lc_tm_app; [exact Habs|]. exact (proj1 (reducible_regular xi beta A u Hu)).
  - apply app_not_value.
  - intros w Hstep. inversion Hstep; subst.
    + apply Hbody. exact Hu.
    + inversion H1.
    + eapply IH; [eassumption|eapply reducible_step; eauto].
Qed.

Lemma reducible_tapp_tabs_fund : forall xi beta R b U,
  locally_closed_tm (tm_tabs b) -> locally_closed_ty U ->
  reducible xi beta R (open_tm_ty b U) ->
  reducible xi beta R (tm_tapp (tm_tabs b) U).
Proof.
  intros xi beta R b U Htabs HU Hbody.
  eapply reducible_expand.
  - apply lc_tm_tapp; [exact Htabs|exact HU].
  - apply tapp_not_value.
  - intros w Hstep. inversion Hstep; subst.
    + exact Hbody.
    + inversion H1.
Qed.

Lemma reducible_app_fund : forall xi beta A B f a,
  reducible xi beta (Ty_Arrow A B) f -> reducible xi beta A a ->
  reducible xi beta B (tm_app f a).
Proof.
  intros xi beta A B f a Hf Ha.
  pose proof (proj2 (reducible_regular xi beta (Ty_Arrow A B) f Hf)) as Hsn.
  revert Hf. induction Hsn as [f Hsteps IH]; intros Hf.
  destruct Hf as [Hlc [Hsn Hcan]].
  destruct (value_dec_lc f Hlc) as [Hv|Hnv].
  - destruct (Hcan f Hv (multi_refl f)) as [T [b [E Hfun]]].
    subst f. apply Hfun. exact Ha.
  - eapply reducible_expand.
    + apply lc_tm_app; [exact Hlc|]. exact (proj1 (reducible_regular xi beta A a Ha)).
    + apply app_not_value.
    + intros w Hstep. inversion Hstep; subst.
      * exfalso. apply Hnv. apply v_abs. assumption.
      * assert (Hfr : reducible xi beta (Ty_Arrow A B) f).
        { exact (conj Hlc (conj Hsn Hcan)). }
        exact (IH t1' H1 (reducible_arrow_step xi beta A B f t1' Hfr H1)).
      * exfalso. apply Hnv. assumption.
Qed.

Lemma reducible_bool_true : forall xi beta,
  reducible xi beta Ty_Bool tm_true.
Proof.
  intros. split; [apply lc_tm_true|]. split.
  - apply value_strongly_normalizing. constructor.
  - intros v Hv Hmulti. assert (E : v = tm_true).
    { eapply value_multi_eq; [constructor|exact Hmulti]. }
    left. exact E.
Qed.

Lemma reducible_bool_false : forall xi beta,
  reducible xi beta Ty_Bool tm_false.
Proof.
  intros. split; [apply lc_tm_false|]. split.
  - apply value_strongly_normalizing. constructor.
  - intros v Hv Hmulti. assert (E : v = tm_false).
    { eapply value_multi_eq; [constructor|exact Hmulti]. }
    right. exact E.
Qed.

Lemma reducible_candidate_fvar : forall xi beta X,
  reducible_candidate xi beta (Ty_FVar X) = xi X.
Proof. reflexivity. Qed.

Theorem fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall theta xi gamma,
    type_substitution_closed theta -> term_substitution_closed gamma ->
    env_reducible xi Gamma gamma ->
    reducible xi [] T (instantiate theta gamma t).
Proof.
  intros Delta Gamma t T Hty. induction Hty;
    intros theta xi gamma Htheta Hgamma Henv; simpl.
  - eapply Henv. exact H.
  - set (x := fresh (L ++ (dom_context Gamma ++ fv_tm t2))).
    assert (Hxall : ~ In x (L ++ (dom_context Gamma ++ fv_tm t2))).
    { unfold x. apply fresh_notin. }
    assert (HxL : ~ In x L) by (eapply not_in_app_l; exact Hxall).
    assert (Hxrest : ~ In x (dom_context Gamma ++ fv_tm t2))
      by (eapply not_in_app_r; exact Hxall).
    assert (Hxdom : ~ In x (dom_context Gamma))
      by (eapply not_in_app_l; exact Hxrest).
    assert (Hxfv : ~ In x (fv_tm t2))
      by (eapply not_in_app_r; exact Hxrest).
    assert (Horig : locally_closed_tm (tm_abs T1 t2)).
    { apply lc_tm_abs.
      - eapply wf_ty_lc; eauto.
      - pose proof (has_type_lc Delta (update Gamma x T1)
          (open_tm t2 (tm_fvar x)) T2 (H0 x HxL)) as Hopened.
        eapply lc_tm_at_open_tm_inv. exact Hopened. }
    assert (HabsLC : locally_closed_tm
      (tm_abs (instantiate_ty theta T1) (instantiate theta gamma t2))).
    { change (locally_closed_tm (instantiate theta gamma (tm_abs T1 t2))).
      eapply instantiate_lc_at; eauto. }
    assert (HabsVal : value (tm_abs (instantiate_ty theta T1)
        (instantiate theta gamma t2))).
    { apply v_abs. exact HabsLC. }
    split; [exact HabsLC|]. split; [apply value_strongly_normalizing; exact HabsVal|].
    intros v Hv Hmulti.
    assert (Heq : v = tm_abs (instantiate_ty theta T1) (instantiate theta gamma t2)).
    { eapply value_multi_eq; eauto. }
    subst v. exists (instantiate_ty theta T1), (instantiate theta gamma t2).
    split; [reflexivity|]. intros u Hu.
    eapply reducible_app_abs_fund; [exact HabsLC| |exact Hu].
    intros w Hw.
    assert (HgammaW : term_substitution_closed (term_subst_update gamma x w)).
    { apply term_subst_update_closed; [exact Hgamma|exact (proj1 (reducible_regular xi [] T1 w Hw))]. }
    assert (HenvW : env_reducible xi (update Gamma x T1)
        (term_subst_update gamma x w)).
    { eapply env_reducible_term_update; [exact Henv|exact Hxdom|exact Hw]. }
    pose proof (H1 x HxL theta xi (term_subst_update gamma x w)
      Htheta HgammaW HenvW) as Hbody.
    unfold open_tm in Hbody.
    rewrite (instantiate_open_tm_rec theta gamma x w 0 t2
      Htheta Hgamma (proj1 (reducible_regular xi [] T1 w Hw)) Hxfv) in Hbody.
    exact Hbody.
  - eapply reducible_app_fund; eauto.
  - set (X := fresh (L ++
      (ftv_context Gamma ++ (ftv_tm t ++ fv_ty T)))).
    assert (HXall : ~ In X (L ++ (ftv_context Gamma ++ (ftv_tm t ++ fv_ty T))))
      by (unfold X; apply fresh_notin).
    assert (HXL : ~ In X L) by (eapply not_in_app_l; exact HXall).
    assert (HXrest : ~ In X (ftv_context Gamma ++ (ftv_tm t ++ fv_ty T)))
      by (eapply not_in_app_r; exact HXall).
    assert (HXctx : ~ In X (ftv_context Gamma))
      by (eapply not_in_app_l; exact HXrest).
    assert (HXtail : ~ In X (ftv_tm t ++ fv_ty T))
      by (eapply not_in_app_r; exact HXrest).
    assert (HXterm : ~ In X (ftv_tm t))
      by (eapply not_in_app_l; exact HXtail).
    assert (HXtype : ~ In X (fv_ty T))
      by (eapply not_in_app_r; exact HXtail).
    assert (Horig : locally_closed_tm (tm_tabs t)).
    { apply lc_tm_tabs.
      pose proof (has_type_lc (X :: Delta) Gamma
        (open_tm_ty t (Ty_FVar X)) (open_ty T (Ty_FVar X))
        (H X HXL)) as Hopened.
      eapply lc_tm_at_open_ty_inv. exact Hopened. }
    assert (HtabsLC : locally_closed_tm (tm_tabs (instantiate theta gamma t))).
    { change (locally_closed_tm (instantiate theta gamma (tm_tabs t))).
      eapply instantiate_lc_at; eauto. }
    assert (HtabsVal : value (tm_tabs (instantiate theta gamma t))).
    { apply v_tabs. exact HtabsLC. }
    split; [exact HtabsLC|]. split; [apply value_strongly_normalizing; exact HtabsVal|].
    intros v Hv Hmulti.
    assert (Heq : v = tm_tabs (instantiate theta gamma t)).
    { eapply value_multi_eq; eauto. }
    subst v. exists (instantiate theta gamma t). split; [reflexivity|].
    intros U HU C.
    set (thetaU := type_subst_update theta X U).
    set (xiC := xi_update xi X C).
    assert (HthetaU : type_substitution_closed thetaU).
    { unfold thetaU. apply type_subst_update_closed; [exact Htheta|exact HU]. }
    assert (HenvC : env_reducible xiC Gamma gamma).
    { unfold xiC. eapply env_reducible_xi_update; eauto. }
    specialize (H0 X HXL thetaU xiC gamma HthetaU Hgamma HenvC).
    unfold thetaU, open_tm_ty in H0.
    rewrite (instantiate_open_tm_ty_rec theta gamma 0 X U t
      Htheta Hgamma HU HXterm) in H0.
    assert (Hmap : xiC X = C).
    { unfold xiC, xi_update. rewrite Nat.eqb_refl. reflexivity. }
    assert (Hsemopen : reducible xiC [] (open_ty T (Ty_FVar X))
        (open_tm_ty_rec 0 U (instantiate theta gamma t)) ->
        reducible xiC [C] T (open_tm_ty_rec 0 U (instantiate theta gamma t))).
    { intro Hr.
      pose proof (reducible_open_ty_rec xiC 0 [] T (Ty_FVar X)
        (open_tm_ty_rec 0 U (instantiate theta gamma t)) eq_refl
        (lc_ty_fvar 0 X)) as Hopen.
      rewrite reducible_candidate_fvar in Hopen. rewrite Hmap in Hopen.
      apply (proj1 Hopen). exact Hr. }
    assert (HrelC : reducible xi [C] T
        (open_tm_ty_rec 0 U (instantiate theta gamma t))).
    { apply (proj1 (reducible_xi_update_irrelevant xi X C [C] T
          (open_tm_ty_rec 0 U (instantiate theta gamma t)) HXtype)).
      apply Hsemopen. exact H0. }
    eapply reducible_tapp_tabs_fund; [exact HtabsLC|exact HU|exact HrelC].
  - eapply reducible_tapp with (U:=instantiate_ty theta U) (V:=U).
    + exact (IHHty theta xi gamma Htheta Hgamma Henv).
    + eapply instantiate_ty_lc_at; [exact Htheta|].
      eapply wf_ty_lc; eauto.
    + eapply wf_ty_lc; eauto.
  - exact (reducible_bool_true xi []).
  - exact (reducible_bool_false xi []).
  - eapply reducible_if; eauto.
  - eapply reducible_choice.
    + exact (proj1 (reducible_regular xi [] T (instantiate theta gamma t1)
        (IHHty1 theta xi gamma Htheta Hgamma Henv))).
    + exact (proj1 (reducible_regular xi [] T (instantiate theta gamma t2)
        (IHHty2 theta xi gamma Htheta Hgamma Henv))).
    + exact (IHHty1 theta xi gamma Htheta Hgamma Henv).
    + exact (IHHty2 theta xi gamma Htheta Hgamma Henv).
Qed.

Lemma instantiate_ty_identity : forall T,
  instantiate_ty identity_type_substitution T = T.
Proof.
  induction T; simpl; try rewrite IHT; try rewrite IHT1; try rewrite IHT2;
    try reflexivity.
Qed.

Lemma instantiate_identity : forall t,
  instantiate identity_type_substitution identity_term_substitution t = t.
Proof.
  induction t; simpl; try rewrite instantiate_ty_identity;
    try rewrite IHt; try rewrite IHt1; try rewrite IHt2; try rewrite IHt3;
    try reflexivity.
Qed.

Lemma reducible_app_abs : forall xi beta A B T b u,
  locally_closed_tm (tm_abs T b) ->
  (forall v, reducible xi beta A v -> reducible xi beta B (open_tm b v)) ->
  reducible xi beta A u ->
  reducible xi beta B (tm_app (tm_abs T b) u).
Proof.
  intros xi beta A B T b u Habs Hbody Hu.
  pose proof (proj2 (reducible_regular xi beta A u Hu)) as Hsn.
  revert Hu. induction Hsn as [u Hnext IH]; intros Hu.
  eapply reducible_expand.
  - apply lc_tm_app; [exact Habs|]. exact (proj1 (reducible_regular xi beta A u Hu)).
  - apply app_not_value.
  - intros w Hstep. inversion Hstep; subst.
    + apply Hbody. exact Hu.
    + inversion H1.
    + eapply IH; [eassumption|eapply reducible_step; eauto].
Qed.

Lemma reducible_tapp_tabs : forall xi beta R b U,
  locally_closed_tm (tm_tabs b) -> locally_closed_ty U ->
  reducible xi beta R (open_tm_ty b U) ->
  reducible xi beta R (tm_tapp (tm_tabs b) U).
Proof.
  intros xi beta R b U Htabs HU Hbody.
  eapply reducible_expand.
  - apply lc_tm_tapp; [exact Htabs|exact HU].
  - apply tapp_not_value.
  - intros w Hstep. inversion Hstep; subst.
    + exact Hbody.
    + inversion H1.
Qed.

Lemma reducible_app : forall xi beta A B f a,
  reducible xi beta (Ty_Arrow A B) f ->
  reducible xi beta A a ->
  reducible xi beta B (tm_app f a).
Proof.
  intros xi beta A B f a Hf Ha.
  pose proof (proj2 (reducible_regular xi beta (Ty_Arrow A B) f Hf)) as Hsn.
  revert Hf. induction Hsn as [f Hsteps IH]; intros Hf.
  destruct Hf as [Hlc [Hsn Hcan]].
  destruct (value_dec_lc f Hlc) as [Hv|Hnv].
  - destruct (Hcan f Hv (multi_refl f)) as [T [b [E Hfun]]].
    subst f. apply Hfun. exact Ha.
  - eapply reducible_expand.
    + apply lc_tm_app; [exact Hlc|]. exact (proj1 (reducible_regular xi beta A a Ha)).
    + apply app_not_value.
    + intros w Hstep. inversion Hstep; subst.
      * exfalso. apply Hnv. apply v_abs. assumption.
      * assert (Hfr : reducible xi beta (Ty_Arrow A B) f).
        { exact (conj Hlc (conj Hsn Hcan)). }
        exact (IH t1' H1 (reducible_arrow_step xi beta A B f t1' Hfr H1)).
      * exfalso. apply Hnv. assumption.
Qed.

Lemma sn_step : forall t u,
  strongly_normalizing t -> t --> u -> strongly_normalizing u.
Proof. intros t u H; inversion H; eauto. Qed.

Lemma sn_of_all_steps : forall t,
  (forall u, t --> u -> strongly_normalizing u) -> strongly_normalizing t.
Proof. constructor; auto. Qed.

Lemma sn_value : forall v, value v -> strongly_normalizing v.
Proof.
  intros v Hv. constructor. intros u Hs. exfalso.
  eapply value_no_step; eauto.
Qed.

Lemma sn_choice : forall t1 t2,
  strongly_normalizing t1 -> strongly_normalizing t2 ->
  locally_closed_tm t1 -> locally_closed_tm t2 ->
  strongly_normalizing (tm_choice t1 t2).
Proof.
  intros t1 t2 H1 H2 L1 L2. constructor. intros u Hs.
  inversion Hs; subst; eauto.
Qed.

Lemma sn_if : forall c t1 t2,
  strongly_normalizing c -> strongly_normalizing t1 ->
  strongly_normalizing t2 -> locally_closed_tm t1 ->
  locally_closed_tm t2 -> strongly_normalizing (tm_if c t1 t2).
Proof.
  intros c t1 t2 Hc. induction Hc as [c Hc IHc].
  intros H1 H2 L1 L2.
  constructor. intros u Hs. inversion Hs; subst; eauto.
Qed.

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  intros t T Hty.
  set (xi := fun _ : atom => bool_sat_candidate).
  assert (Henv : env_reducible xi empty identity_term_substitution).
  { intros x U Hlookup. discriminate. }
  pose proof (fundamental [] empty t T Hty identity_type_substitution xi
    identity_term_substitution identity_type_substitution_closed
    identity_term_substitution_closed Henv) as Hred.
  rewrite instantiate_identity in Hred.
  exact (proj2 (reducible_regular xi [] T t Hred)).
Qed.

End SystemFNormalizationIfNondeterminismEasyTask.
