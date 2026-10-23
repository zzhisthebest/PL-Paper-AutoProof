(** System F parametricity benchmark, Easy variant.
    Features: if-nondeterminism. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFParametricityIfNondeterminismEasyTask.

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

Inductive evaluates : tm -> tm -> Prop :=
  | EvalValue : forall v, value v -> evaluates v v
  | EvalApp : forall f arg U body v result,
      evaluates f (tm_abs U body) -> evaluates arg v ->
      evaluates (open_tm body v) result -> evaluates (tm_app f arg) result
  | EvalTApp : forall f U body result,
      evaluates f (tm_tabs body) -> locally_closed_ty U ->
      evaluates (open_tm_ty body U) result -> evaluates (tm_tapp f U) result
  | EvalIfTrue : forall c t u v,
      evaluates c tm_true -> evaluates t v -> locally_closed_tm u ->
      evaluates (tm_if c t u) v
  | EvalIfFalse : forall c t u v,
      evaluates c tm_false -> locally_closed_tm t -> evaluates u v ->
      evaluates (tm_if c t u) v
  | EvalChoiceLeft : forall t1 t2 v,
      evaluates t1 v -> locally_closed_tm t2 -> evaluates (tm_choice t1 t2) v
  | EvalChoiceRight : forall t1 t2 v,
      locally_closed_tm t1 -> evaluates t2 v -> evaluates (tm_choice t1 t2) v.

Lemma multi_if : forall c c' t u,
  c -->* c' -> locally_closed_tm t -> locally_closed_tm u ->
  tm_if c t u -->* tm_if c' t u.
Proof. intros c c' t u H. induction H; eauto using multi, step. Qed.

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

(* Relational interpretation of a type.  The list records relations for
   locally nameless type variables; universal types extend it with an
   arbitrary relation, which is the parametricity step. *)
Definition binary_relation := tm -> tm -> Prop.

Fixpoint value_relation (rho : atom -> binary_relation)
    (bound : list binary_relation) (T : ty) (v1 v2 : tm) : Prop :=
  match T with
  | Ty_BVar n => match nth_error bound n with
                 | Some R => R v1 v2
                 | None => False
                 end
  | Ty_FVar X => rho X v1 v2
  | Ty_Bool => (v1 = tm_true /\ v2 = tm_true) \/
               (v1 = tm_false /\ v2 = tm_false)
  | Ty_Arrow A B =>
      exists A1 b1 A2 b2,
        v1 = tm_abs A1 b1 /\ v2 = tm_abs A2 b2 /\
        value v1 /\ value v2 /\
      forall a1 a2, value_relation rho bound A a1 a2 ->
        exists r1 r2,
          evaluates (open_tm b1 a1) r1 /\ evaluates (open_tm b2 a2) r2 /\
          value_relation rho bound B r1 r2
  | Ty_All Tbody =>
      exists b1 b2, v1 = tm_tabs b1 /\ v2 = tm_tabs b2 /\
      value v1 /\ value v2 /\
      forall (U1 U2 : ty) (R : binary_relation),
        locally_closed_ty U1 -> locally_closed_ty U2 ->
        (forall x y, R x y -> value x /\ value y) ->
        exists r1 r2,
          evaluates (open_tm_ty b1 U1) r1 /\
          evaluates (open_tm_ty b2 U2) r2 /\
          value_relation rho (R :: bound) Tbody r1 r2
  end.

Definition relation_value_closed (R : binary_relation) : Prop :=
  forall v1 v2, R v1 v2 -> value v1 /\ value v2.

Definition relation_subst_update (rho : atom -> binary_relation)
    (X : atom) (R : binary_relation) : atom -> binary_relation :=
  fun Y => if Nat.eqb X Y then R else rho Y.

Lemma value_relation_update_fresh : forall rho bound T X R v1 v2,
  ~ In X (fv_ty T) ->
  value_relation (relation_subst_update rho X R) bound T v1 v2 <->
  value_relation rho bound T v1 v2.
Proof.
  intros rho bound T. revert rho bound.
  induction T; intros rho bound X R v1 v2 Hfresh; simpl in *.
  - tauto.
  - destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply Hfresh. simpl. auto.
    + unfold relation_subst_update. simpl. rewrite E. tauto.
  - simpl in Hfresh. split; intros H.
    + destruct H as (A1 & b1 & A2 & b2 & E1 & E2 & V1 & V2 & Hall).
      exists A1, b1, A2, b2. repeat split; try assumption.
      intros a1 a2 Ha.
      assert (HF1 : ~ In X (fv_ty T1)) by (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
      assert (HF2 : ~ In X (fv_ty T2)) by (intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
      apply (proj2 (IHT1 rho bound X R a1 a2 HF1)) in Ha.
      destruct (Hall a1 a2 Ha) as (r1 & r2 & Hr1 & Hr2 & Hout).
      exists r1, r2. repeat split; try assumption.
      apply (proj1 (IHT2 rho bound X R r1 r2 HF2)). exact Hout.
    + destruct H as (A1 & b1 & A2 & b2 & E1 & E2 & V1 & V2 & Hall).
      exists A1, b1, A2, b2. repeat split; try assumption.
      intros a1 a2 Ha.
      assert (HF1 : ~ In X (fv_ty T1)) by (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
      assert (HF2 : ~ In X (fv_ty T2)) by (intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
      apply (proj1 (IHT1 rho bound X R a1 a2 HF1)) in Ha.
      destruct (Hall a1 a2 Ha) as (r1 & r2 & Hr1 & Hr2 & Hout).
      exists r1, r2. repeat split; try assumption.
      apply (proj2 (IHT2 rho bound X R r1 r2 HF2)). exact Hout.
  - simpl in Hfresh. split; intros H.
    + destruct H as (b1 & b2 & E1 & E2 & V1 & V2 & Hall).
      exists b1, b2. repeat split; try assumption.
      intros U1 U2 Q HU1 HU2 HQ.
      assert (HF : ~ In X (fv_ty T)) by assumption.
      destruct (Hall U1 U2 Q HU1 HU2 HQ) as (r1 & r2 & Hr1 & Hr2 & Hout).
      exists r1, r2. repeat split; try assumption.
      apply (proj1 (IHT rho (Q :: bound) X R r1 r2 HF)). exact Hout.
    + destruct H as (b1 & b2 & E1 & E2 & V1 & V2 & Hall).
      exists b1, b2. repeat split; try assumption.
      intros U1 U2 Q HU1 HU2 HQ.
      assert (HF : ~ In X (fv_ty T)) by assumption.
      destruct (Hall U1 U2 Q HU1 HU2 HQ) as (r1 & r2 & Hr1 & Hr2 & Hout).
      exists r1, r2. repeat split; try assumption.
      apply (proj2 (IHT rho (Q :: bound) X R r1 r2 HF)). exact Hout.
  - tauto.
Qed.

Definition related_context (Gamma : context) (gamma1 gamma2 : term_substitution)
    (rho : atom -> binary_relation) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    value_relation rho [] T (gamma1 x) (gamma2 x).

Definition relation_substitution_good (rho : atom -> binary_relation) : Prop :=
  forall X, relation_value_closed (rho X).

Lemma relation_substitution_good_update : forall rho X R,
  relation_substitution_good rho -> relation_value_closed R ->
  relation_substitution_good (relation_subst_update rho X R).
Proof.
  intros rho X R Hrho HR Y. unfold relation_subst_update.
  destruct (Nat.eqb X Y); auto.
Qed.

Lemma lookup_context_fv_context : forall Gamma x T X,
  lookup_context x Gamma = Some T -> In X (fv_ty T) -> In X (ftv_context Gamma).
Proof.
  induction Gamma as [|[y S] Gamma IH]; intros x T X Hlook Hin; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + inversion Hlook; subst. apply in_or_app. left. exact Hin.
    + apply in_or_app. right. eapply IH; eauto.
Qed.

Lemma related_context_update_term : forall Gamma gamma1 gamma2 rho x T a1 a2,
  related_context Gamma gamma1 gamma2 rho ->
  value_relation rho [] T a1 a2 ->
  ~ In x (dom_context Gamma) ->
  related_context (update Gamma x T)
    (term_subst_update gamma1 x a1) (term_subst_update gamma2 x a2) rho.
Proof.
  intros Gamma gamma1 gamma2 rho x T a1 a2 Hctx Ha Hfresh y S Hlook.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y.
    rewrite lookup_context_update_eq in Hlook. inversion Hlook; subst S.
    unfold term_subst_update. simpl. rewrite Nat.eqb_refl. exact Ha.
  - apply Nat.eqb_neq in E.
    rewrite lookup_context_update_neq in Hlook by congruence.
    unfold term_subst_update. assert (E' : Nat.eqb x y = false) by (apply Nat.eqb_neq; congruence).
    rewrite E'. eapply Hctx; eauto.
Qed.

Lemma related_context_update_typevar : forall Gamma gamma1 gamma2 rho X R,
  related_context Gamma gamma1 gamma2 rho ->
  ~ In X (ftv_context Gamma) ->
  related_context Gamma gamma1 gamma2 (relation_subst_update rho X R).
Proof.
  intros Gamma gamma1 gamma2 rho X R Hctx Hfresh x T Hlook.
  specialize (Hctx x T Hlook).
  assert (Hnot : ~ In X (fv_ty T)).
  { intro Hin. apply Hfresh. eapply lookup_context_fv_context; eauto. }
  apply (proj2 (value_relation_update_fresh rho [] T X R
    (gamma1 x) (gamma2 x) Hnot)). exact Hctx.
Qed.

Lemma value_relation_open_ty : forall rho bound T X R v1 v2,
  ~ In X (fv_ty T) ->
  lc_ty_at (S (length bound)) T ->
  value_relation rho (bound ++ [R]) T v1 v2 <->
  value_relation (relation_subst_update rho X R) bound
    (open_ty_rec (length bound) (Ty_FVar X) T) v1 v2.
Proof.
  intros rho bound T. revert rho bound.
  induction T; intros rho bound X R v1 v2 Hfresh Hlc; simpl in *.
  - inversion Hlc as [| | | |]; subst.
    destruct (Nat.eqb (length bound) n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. simpl. unfold relation_subst_update.
      rewrite Nat.eqb_refl. rewrite nth_error_app2 by lia.
      replace (length bound - length bound) with 0 by lia. simpl. tauto.
    + apply Nat.eqb_neq in E. simpl. rewrite nth_error_app1 by lia.
      tauto.
  - simpl in Hfresh. destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply Hfresh. simpl. auto.
    + unfold relation_subst_update. simpl. rewrite E. tauto.
  - inversion Hlc; subst. simpl. split; intros H.
    + destruct H as (A1 & b1 & A2 & b2 & E1 & E2 & V1 & V2 & Hall).
      exists A1, b1, A2, b2. repeat split; try assumption.
      intros a1 a2 Ha.
      assert (HF1 : ~ In X (fv_ty T1)) by (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
      assert (HF2 : ~ In X (fv_ty T2)) by (intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
      pose proof (IHT1 rho bound X R a1 a2 HF1 H2) as [I1 I2].
      destruct (Hall a1 a2 (I2 Ha)) as (r1 & r2 & Hr1 & Hr2 & Hout).
        exists r1, r2. repeat split; try assumption.
        pose proof (IHT2 rho bound X R r1 r2 HF2 H3) as [J1 J2].
        apply J1. exact Hout.
    + destruct H as (A1 & b1 & A2 & b2 & E1 & E2 & V1 & V2 & Hall).
      exists A1, b1, A2, b2. repeat split; try assumption.
      intros a1 a2 Ha.
      assert (HF1 : ~ In X (fv_ty T1)) by (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
      assert (HF2 : ~ In X (fv_ty T2)) by (intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
      pose proof (IHT1 rho bound X R a1 a2 HF1 H2) as [I1 I2].
      destruct (Hall a1 a2 (I1 Ha)) as (r1 & r2 & Hr1 & Hr2 & Hout).
        exists r1, r2. repeat split; try assumption.
        pose proof (IHT2 rho bound X R r1 r2 HF2 H3) as [J1 J2].
        apply J2. exact Hout.
  - inversion Hlc; subst. simpl. split.
    + intros (b1 & b2 & E1 & E2 & V1 & V2 & Hall).
      exists b1, b2. repeat split; try assumption.
      intros U1 U2 Q HU1 HU2 HQ.
      assert (HF : ~ In X (fv_ty T)) by exact Hfresh.
      destruct (Hall U1 U2 Q HU1 HU2 HQ) as (r1 & r2 & Hr1 & Hr2 & Hout).
      exists r1, r2. repeat split; try assumption.
      pose proof (IHT rho (Q :: bound) X R r1 r2 HF H1) as [I1 I2].
      apply I1. exact Hout.
    + intros (b1 & b2 & E1 & E2 & V1 & V2 & Hall).
      exists b1, b2. repeat split; try assumption.
      intros U1 U2 Q HU1 HU2 HQ.
      assert (HF : ~ In X (fv_ty T)) by exact Hfresh.
      destruct (Hall U1 U2 Q HU1 HU2 HQ) as (r1 & r2 & Hr1 & Hr2 & Hout).
      exists r1, r2. repeat split; try assumption.
      pose proof (IHT rho (Q :: bound) X R r1 r2 HF H1) as [I1 I2].
      apply I2. exact Hout.
  - simpl. tauto.
Qed.

Lemma value_relation_bound_irrelevant : forall rho T k,
  lc_ty_at k T ->
  forall prefix b1 b2 v1 v2, length prefix = k ->
  value_relation rho (prefix ++ b1) T v1 v2 <-> value_relation rho (prefix ++ b2) T v1 v2.
Proof.
  intros rho T. induction T; intros k Hlc prefix b1 b2 v1 v2 Hlen; simpl in *.
  - inversion Hlc; subst. rewrite !nth_error_app1 by lia. tauto.
  - tauto.
  - inversion Hlc; subst. split; intros H.
    + destruct H as (A1 & c1 & A2 & c2 & E1 & E2 & V1 & V2 & Hall).
      exists A1, c1, A2, c2. repeat split; try assumption.
      intros a1 a2 Ha.
      pose proof (IHT1 (length prefix) H2 prefix b1 b2 a1 a2 eq_refl) as [I1 I2].
      destruct (Hall a1 a2 (I2 Ha)) as (r1 & r2 & Hr1 & Hr2 & Hout).
      exists r1, r2. repeat split; try assumption.
      pose proof (IHT2 (length prefix) H3 prefix b1 b2 r1 r2 eq_refl) as [J1 J2].
      apply J1. exact Hout.
    + destruct H as (A1 & c1 & A2 & c2 & E1 & E2 & V1 & V2 & Hall).
      exists A1, c1, A2, c2. repeat split; try assumption.
      intros a1 a2 Ha.
      pose proof (IHT1 (length prefix) H2 prefix b1 b2 a1 a2 eq_refl) as [I1 I2].
      destruct (Hall a1 a2 (I1 Ha)) as (r1 & r2 & Hr1 & Hr2 & Hout).
      exists r1, r2. repeat split; try assumption.
      pose proof (IHT2 (length prefix) H3 prefix b1 b2 r1 r2 eq_refl) as [J1 J2].
      apply J2. exact Hout.
  - inversion Hlc; subst. split; intros (c1 & c2 & E1 & E2 & V1 & V2 & Hall);
      exists c1, c2; repeat split; try assumption.
    + intros U1 U2 Q HU1 HU2 HQ.
      destruct (Hall U1 U2 Q HU1 HU2 HQ) as (r1 & r2 & Hr1 & Hr2 & Hout).
      exists r1, r2. repeat split; try assumption.
      pose proof (IHT (S (length prefix)) H1 (Q :: prefix) b1 b2 r1 r2 eq_refl) as [I1 I2].
      apply I1. exact Hout.
    + intros U1 U2 Q HU1 HU2 HQ.
      destruct (Hall U1 U2 Q HU1 HU2 HQ) as (r1 & r2 & Hr1 & Hr2 & Hout).
      exists r1, r2. repeat split; try assumption.
      pose proof (IHT (S (length prefix)) H1 (Q :: prefix) b1 b2 r1 r2 eq_refl) as [I1 I2].
      apply I2. exact Hout.
  - tauto.
Qed.

Lemma value_relation_open_ty_general : forall rho bound T U R v1 v2,
  lc_ty_at (S (length bound)) T ->
  locally_closed_ty U ->
  (forall x y, R x y <-> value_relation rho bound U x y) ->
  value_relation rho (bound ++ [R]) T v1 v2 <->
  value_relation rho bound (open_ty_rec (length bound) U T) v1 v2.
Proof.
  intros rho bound T. revert rho bound.
  induction T; intros rho bound U R v1 v2 Hlc HU HR; simpl in *.
  - inversion Hlc; subst.
    destruct (Nat.eqb (length bound) n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. rewrite nth_error_app2 by lia.
      replace (length bound - length bound) with 0 by lia. simpl. apply HR.
    + apply Nat.eqb_neq in E. rewrite nth_error_app1 by lia. tauto.
  - tauto.
  - inversion Hlc; subst. simpl. split; intros H.
    + destruct H as (A1 & b1 & A2 & b2 & E1 & E2 & V1 & V2 & Hall).
      exists A1, b1, A2, b2. repeat split; try assumption.
      intros a1 a2 Ha.
      pose proof (IHT1 rho bound U R a1 a2 H2 HU HR) as [I1 I2].
      pose proof (IHT2 rho bound U R v1 v2 H3 HU HR) as [J1 J2].
      destruct (Hall a1 a2 (I2 Ha)) as (r1 & r2 & Hr1 & Hr2 & Hout).
      exists r1, r2. repeat split; try assumption.
      pose proof (IHT2 rho bound U R r1 r2 H3 HU HR) as [K1 K2].
      apply K1. exact Hout.
    + destruct H as (A1 & b1 & A2 & b2 & E1 & E2 & V1 & V2 & Hall).
      exists A1, b1, A2, b2. repeat split; try assumption.
      intros a1 a2 Ha.
      pose proof (IHT1 rho bound U R a1 a2 H2 HU HR) as [I1 I2].
      destruct (Hall a1 a2 (I1 Ha)) as (r1 & r2 & Hr1 & Hr2 & Hout).
      exists r1, r2. repeat split; try assumption.
      pose proof (IHT2 rho bound U R r1 r2 H3 HU HR) as [K1 K2].
      apply K2. exact Hout.
  - inversion Hlc; subst. simpl. split.
    + intros (b1 & b2 & E1 & E2 & V1 & V2 & Hall).
      exists b1, b2. repeat split; try assumption.
      intros U1 U2 Q HU1 HU2 HQ.
      destruct (Hall U1 U2 Q HU1 HU2 HQ) as (r1 & r2 & Hr1 & Hr2 & Hout).
      exists r1, r2. repeat split; try assumption.
      assert (HRQ : forall x y, R x y <-> value_relation rho (Q :: bound) U x y).
      { intro x; intro y. pose proof (value_relation_bound_irrelevant rho U 0 HU [] bound (Q :: bound) x y eq_refl) as [J1 J2].
        split; intro Hxy.
        - apply J1. apply (proj1 (HR x y)). exact Hxy.
        - apply (proj2 (HR x y)). apply J2. exact Hxy. }
      pose proof (IHT rho (Q :: bound) U R r1 r2 H1 HU HRQ) as [I1 I2].
      apply I1. exact Hout.
    + intros (b1 & b2 & E1 & E2 & V1 & V2 & Hall).
      exists b1, b2. repeat split; try assumption.
      intros U1 U2 Q HU1 HU2 HQ.
      destruct (Hall U1 U2 Q HU1 HU2 HQ) as (r1 & r2 & Hr1 & Hr2 & Hout).
      exists r1, r2. repeat split; try assumption.
      assert (HRQ : forall x y, R x y <-> value_relation rho (Q :: bound) U x y).
      { intro x; intro y. pose proof (value_relation_bound_irrelevant rho U 0 HU [] bound (Q :: bound) x y eq_refl) as [J1 J2].
        split; intro Hxy.
        - apply J1. apply (proj1 (HR x y)). exact Hxy.
        - apply (proj2 (HR x y)). apply J2. exact Hxy. }
      pose proof (IHT rho (Q :: bound) U R r1 r2 H1 HU HRQ) as [I1 I2].
      apply I2. exact Hout.
  - tauto.
Qed.

Lemma value_relation_values : forall rho bound T v1 v2,
  (forall X, relation_value_closed (rho X)) ->
  Forall relation_value_closed bound ->
  value_relation rho bound T v1 v2 -> value v1 /\ value v2.
Proof.
  induction T; intros v1 v2 Hrho Hbound Hrel; simpl in Hrel.
  - destruct (nth_error bound n) as [R|] eqn:E; try contradiction.
    apply Forall_forall with (x := R) in Hbound.
    + eauto.
    + apply nth_error_In in E. exact E.
  - eapply Hrho; eauto.
  - destruct Hrel as (A1 & b1 & A2 & b2 & -> & -> & Hv1 & Hv2 & H). auto.
  - destruct Hrel as (b1 & b2 & -> & -> & Hv1 & Hv2 & H). auto.
  - destruct Hrel as [[H1 H2] | [H1 H2]]; subst; split; constructor.
Qed.

Lemma instantiate_open_tm_rec : forall t k x theta gamma u,
  ~ In x (fv_tm t) -> term_substitution_closed gamma ->
  instantiate theta (term_subst_update gamma x u)
      (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k u (instantiate theta gamma t).
Proof.
  induction t; intros k x theta gamma u Hfresh Hgamma; simpl in *.
  - destruct (Nat.eqb k n); [unfold term_subst_update; simpl; rewrite Nat.eqb_refl; reflexivity|reflexivity].
  - simpl in Hfresh. unfold term_subst_update. simpl.
    destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply Hfresh. simpl. auto.
    + destruct (Nat.eqb x a); [congruence|].
      erewrite open_tm_rec_lc_at; [reflexivity|].
      eapply (lc_tm_at_monotone 0 0 0 k); [apply Hgamma|lia|lia].
  - f_equal. apply IHt; assumption.
  - simpl in Hfresh. f_equal.
    + apply IHt1; [intro H; apply Hfresh; apply in_or_app; left; exact H|exact Hgamma].
    + apply IHt2; [intro H; apply Hfresh; apply in_or_app; right; exact H|exact Hgamma].
  - f_equal. apply IHt; assumption.
  - f_equal. apply IHt; assumption.
  - reflexivity.
  - reflexivity.
  - simpl in Hfresh. f_equal.
    + apply IHt1; [intro H; apply Hfresh; apply in_or_app; left; exact H|exact Hgamma].
    + apply IHt2; [intro H; apply Hfresh; apply in_or_app; right; apply in_or_app; left; exact H|exact Hgamma].
    + apply IHt3; [intro H; apply Hfresh; apply in_or_app; right; apply in_or_app; right; exact H|exact Hgamma].
  - simpl in Hfresh. f_equal.
    + apply IHt1; [intro H; apply Hfresh; apply in_or_app; left; exact H|exact Hgamma].
    + apply IHt2; [intro H; apply Hfresh; apply in_or_app; right; exact H|exact Hgamma].
Qed.

Lemma instantiate_open_tm : forall t x theta gamma u,
  ~ In x (fv_tm t) -> term_substitution_closed gamma ->
  instantiate theta (term_subst_update gamma x u) (open_tm t (tm_fvar x)) =
  open_tm (instantiate theta gamma t) u.
Proof. intros; apply instantiate_open_tm_rec; assumption. Qed.

Lemma instantiate_ty_open_ty_rec : forall T k X theta U,
  ~ In X (fv_ty T) -> type_substitution_closed theta ->
  instantiate_ty (type_subst_update theta X U)
      (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k U (instantiate_ty theta T).
Proof.
  induction T; intros k X theta U Hfresh Htheta; simpl in *.
  - destruct (Nat.eqb k n); [unfold type_subst_update; simpl; rewrite Nat.eqb_refl; reflexivity|reflexivity].
  - simpl in Hfresh. destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply Hfresh. simpl. auto.
    + unfold type_subst_update. simpl. rewrite E.
      erewrite open_ty_rec_lc_at; [reflexivity|].
      eapply lc_ty_at_monotone; [apply Htheta|lia].
  - simpl in Hfresh. f_equal.
    + apply IHT1; [intro H; apply Hfresh; apply in_or_app; left; exact H|exact Htheta].
    + apply IHT2; [intro H; apply Hfresh; apply in_or_app; right; exact H|exact Htheta].
  - f_equal. apply IHT; assumption.
  - reflexivity.
Qed.

Lemma instantiate_open_tm_ty_rec : forall t k X theta gamma U,
  ~ In X (ftv_tm t) -> type_substitution_closed theta -> term_substitution_closed gamma ->
  instantiate (type_subst_update theta X U) gamma
      (open_tm_ty_rec k (Ty_FVar X) t) =
  open_tm_ty_rec k U (instantiate theta gamma t).
Proof.
  induction t; intros k X theta gamma U Hfresh Htheta Hgamma; simpl in *.
  - reflexivity.
  - erewrite open_tm_ty_rec_lc_at; [reflexivity|].
    eapply (lc_tm_at_monotone 0 0 k 0); [apply Hgamma|lia|lia].
  - simpl in Hfresh. f_equal.
    + apply instantiate_ty_open_ty_rec.
      * intro H. apply Hfresh. apply in_or_app. left. exact H.
      * exact Htheta.
    + apply IHt.
      * intro H. apply Hfresh. apply in_or_app. right. exact H.
      * exact Htheta.
      * exact Hgamma.
  - simpl in Hfresh. f_equal.
    + apply IHt1.
      * intro H. apply Hfresh. apply in_or_app. left. exact H.
      * exact Htheta.
      * exact Hgamma.
    + apply IHt2.
      * intro H. apply Hfresh. apply in_or_app. right. exact H.
      * exact Htheta.
      * exact Hgamma.
  - f_equal. apply IHt; assumption.
  - simpl in Hfresh. f_equal.
    + apply IHt.
      * intro H. apply Hfresh. apply in_or_app. left. exact H.
      * exact Htheta.
      * exact Hgamma.
    + apply instantiate_ty_open_ty_rec.
      * intro H. apply Hfresh. apply in_or_app. right. exact H.
      * exact Htheta.
  - reflexivity.
  - reflexivity.
  - simpl in Hfresh. f_equal.
    + apply IHt1.
      * intro H. apply Hfresh. apply in_or_app. left. exact H.
      * exact Htheta.
      * exact Hgamma.
    + apply IHt2.
      * intro H. apply Hfresh. apply in_or_app. right. apply in_or_app. left. exact H.
      * exact Htheta.
      * exact Hgamma.
    + apply IHt3.
      * intro H. apply Hfresh. apply in_or_app. right. apply in_or_app. right. exact H.
      * exact Htheta.
      * exact Hgamma.
  - simpl in Hfresh. f_equal.
    + apply IHt1.
      * intro H. apply Hfresh. apply in_or_app. left. exact H.
      * exact Htheta.
      * exact Hgamma.
    + apply IHt2.
      * intro H. apply Hfresh. apply in_or_app. right. exact H.
      * exact Htheta.
      * exact Hgamma.
Qed.

Lemma wf_ty_locally_closed : forall Delta T,
  wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T Hwf. induction Hwf.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; assumption.
  - unfold locally_closed_ty. apply lc_ty_all. apply lc_ty_at_open_inv with (X := fresh L).
    apply H0. apply fresh_notin.
  - apply lc_ty_bool.
Qed.

Lemma has_type_locally_closed : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T Hty. induction Hty.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + apply wf_ty_locally_closed with (Delta := Delta); assumption.
    + unfold locally_closed_tm in *.
      apply lc_tm_at_open_tm_inv with (x := fresh L).
      * apply H1. apply fresh_notin.
  - apply lc_tm_app; assumption.
  - apply lc_tm_tabs. unfold locally_closed_tm in *.
    apply lc_tm_at_open_ty_inv with (X := fresh L).
    + apply H0. apply fresh_notin.
  - apply lc_tm_tapp; [assumption|apply wf_ty_locally_closed with (Delta := Delta); assumption].
  - apply lc_tm_true.
  - apply lc_tm_false.
  - apply lc_tm_if; assumption.
  - apply lc_tm_choice; assumption.
Qed.

Lemma has_type_ty_locally_closed : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_ty T.
Proof.
  intros Delta Gamma t T Hty. induction Hty.
  - apply wf_ty_locally_closed with (Delta := Delta). assumption.
  - apply lc_ty_arrow.
    + apply wf_ty_locally_closed with (Delta := Delta). assumption.
    + specialize (H1 (fresh L)). apply H1. apply fresh_notin.
  - inversion IHHty1; assumption.
  - unfold locally_closed_ty. apply lc_ty_all.
    apply lc_ty_at_open_inv with (X := fresh L).
    apply H0. apply fresh_notin.
  - inversion IHHty; subst.
    apply lc_ty_at_open with (k := 0).
    + assumption.
    + apply wf_ty_locally_closed with (Delta := Delta). assumption.
  - apply lc_ty_bool.
  - apply lc_ty_bool.
  - exact IHHty2.
  - exact IHHty1.
Qed.

Lemma instantiate_ty_preserves_lc : forall theta k T,
  lc_ty_at k T -> type_substitution_closed theta ->
  lc_ty_at k (instantiate_ty theta T).
Proof.
  intros theta k T Hlc. induction Hlc; intros Htheta; simpl.
  - apply lc_ty_bvar. assumption.
  - eapply lc_ty_at_monotone; [apply Htheta|lia].
  - apply lc_ty_arrow; auto.
  - apply lc_ty_all. apply IHHlc. exact Htheta.
  - apply lc_ty_bool.
Qed.

Lemma instantiate_preserves_lc : forall theta gamma K k t,
  lc_tm_at K k t -> type_substitution_closed theta ->
  term_substitution_closed gamma ->
  lc_tm_at K k (instantiate theta gamma t).
Proof.
  intros theta gamma K k t Hlc. revert theta gamma.
  induction Hlc; intros theta gamma Htheta Hgamma; simpl.
  - apply lc_tm_bvar. assumption.
  - eapply lc_tm_at_monotone; [apply Hgamma|lia|lia].
  - apply lc_tm_abs.
    + eapply instantiate_ty_preserves_lc; eauto.
    + eapply IHHlc; eauto.
  - apply lc_tm_app; eauto.
  - apply lc_tm_tabs. eapply IHHlc; eauto.
  - apply lc_tm_tapp.
    + eapply IHHlc; eauto.
    + eapply instantiate_ty_preserves_lc; eauto.
  - apply lc_tm_true.
  - apply lc_tm_false.
  - apply lc_tm_if; eauto.
  - apply lc_tm_choice; eauto.
Qed.

Theorem fundamental_theorem : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall theta1 theta2 rho gamma1 gamma2,
    type_substitution_closed theta1 ->
    type_substitution_closed theta2 ->
    term_substitution_closed gamma1 ->
    term_substitution_closed gamma2 ->
    relation_substitution_good rho ->
    related_context Gamma gamma1 gamma2 rho ->
    exists v1 v2,
      evaluates (instantiate theta1 gamma1 t) v1 /\
      evaluates (instantiate theta2 gamma2 t) v2 /\
      value_relation rho [] T v1 v2.
Proof.
  intros Delta Gamma t T Hty.
  induction Hty; intros theta1 theta2 rho gamma1 gamma2 Htheta1 Htheta2
    Hgamma1 Hgamma2 Hrho Hctx.
  - pose proof (Hctx x T H) as Hrel.
    pose proof (value_relation_values rho [] T (gamma1 x) (gamma2 x)
      Hrho (Forall_nil _) Hrel) as [Hv1 Hv2].
    exists (gamma1 x), (gamma2 x). split.
    + apply EvalValue. exact Hv1.
    + split.
      * apply EvalValue. exact Hv2.
      * exact Hrel.
  - set (z := fresh (L ++ fv_tm t2 ++ dom_context Gamma)).
    assert (HzL : ~ In z L).
    { unfold z. intro Hin. apply (fresh_notin (L ++ fv_tm t2 ++ dom_context Gamma)).
      apply in_or_app. left. exact Hin. }
    assert (Hzfv : ~ In z (fv_tm t2)).
    { unfold z. intro Hin. apply (fresh_notin (L ++ fv_tm t2 ++ dom_context Gamma)).
      apply in_or_app. right. apply in_or_app. left. exact Hin. }
    assert (Hzdom : ~ In z (dom_context Gamma)).
    { unfold z. intro Hin. apply (fresh_notin (L ++ fv_tm t2 ++ dom_context Gamma)).
      apply in_or_app. right. apply in_or_app. right. exact Hin. }
    assert (Hopenlc : locally_closed_tm (open_tm t2 (tm_fvar z))).
    { eapply has_type_locally_closed. apply H0. exact HzL. }
    assert (Hbodylc : lc_tm_at 0 1 t2).
    { unfold locally_closed_tm in Hopenlc. eapply lc_tm_at_open_tm_inv; eauto. }
    assert (Hsourceabs : locally_closed_tm (tm_abs T1 t2)).
    { apply lc_tm_abs.
      - apply wf_ty_locally_closed with (Delta := Delta). exact H.
      - exact Hbodylc. }
    assert (Habs1 : value (tm_abs (instantiate_ty theta1 T1) (instantiate theta1 gamma1 t2))).
    { apply v_abs. change (locally_closed_tm (instantiate theta1 gamma1 (tm_abs T1 t2))).
      eapply instantiate_preserves_lc; [exact Hsourceabs|exact Htheta1|exact Hgamma1]. }
    assert (Habs2 : value (tm_abs (instantiate_ty theta2 T1) (instantiate theta2 gamma2 t2))).
    { apply v_abs. change (locally_closed_tm (instantiate theta2 gamma2 (tm_abs T1 t2))).
      eapply instantiate_preserves_lc; [exact Hsourceabs|exact Htheta2|exact Hgamma2]. }
    exists (tm_abs (instantiate_ty theta1 T1) (instantiate theta1 gamma1 t2)),
      (tm_abs (instantiate_ty theta2 T1) (instantiate theta2 gamma2 t2)).
    split.
    + simpl. apply EvalValue. exact Habs1.
    + split.
      * simpl. apply EvalValue. exact Habs2.
      * exists (instantiate_ty theta1 T1), (instantiate theta1 gamma1 t2),
          (instantiate_ty theta2 T1), (instantiate theta2 gamma2 t2).
        repeat split; try reflexivity; try assumption.
        intros a1 a2 Ha.
        pose proof (value_relation_values rho [] T1 a1 a2 Hrho (Forall_nil _) Ha)
          as [Hva1 Hva2].
        pose proof (related_context_update_term Gamma gamma1 gamma2 rho z T1 a1 a2
          Hctx Ha Hzdom) as Hctx'.
        pose proof (H1 z HzL theta1 theta2 rho
          (term_subst_update gamma1 z a1) (term_subst_update gamma2 z a2)
          Htheta1 Htheta2
          (term_subst_update_closed gamma1 z a1 Hgamma1 (value_regular a1 Hva1))
          (term_subst_update_closed gamma2 z a2 Hgamma2 (value_regular a2 Hva2))
          Hrho Hctx') as (r1 & r2 & He1 & He2 & Hrel).
        exists r1, r2. split.
        -- rewrite <- (instantiate_open_tm t2 z theta1 gamma1 a1 Hzfv Hgamma1).
           exact He1.
        -- split.
           ++ rewrite <- (instantiate_open_tm t2 z theta2 gamma2 a2 Hzfv Hgamma2).
              exact He2.
           ++ exact Hrel.
  - destruct (IHHty1 theta1 theta2 rho gamma1 gamma2 Htheta1 Htheta2
      Hgamma1 Hgamma2 Hrho Hctx) as (f1 & f2 & Hf1 & Hf2 & Hfr).
    destruct (IHHty2 theta1 theta2 rho gamma1 gamma2 Htheta1 Htheta2
      Hgamma1 Hgamma2 Hrho Hctx) as (a1 & a2 & Ha1 & Ha2 & Har).
    destruct Hfr as (A1 & b1 & A2 & b2 & Ef1 & Ef2 & Vf1 & Vf2 & Hbeh).
    destruct (Hbeh a1 a2 Har) as (r1 & r2 & Hb1 & Hb2 & Hrel).
    exists r1, r2. split.
    + simpl. eapply EvalApp with (U := A1) (body := b1) (v := a1).
      * rewrite Ef1 in Hf1. exact Hf1.
      * exact Ha1.
      * exact Hb1.
    + split.
      * simpl. eapply EvalApp with (U := A2) (body := b2) (v := a2).
        -- rewrite Ef2 in Hf2. exact Hf2.
        -- exact Ha2.
        -- exact Hb2.
      * exact Hrel.
  - set (z := fresh (L ++ ftv_tm t ++ fv_ty T ++ ftv_context Gamma)).
    assert (HzL : ~ In z L).
    { unfold z. intro Hin. apply (fresh_notin (L ++ ftv_tm t ++ fv_ty T ++ ftv_context Gamma)).
      apply in_or_app. left. exact Hin. }
    assert (Hzftv : ~ In z (ftv_tm t)).
    { unfold z. intro Hin. apply (fresh_notin (L ++ ftv_tm t ++ fv_ty T ++ ftv_context Gamma)).
      apply in_or_app. right. apply in_or_app. left. exact Hin. }
    assert (HzT : ~ In z (fv_ty T)).
    { unfold z. intro Hin. apply (fresh_notin (L ++ ftv_tm t ++ fv_ty T ++ ftv_context Gamma)).
      apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hin. }
    assert (HzGamma : ~ In z (ftv_context Gamma)).
    { unfold z. intro Hin. apply (fresh_notin (L ++ ftv_tm t ++ fv_ty T ++ ftv_context Gamma)).
      apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact Hin. }
    assert (HopenTyLC : locally_closed_ty (open_ty T (Ty_FVar z))).
    { eapply has_type_ty_locally_closed. apply H. exact HzL. }
    assert (HTbodyLC : lc_ty_at 1 T).
    { unfold locally_closed_ty in HopenTyLC. eapply lc_ty_at_open_inv; eauto. }
    assert (HopenTmLC : locally_closed_tm (open_tm_ty t (Ty_FVar z))).
    { eapply has_type_locally_closed. apply H. exact HzL. }
    assert (HbodyLC : lc_tm_at 1 0 t).
    { unfold locally_closed_tm in HopenTmLC. eapply lc_tm_at_open_ty_inv; eauto. }
    assert (HsourceTabs : locally_closed_tm (tm_tabs t)).
    { apply lc_tm_tabs. exact HbodyLC. }
    assert (Htabs1 : value (tm_tabs (instantiate theta1 gamma1 t))).
    { apply v_tabs. change (locally_closed_tm (instantiate theta1 gamma1 (tm_tabs t))).
      eapply instantiate_preserves_lc; [exact HsourceTabs|exact Htheta1|exact Hgamma1]. }
    assert (Htabs2 : value (tm_tabs (instantiate theta2 gamma2 t))).
    { apply v_tabs. change (locally_closed_tm (instantiate theta2 gamma2 (tm_tabs t))).
      eapply instantiate_preserves_lc; [exact HsourceTabs|exact Htheta2|exact Hgamma2]. }
    exists (tm_tabs (instantiate theta1 gamma1 t)), (tm_tabs (instantiate theta2 gamma2 t)).
    split.
    + simpl. apply EvalValue. exact Htabs1.
    + split.
      * simpl. apply EvalValue. exact Htabs2.
      * exists (instantiate theta1 gamma1 t), (instantiate theta2 gamma2 t).
        repeat split; try reflexivity; try assumption.
        intros U1 U2 Q HU1 HU2 HQ.
        pose proof (type_subst_update_closed theta1 z U1 Htheta1 HU1) as Htheta1'.
        pose proof (type_subst_update_closed theta2 z U2 Htheta2 HU2) as Htheta2'.
        pose proof (relation_substitution_good_update rho z Q Hrho HQ) as Hrho'.
        pose proof (related_context_update_typevar Gamma gamma1 gamma2 rho z Q
          Hctx HzGamma) as Hctx'.
        destruct (H0 z HzL
          (type_subst_update theta1 z U1) (type_subst_update theta2 z U2)
          (relation_subst_update rho z Q) gamma1 gamma2
          Htheta1' Htheta2' Hgamma1 Hgamma2 Hrho' Hctx')
          as (r1 & r2 & He1 & He2 & Hrel).
        exists r1, r2. split.
        -- unfold open_tm_ty. rewrite <- (instantiate_open_tm_ty_rec t 0 z theta1 gamma1 U1
             Hzftv Htheta1 Hgamma1). exact He1.
        -- split.
           ++ unfold open_tm_ty. rewrite <- (instantiate_open_tm_ty_rec t 0 z theta2 gamma2 U2
                Hzftv Htheta2 Hgamma2). exact He2.
           ++ apply (proj2 (value_relation_open_ty rho [] T z Q r1 r2 HzT HTbodyLC)).
              exact Hrel.

  - destruct (IHHty theta1 theta2 rho gamma1 gamma2 Htheta1 Htheta2
      Hgamma1 Hgamma2 Hrho Hctx) as (f1 & f2 & Hf1 & Hf2 & Hfr).
    destruct Hfr as (b1 & b2 & Ef1 & Ef2 & Vf1 & Vf2 & Hforall).
    set (U1 := instantiate_ty theta1 U).
    set (U2 := instantiate_ty theta2 U).
    set (R := fun a b => value_relation rho [] U a b).
    assert (HUlc : locally_closed_ty U).
    { apply wf_ty_locally_closed with (Delta := Delta). exact H. }
    assert (HU1 : locally_closed_ty U1).
    { unfold U1. eapply instantiate_ty_preserves_lc; [|exact Htheta1].
      apply wf_ty_locally_closed with (Delta := Delta). exact H. }
    assert (HU2 : locally_closed_ty U2).
    { unfold U2. eapply instantiate_ty_preserves_lc; [|exact Htheta2].
      apply wf_ty_locally_closed with (Delta := Delta). exact H. }
    assert (HRgood : forall x y, R x y -> value x /\ value y).
    { intros x y Hxy. unfold R in Hxy.
      eapply value_relation_values; [exact Hrho|constructor|exact Hxy]. }
    pose proof (Hforall U1 U2 R HU1 HU2 HRgood) as
      (r1 & r2 & Hb1 & Hb2 & Hrel).
    assert (HTlc : lc_ty_at 1 T).
    { pose proof (has_type_ty_locally_closed Delta Gamma t (Ty_All T) Hty) as Halllc.
      inversion Halllc; assumption. }
    assert (HRrel : forall a b, R a b <-> value_relation rho [] U a b).
    { intros a b. unfold R. tauto. }
    pose proof (value_relation_open_ty_general rho [] T U R r1 r2 HTlc HUlc HRrel)
      as [Hopen Hclose].
    exists r1, r2. split.
    + simpl. eapply EvalTApp with (body := b1).
      * rewrite Ef1 in Hf1. exact Hf1.
      * exact HU1.
      * exact Hb1.
    + split.
      * simpl. eapply EvalTApp with (body := b2).
        -- rewrite Ef2 in Hf2. exact Hf2.
        -- exact HU2.
        -- exact Hb2.
      * apply Hopen. exact Hrel.
  - exists tm_true, tm_true. split.
    + simpl. apply EvalValue. apply v_true.
    + split.
      * simpl. apply EvalValue. apply v_true.
      * simpl. left. split; reflexivity.
  - exists tm_false, tm_false. split.
    + simpl. apply EvalValue. apply v_false.
    + split.
      * simpl. apply EvalValue. apply v_false.
      * simpl. right. split; reflexivity.
  - destruct (IHHty1 theta1 theta2 rho gamma1 gamma2 Htheta1 Htheta2
      Hgamma1 Hgamma2 Hrho Hctx) as (c1 & c2 & Hc1 & Hc2 & Hcr).
    destruct (IHHty2 theta1 theta2 rho gamma1 gamma2 Htheta1 Htheta2
      Hgamma1 Hgamma2 Hrho Hctx) as (r1 & r2 & Hr1 & Hr2 & Hrel1).
    destruct (IHHty3 theta1 theta2 rho gamma1 gamma2 Htheta1 Htheta2
      Hgamma1 Hgamma2 Hrho Hctx) as (s1 & s2 & Hs1 & Hs2 & Hrel2).
    destruct Hcr as [[Ec1 Ec2] | [Ec1 Ec2]].
    + pose proof (has_type_locally_closed Delta Gamma t3 T Hty3) as Hlc3.
      assert (Hlc3a : locally_closed_tm (instantiate theta1 gamma1 t3)).
      { eapply instantiate_preserves_lc; eauto. }
      assert (Hlc3b : locally_closed_tm (instantiate theta2 gamma2 t3)).
      { eapply instantiate_preserves_lc; eauto. }
      exists r1, r2. split.
      * simpl. eapply EvalIfTrue.
        -- rewrite Ec1 in Hc1. exact Hc1.
        -- exact Hr1.
        -- exact Hlc3a.
      * split.
        -- simpl. eapply EvalIfTrue.
           ++ rewrite Ec2 in Hc2. exact Hc2.
           ++ exact Hr2.
           ++ exact Hlc3b.
        -- exact Hrel1.
    + pose proof (has_type_locally_closed Delta Gamma t2 T Hty2) as Hlc2.
      assert (Hlc2a : locally_closed_tm (instantiate theta1 gamma1 t2)).
      { eapply instantiate_preserves_lc; eauto. }
      assert (Hlc2b : locally_closed_tm (instantiate theta2 gamma2 t2)).
      { eapply instantiate_preserves_lc; eauto. }
      exists s1, s2. split.
      * simpl. eapply EvalIfFalse.
        -- rewrite Ec1 in Hc1. exact Hc1.
        -- exact Hlc2a.
        -- exact Hs1.
      * split.
        -- simpl. eapply EvalIfFalse.
           ++ rewrite Ec2 in Hc2. exact Hc2.
           ++ exact Hlc2b.
           ++ exact Hs2.
        -- exact Hrel2.
  - destruct (IHHty1 theta1 theta2 rho gamma1 gamma2 Htheta1 Htheta2
      Hgamma1 Hgamma2 Hrho Hctx) as (r1 & r2 & Hr1 & Hr2 & Hrel).
    pose proof (has_type_locally_closed Delta Gamma t2 T Hty2) as Hlc2.
    assert (Hlc2a : locally_closed_tm (instantiate theta1 gamma1 t2)).
    { eapply instantiate_preserves_lc; eauto. }
    assert (Hlc2b : locally_closed_tm (instantiate theta2 gamma2 t2)).
    { eapply instantiate_preserves_lc; eauto. }
    exists r1, r2. split.
    + simpl. eapply EvalChoiceLeft; [exact Hr1|exact Hlc2a].
    + split.
      * simpl. eapply EvalChoiceLeft; [exact Hr2|exact Hlc2b].
      * exact Hrel.
Qed.

Lemma evaluates_result_value : forall t v,
  evaluates t v -> value v.
Proof. intros t v Hev. induction Hev; eauto. Qed.

Lemma evaluates_source_locally_closed : forall t v,
  evaluates t v -> locally_closed_tm t.
Proof.
  intros t v Hev. induction Hev.
  - apply value_regular. assumption.
  - apply lc_tm_app; assumption.
  - apply lc_tm_tapp; assumption.
  - apply lc_tm_if; assumption.
  - apply lc_tm_if; assumption.
  - apply lc_tm_choice; assumption.
  - apply lc_tm_choice; assumption.
Qed.

Lemma evaluates_to_multi : forall t v,
  evaluates t v -> t -->* v.
Proof.
  intros t v Hev. induction Hev.
  - constructor.
  - eapply multi_trans.
    + eapply multi_app_left; [exact IHHev1|].
      apply evaluates_source_locally_closed with (v := v). exact Hev2.
    + eapply multi_trans.
      * apply multi_app_right.
        -- apply evaluates_result_value with (t := f). exact Hev1.
        -- exact IHHev2.
      * eapply multi_step.
        -- apply ST_AppAbs.
           ++ apply value_regular. eapply evaluates_result_value; exact Hev1.
           ++ apply evaluates_result_value with (t := arg). exact Hev2.
        -- exact IHHev3.
  - eapply multi_trans.
    + apply multi_tapp; [exact IHHev1|exact H].
    + eapply multi_step.
      * apply ST_TAppTabs.
        -- apply value_regular. eapply evaluates_result_value; exact Hev1.
        -- exact H.
      * exact IHHev2.
  - eapply multi_trans.
    + eapply multi_if.
      * exact IHHev1.
      * apply evaluates_source_locally_closed with (v := v). exact Hev2.
      * assumption.
    + eapply multi_step.
      * apply ST_IfTrue.
        -- apply evaluates_source_locally_closed with (v := v). exact Hev2.
        -- assumption.
      * exact IHHev2.
  - eapply multi_trans.
    + eapply multi_if.
      * exact IHHev1.
      * assumption.
      * apply evaluates_source_locally_closed with (v := v). exact Hev2.
    + eapply multi_step.
      * apply ST_IfFalse.
        -- assumption.
        -- apply evaluates_source_locally_closed with (v := v). exact Hev2.
      * exact IHHev2.
  - eapply multi_step.
    + apply ST_ChoiceLeft.
      * apply evaluates_source_locally_closed with (v := v). exact Hev.
      * assumption.
    + exact IHHev.
  - eapply multi_step.
    + apply ST_ChoiceRight.
      * assumption.
      * apply evaluates_source_locally_closed with (v := v). exact Hev.
    + exact IHHev.
Qed.

Lemma instantiate_ty_identity : forall T,
  instantiate_ty identity_type_substitution T = T.
Proof. induction T; simpl; try rewrite IHT1; try rewrite IHT2; try rewrite IHT; reflexivity. Qed.

Lemma instantiate_identity : forall t,
  instantiate identity_type_substitution identity_term_substitution t = t.
Proof.
  induction t; simpl; try rewrite instantiate_ty_identity;
    try rewrite IHt; try rewrite IHt1; try rewrite IHt2; try rewrite IHt3;
    reflexivity.
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
  set (rho0 := fun (_ : atom) => fun (_ _ : tm) => False).
  assert (Hrho0 : relation_substitution_good rho0).
  { intros X a b Hab. contradiction. }
  assert (Hctx0 : related_context empty identity_term_substitution
    identity_term_substitution rho0).
  { intros x T Hlookup. discriminate. }
  destruct (fundamental_theorem [] empty t
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) Ht
    identity_type_substitution identity_type_substitution rho0
    identity_term_substitution identity_term_substitution
    identity_type_substitution_closed identity_type_substitution_closed
    identity_term_substitution_closed identity_term_substitution_closed
    Hrho0 Hctx0) as (r1 & r2 & He1 & He2 & Hpoly).
  rewrite !instantiate_identity in He1, He2.
  simpl in Hpoly.
  destruct Hpoly as (b1 & b2 & Er1 & Er2 & Vr1 & Vr2 & Hall).
  pose proof (wf_ty_locally_closed [] U HU) as HUlc.
  set (R := fun x y => x = v /\ y = v).
  assert (HRgood : relation_value_closed R).
  { intros x y Hxy. destruct Hxy as [-> ->]. split; assumption. }
  destruct (Hall U U R HUlc HUlc HRgood) as
    (q1 & q2 & Hq1 & Hq2 & Hqrel).
  simpl in Hqrel.
  destruct Hqrel as (A1 & c1 & A2 & c2 & Eq1 & Eq2 & Vq1 & Vq2 & Hbeh).
  assert (Hargrel : value_relation rho0 [R] (Ty_BVar 0) v v).
  { simpl. unfold R. auto. }
  destruct (Hbeh v v Hargrel) as (o1 & o2 & Ho1 & Ho2 & Houtrel).
  simpl in Houtrel. unfold R in Houtrel.
  destruct Houtrel as [Ho1eq Ho2eq]. subst o1 o2.
  assert (Htapp : evaluates (tm_tapp t U) q1).
  { eapply EvalTApp with (body := b1).
    - rewrite Er1 in He1. exact He1.
    - exact HUlc.
    - exact Hq1. }
  assert (Htapp_abs : evaluates (tm_tapp t U) (tm_abs A1 c1)).
  { rewrite <- Eq1. exact Htapp. }
  eapply evaluates_to_multi.
  eapply EvalApp with (U := A1) (body := c1) (v := v) (result := v).
  - exact Htapp_abs.
  - apply EvalValue. exact Hv.
  - exact Ho1.
Qed.

End SystemFParametricityIfNondeterminismEasyTask.
