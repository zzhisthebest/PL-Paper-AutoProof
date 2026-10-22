(** System F parametricity benchmark, Easy variant.
    Features: if. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFParametricityIfEasyTask.

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
      evaluates (tm_if c t u) v.

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

Definition unary_type_env := atom -> tm -> Prop.

Definition unary_type_env_update (rho : unary_type_env) (X : atom)
    (P : tm -> Prop) : unary_type_env :=
  fun Y => if Nat.eqb X Y then P else rho Y.

Fixpoint logical_value (rho : unary_type_env) (bound : list (tm -> Prop))
    (T : ty) (v : tm) {struct T} : Prop :=
  match T with
  | Ty_BVar i => nth i bound (fun _ => False) v
  | Ty_FVar X => rho X v
  | Ty_Arrow A B =>
      value v /\ forall a, value a -> logical_value rho bound A a ->
        exists w, evaluates (tm_app v a) w /\ logical_value rho bound B w
  | Ty_All B =>
      value v /\ forall U P, locally_closed_ty U ->
        (forall a, P a -> value a) ->
        exists w, evaluates (tm_tapp v U) w /\
          logical_value rho (P :: bound) B w
  | Ty_Bool => v = tm_true \/ v = tm_false
  end.

Lemma logical_value_open_ty_rec : forall T k X rho P bound v,
  ~ In X (fv_ty T) -> nth k bound (fun _ => False) = P ->
  (logical_value (unary_type_env_update rho X P) bound
      (open_ty_rec k (Ty_FVar X) T) v <->
   logical_value rho bound T v).
Proof.
  induction T; intros k X rho P bound v Hfresh Hnth; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n.
      unfold unary_type_env_update. simpl. rewrite Nat.eqb_refl, Hnth. tauto.
    + tauto.
  - simpl in Hfresh. simpl. unfold unary_type_env_update.
    destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E. exfalso. apply Hfresh. left. symmetry. exact E.
    + tauto.
  - simpl. assert (~ In X (fv_ty T1) /\ ~ In X (fv_ty T2))
      as [Hfresh1 Hfresh2].
    { rewrite in_app_iff in Hfresh. tauto. }
    split.
    + intros [Hv Hfun]. split; [exact Hv|]. intros a0 Hval Ha.
      pose proof (IHT1 k X rho P bound a0 Hfresh1 Hnth) as Hdom.
      apply (proj2 Hdom) in Ha.
      destruct (Hfun a0 Hval Ha) as [w [He Hr]].
      pose proof (IHT2 k X rho P bound w Hfresh2 Hnth) as Hcod.
      apply (proj1 Hcod) in Hr. exists w; auto.
    + intros [Hv Hfun]. split; [exact Hv|]. intros a0 Hval Ha.
      pose proof (IHT1 k X rho P bound a0 Hfresh1 Hnth) as Hdom.
      apply (proj1 Hdom) in Ha.
      destruct (Hfun a0 Hval Ha) as [w [He Hr]].
      pose proof (IHT2 k X rho P bound w Hfresh2 Hnth) as Hcod.
      apply (proj2 Hcod) in Hr. exists w; auto.
  - simpl. split.
    + intros [Hv Hall]. split; [exact Hv|]. intros U Q HU HQ.
      destruct (Hall U Q HU HQ) as [w [He Hr]].
      pose proof (IHT (S k) X rho P (Q :: bound) w Hfresh) as Hopen.
      assert (nth (S k) (Q :: bound) (fun _ => False) = P) as Hnth'.
      { simpl. exact Hnth. }
      apply (proj1 (Hopen Hnth')) in Hr.
      exists w; auto.
    + intros [Hv Hall]. split; [exact Hv|]. intros U Q HU HQ.
      destruct (Hall U Q HU HQ) as [w [He Hr]].
      pose proof (IHT (S k) X rho P (Q :: bound) w Hfresh) as Hopen.
      assert (nth (S k) (Q :: bound) (fun _ => False) = P) as Hnth'.
      { simpl. exact Hnth. }
      apply (proj2 (Hopen Hnth')) in Hr.
      exists w; auto.
  - tauto.
Qed.

Definition unary_env_value_property (rho : unary_type_env) : Prop :=
  forall X v, rho X v -> value v.

Definition bound_value_property (bound : list (tm -> Prop)) : Prop :=
  forall i v, nth i bound (fun _ => False) v -> value v.

Lemma logical_value_is_value : forall T rho bound v,
  unary_env_value_property rho -> bound_value_property bound ->
  logical_value rho bound T v -> value v.
Proof.
  induction T; intros rho bound v Hrho Hbound Hrel; simpl in Hrel.
  - eapply Hbound. exact Hrel.
  - eapply Hrho. exact Hrel.
  - destruct Hrel as [Hv _]. exact Hv.
  - destruct Hrel as [Hv _]. exact Hv.
  - destruct Hrel as [Heq|Heq]; subst; constructor.
Qed.

Lemma bound_value_property_cons : forall P bound,
  (forall v, P v -> value v) -> bound_value_property bound ->
  bound_value_property (P :: bound).
Proof.
  intros P bound HP Hb i v H. destruct i; simpl in H.
  - eapply HP; eauto.
  - eapply Hb; eauto.
Qed.

Lemma logical_value_bound_independent : forall k T,
  lc_ty_at k T -> forall rho b1 b2 v,
  (forall i, i < k -> nth i b1 (fun _ => False) = nth i b2 (fun _ => False)) ->
  (logical_value rho b1 T v <-> logical_value rho b2 T v).
Proof.
  intros k T Hlc. induction Hlc; intros rho b1 b2 v Hprefix; simpl.
  - rewrite (Hprefix i H). tauto.
  - tauto.
  - split.
    + intros [Hv Hfun]. split; [exact Hv|]. intros a Ha Hrel.
      apply (proj2 (IHHlc1 rho b1 b2 a Hprefix)) in Hrel.
      destruct (Hfun a Ha Hrel) as [w [He Hr]].
      apply (proj1 (IHHlc2 rho b1 b2 w Hprefix)) in Hr.
      exists w; auto.
    + intros [Hv Hfun]. split; [exact Hv|]. intros a Ha Hrel.
      apply (proj1 (IHHlc1 rho b1 b2 a Hprefix)) in Hrel.
      destruct (Hfun a Ha Hrel) as [w [He Hr]].
      apply (proj2 (IHHlc2 rho b1 b2 w Hprefix)) in Hr.
      exists w; auto.
  - split.
    + intros [Hv Hall]. split; [exact Hv|]. intros U P HU HP.
      destruct (Hall U P HU HP) as [w [He Hr]].
      assert (forall i, i < S k ->
          nth i (P :: b1) (fun _ => False) = nth i (P :: b2) (fun _ => False)) as Hp.
      { intros [|i] Hi; simpl; auto. apply Hprefix. lia. }
      apply (proj1 (IHHlc rho (P :: b1) (P :: b2) w Hp)) in Hr.
      exists w; auto.
    + intros [Hv Hall]. split; [exact Hv|]. intros U P HU HP.
      destruct (Hall U P HU HP) as [w [He Hr]].
      assert (forall i, i < S k ->
          nth i (P :: b1) (fun _ => False) = nth i (P :: b2) (fun _ => False)) as Hp.
      { intros [|i] Hi; simpl; auto. apply Hprefix. lia. }
      apply (proj2 (IHHlc rho (P :: b1) (P :: b2) w Hp)) in Hr.
      exists w; auto.
  - tauto.
Qed.

Lemma logical_value_env_irrelevant : forall T rho X P bound v,
  ~ In X (fv_ty T) ->
  (logical_value (unary_type_env_update rho X P) bound T v <->
   logical_value rho bound T v).
Proof.
  induction T; intros rho X P bound v Hfresh; simpl in *.
  - tauto.
  - simpl in Hfresh. unfold unary_type_env_update.
    destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E. exfalso. apply Hfresh. left. symmetry. exact E.
    + tauto.
  - assert (~ In X (fv_ty T1) /\ ~ In X (fv_ty T2)) as [H1 H2].
    { rewrite in_app_iff in Hfresh. tauto. }
    simpl. split.
    + intros [Hv Hfun]. split; [exact Hv|]. intros a Hval Ha.
      pose proof (IHT1 rho X P bound a H1) as Hd.
      apply (proj2 Hd) in Ha.
      destruct (Hfun a Hval Ha) as [w [He Hr]].
      pose proof (IHT2 rho X P bound w H2) as Hc.
      apply (proj1 Hc) in Hr. exists w; auto.
    + intros [Hv Hfun]. split; [exact Hv|]. intros a Hval Ha.
      pose proof (IHT1 rho X P bound a H1) as Hd.
      apply (proj1 Hd) in Ha.
      destruct (Hfun a Hval Ha) as [w [He Hr]].
      pose proof (IHT2 rho X P bound w H2) as Hc.
      apply (proj2 Hc) in Hr. exists w; auto.
  - simpl. split.
    + intros [Hv Hall]. split; [exact Hv|]. intros U Q HU HQ.
      destruct (Hall U Q HU HQ) as [w [He Hr]].
      pose proof (IHT rho X P (Q :: bound) w Hfresh) as Hrrel.
      apply (proj1 Hrrel) in Hr. exists w; auto.
    + intros [Hv Hall]. split; [exact Hv|]. intros U Q HU HQ.
      destruct (Hall U Q HU HQ) as [w [He Hr]].
      pose proof (IHT rho X P (Q :: bound) w Hfresh) as Hrrel.
      apply (proj2 Hrrel) in Hr. exists w; auto.
  - tauto.
Qed.

Fixpoint insert_bound (k : nat) (P : tm -> Prop)
    (bound : list (tm -> Prop)) : list (tm -> Prop) :=
  match k, bound with
  | 0, _ => P :: bound
  | S k', Q :: bound' => Q :: insert_bound k' P bound'
  | S _, [] => []
  end.

Lemma insert_bound_nth_lt : forall k P bound i,
  k <= length bound -> i < k ->
  nth i (insert_bound k P bound) (fun _ => False) =
  nth i bound (fun _ => False).
Proof.
  induction k; intros P bound i Hlen Hi; simpl in *.
  - lia.
  - destruct bound as [|Q bound']; simpl in *; [lia|].
    destruct i; simpl.
    + reflexivity.
    + apply IHk; lia.
Qed.

Lemma insert_bound_nth_eq : forall k P bound,
  k <= length bound ->
  nth k (insert_bound k P bound) (fun _ => False) = P.
Proof.
  induction k; intros P bound Hlen; simpl.
  - reflexivity.
  - destruct bound as [|Q bound']; simpl in *; [lia|].
    rewrite IHk by lia. reflexivity.
Qed.

Lemma logical_value_bound_independent_zero : forall T rho b1 b2 v,
  lc_ty_at 0 T -> logical_value rho b1 T v <-> logical_value rho b2 T v.
Proof.
  intros. eapply logical_value_bound_independent; eauto.
  intros i Hi. lia.
Qed.

Lemma logical_value_open_ty_subst : forall k T,
  lc_ty_at (S k) T -> forall rho bound P U v,
  k <= length bound -> lc_ty_at 0 U ->
  (forall a, P a <-> logical_value rho bound U a) ->
  (logical_value rho (insert_bound k P bound) T v <->
   logical_value rho bound (open_ty_rec k U T) v).
Proof.
  intros k T. revert k. induction T; intros k Hlc rho bound P U v Hlen HU HP; simpl.
  - inversion Hlc; subst.
    destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n.
      rewrite insert_bound_nth_eq by exact Hlen.
      rewrite HP. tauto.
    + assert (n < k) by (apply Nat.eqb_neq in E; lia).
      rewrite insert_bound_nth_lt by assumption. tauto.
  - inversion Hlc; subst. tauto.
  - inversion Hlc; subst.
    simpl. split.
    + intros [Hv Hfun]. split; [exact Hv|]. intros a Ha Hra.
      pose proof (IHT1 k H2 rho bound P U a Hlen HU HP) as Hd.
      apply (proj2 Hd) in Hra.
      destruct (Hfun a Ha Hra) as [w [He Hr]].
      pose proof (IHT2 k H3 rho bound P U w Hlen HU HP) as Hc.
      apply (proj1 Hc) in Hr. exists w; auto.
    + intros [Hv Hfun]. split; [exact Hv|]. intros a Ha Hra.
      pose proof (IHT1 k H2 rho bound P U a Hlen HU HP) as Hd.
      apply (proj1 Hd) in Hra.
      destruct (Hfun a Ha Hra) as [w [He Hr]].
      pose proof (IHT2 k H3 rho bound P U w Hlen HU HP) as Hc.
      apply (proj2 Hc) in Hr. exists w; auto.
  - inversion Hlc; subst. simpl. split.
    + intros [Hv Hall]. split; [exact Hv|]. intros V Q HV HQ.
      destruct (Hall V Q HV HQ) as [w [He Hr]].
      assert (S k <= length (Q :: bound)) as Hlen' by (simpl; lia).
      assert (forall a, P a <-> logical_value rho (Q :: bound) U a) as HP'.
      { intros a. pose proof (logical_value_bound_independent_zero U rho bound
          (Q :: bound) a HU) as Hbi. rewrite HP. exact Hbi. }
      pose proof (IHT (S k) H1 rho (Q :: bound) P U w Hlen' HU HP') as Hopen.
      apply (proj1 Hopen) in Hr. exists w; auto.
    + intros [Hv Hall]. split; [exact Hv|]. intros V Q HV HQ.
      destruct (Hall V Q HV HQ) as [w [He Hr]].
      assert (S k <= length (Q :: bound)) as Hlen' by (simpl; lia).
      assert (forall a, P a <-> logical_value rho (Q :: bound) U a) as HP'.
      { intros a. pose proof (logical_value_bound_independent_zero U rho bound
          (Q :: bound) a HU) as Hbi. rewrite HP. exact Hbi. }
      pose proof (IHT (S k) H1 rho (Q :: bound) P U w Hlen' HU HP') as Hopen.
      apply (proj2 Hopen) in Hr. exists w; auto.
  - inversion Hlc; subst. tauto.
Qed.

Lemma logical_value_open_ty_free : forall k T,
  lc_ty_at (S k) T -> forall rho bound X P v,
  k <= length bound -> ~ In X (fv_ty T) ->
  (logical_value (unary_type_env_update rho X P) bound
      (open_ty_rec k (Ty_FVar X) T) v <->
   logical_value rho (insert_bound k P bound) T v).
Proof.
  intros k T. revert k. induction T; intros k Hlc rho bound X P v Hlen Hfresh; simpl.
  - inversion Hlc; subst.
    destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n.
      unfold unary_type_env_update. simpl. rewrite Nat.eqb_refl.
      rewrite insert_bound_nth_eq by exact Hlen. tauto.
    + apply Nat.eqb_neq in E. assert (n < k) by lia.
      rewrite insert_bound_nth_lt by assumption. tauto.
  - inversion Hlc; subst. simpl in Hfresh. unfold unary_type_env_update.
    destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E. exfalso. apply Hfresh. left. symmetry. exact E.
    + tauto.
  - inversion Hlc; subst.
    assert (~ In X (fv_ty T1) /\ ~ In X (fv_ty T2)) as [Hf1 Hf2].
    { simpl in Hfresh. rewrite in_app_iff in Hfresh. tauto. }
    simpl. split.
    + intros [Hv Hfun]. split; [exact Hv|]. intros a Ha Hra.
      pose proof (IHT1 k H2 rho bound X P a Hlen Hf1) as Hd.
      apply (proj2 Hd) in Hra.
      destruct (Hfun a Ha Hra) as [w [He Hr]].
      pose proof (IHT2 k H3 rho bound X P w Hlen Hf2) as Hc.
      apply (proj1 Hc) in Hr. exists w; auto.
    + intros [Hv Hfun]. split; [exact Hv|]. intros a Ha Hra.
      pose proof (IHT1 k H2 rho bound X P a Hlen Hf1) as Hd.
      apply (proj1 Hd) in Hra.
      destruct (Hfun a Ha Hra) as [w [He Hr]].
      pose proof (IHT2 k H3 rho bound X P w Hlen Hf2) as Hc.
      apply (proj2 Hc) in Hr. exists w; auto.
  - inversion Hlc; subst. simpl. split.
    + intros [Hv Hall]. split; [exact Hv|]. intros U Q HU HQ.
      destruct (Hall U Q HU HQ) as [w [He Hr]].
      assert (S k <= length (Q :: bound)) as Hlen' by (simpl; lia).
      assert (~ In X (fv_ty T)) as Hf by exact Hfresh.
      pose proof (IHT (S k) H1 rho (Q :: bound) X P w Hlen' Hf) as Hopen.
      apply (proj1 Hopen) in Hr. exists w; auto.
    + intros [Hv Hall]. split; [exact Hv|]. intros U Q HU HQ.
      destruct (Hall U Q HU HQ) as [w [He Hr]].
      assert (S k <= length (Q :: bound)) as Hlen' by (simpl; lia).
      assert (~ In X (fv_ty T)) as Hf by exact Hfresh.
      pose proof (IHT (S k) H1 rho (Q :: bound) X P w Hlen' Hf) as Hopen.
      apply (proj2 Hopen) in Hr. exists w; auto.
  - inversion Hlc; subst. tauto.
Qed.

Definition logical_context (rho : unary_type_env) (bound : list (tm -> Prop))
    (Gamma : context) (gamma : term_substitution) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    exists v, gamma x = v /\ value v /\ logical_value rho bound T v.

Lemma lookup_context_ftv : forall Gamma x T X,
  lookup_context x Gamma = Some T -> In X (fv_ty T) ->
  In X (ftv_context Gamma).
Proof.
  induction Gamma as [|[y A] Gamma IH]; intros x T X Hlookup Hfv; simpl in *.
  - discriminate.
  - unfold lookup_context in Hlookup at 1. simpl in Hlookup.
    destruct (Nat.eqb x y) eqn:E.
    + inversion Hlookup; subst. apply in_or_app. left. exact Hfv.
    + apply in_or_app. right. eapply IH; eauto.
Qed.

Lemma logical_context_type_env_update : forall rho bound Gamma gamma X P,
  (forall x T, lookup_context x Gamma = Some T -> ~ In X (fv_ty T)) ->
  logical_context rho bound Gamma gamma ->
  logical_context (unary_type_env_update rho X P) bound Gamma gamma.
Proof.
  intros rho bound Gamma gamma X P Hfresh Hctx x T Hlookup.
  destruct (Hctx x T Hlookup) as [v [E [Hv Hrel]]].
  exists v. repeat split; try assumption.
  pose proof (logical_value_env_irrelevant T rho X P bound v
      (Hfresh x T Hlookup)) as Hirr.
  apply (proj2 Hirr). exact Hrel.
Qed.

Lemma logical_context_term_update : forall rho bound Gamma gamma x T a,
  logical_context rho bound Gamma gamma -> value a ->
  logical_value rho bound T a ->
  logical_context rho bound (update Gamma x T)
    (term_subst_update gamma x a).
Proof.
  intros rho bound Gamma gamma x T a Hctx Ha Hrel y S Hlook.
  unfold update in Hlook. unfold lookup_context in Hlook at 1. simpl in Hlook.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y. inversion Hlook; subst S.
    exists a. repeat split; try assumption.
    unfold term_subst_update. rewrite Nat.eqb_refl. reflexivity.
  - assert (x <> y) as Hneq by (intro Heq; subst; rewrite Nat.eqb_refl in E; discriminate).
    destruct (Hctx y S Hlook) as [v [Ev [Hv Hvr]]].
    exists v. repeat split; try assumption.
    unfold term_subst_update. simpl.
    destruct (Nat.eqb x y) eqn:Exy.
    + apply Nat.eqb_eq in Exy. contradiction.
    + exact Ev.
Qed.

Lemma evaluates_local_closed : forall t v,
  evaluates t v -> locally_closed_tm t.
Proof.
  intros t v H. induction H.
  - apply value_regular in H. exact H.
  - apply lc_tm_app; assumption.
  - apply lc_tm_tapp; assumption.
  - apply lc_tm_if; assumption.
  - apply lc_tm_if; assumption.
Qed.

Lemma evaluates_value : forall t v,
  evaluates t v -> value v.
Proof.
  intros t v H. induction H; assumption.
Qed.

Lemma evaluates_multi : forall t v,
  evaluates t v -> t -->* v.
Proof.
  intros t v H. induction H.
  - constructor.
  - eapply multi_trans.
    + eapply multi_app_left; [exact IHevaluates1|].
      eapply evaluates_local_closed. exact H0.
    + eapply multi_trans.
      * eapply multi_app_right; [eapply evaluates_value; exact H|exact IHevaluates2].
      * eapply multi_step.
        -- apply ST_AppAbs.
           ++ eapply value_regular. eapply evaluates_value. exact H.
           ++ eapply evaluates_value. exact H0.
        -- exact IHevaluates3.
  - eapply multi_trans.
    + eapply multi_tapp; [exact IHevaluates1|assumption].
    + eapply multi_step.
      * apply ST_TAppTabs.
        -- eapply value_regular. eapply evaluates_value. exact H.
        -- exact H0.
      * exact IHevaluates2.
  - eapply multi_trans.
    + eapply multi_if.
      * exact IHevaluates1.
      * eapply evaluates_local_closed. exact H0.
      * exact H1.
    + eapply multi_trans.
      * eapply multi_step.
        -- apply ST_IfTrue.
           ++ eapply evaluates_local_closed. exact H0.
           ++ exact H1.
        -- constructor.
      * exact IHevaluates2.
  - eapply multi_trans.
    + eapply multi_if.
      * exact IHevaluates1.
      * exact H0.
      * eapply evaluates_local_closed. exact H1.
    + eapply multi_trans.
      * eapply multi_step.
        -- apply ST_IfFalse.
           ++ exact H0.
           ++ eapply evaluates_local_closed. exact H1.
        -- constructor.
      * exact IHevaluates2.
Qed.

Lemma wf_ty_locally_closed : forall Delta T,
  wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H. induction H.
  - constructor.
  - constructor; assumption.
  - apply lc_ty_all.
    eapply lc_ty_at_open_inv with (X := fresh L).
    exact (H0 (fresh L) (fresh_notin L)).
  - constructor.
Qed.

Lemma has_type_locally_closed_type : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_ty T.
Proof.
  intros Delta Gamma t T Hty. induction Hty.
  - eapply wf_ty_locally_closed. exact H0.
  - apply lc_ty_arrow.
    + eapply wf_ty_locally_closed. exact H.
    + specialize (H1 (fresh L) (fresh_notin L)). exact H1.
  - inversion IHHty1; subst. assumption.
  - apply lc_ty_all.
    pose proof (H0 (fresh L) (fresh_notin L)) as Hlc.
    eapply lc_ty_at_open_inv. exact Hlc.
  - inversion IHHty; subst.
    eapply lc_ty_at_open; [eassumption|].
    eapply wf_ty_locally_closed. exact H.
  - constructor.
  - constructor.
  - exact IHHty2.
Qed.

Lemma has_type_locally_closed : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T Hty. induction Hty.
  - constructor.
  - apply lc_tm_abs.
    + eapply wf_ty_locally_closed. exact H.
    + eapply lc_tm_at_open_tm_inv.
      exact (H1 (fresh L) (fresh_notin L)).
  - apply lc_tm_app; assumption.
  - apply lc_tm_tabs.
    eapply lc_tm_at_open_ty_inv.
    exact (H0 (fresh L) (fresh_notin L)).
  - apply lc_tm_tapp; [assumption|eapply wf_ty_locally_closed; eassumption].
  - constructor.
  - constructor.
  - apply lc_tm_if; assumption.
Qed.

Lemma instantiate_ty_locally_closed_at : forall theta K T,
  type_substitution_closed theta -> lc_ty_at K T ->
  lc_ty_at K (instantiate_ty theta T).
Proof.
  intros theta K T Htheta Hlc. induction Hlc; simpl.
  - constructor. assumption.
  - eapply lc_ty_at_monotone.
    + apply Htheta.
    + lia.
  - constructor; assumption.
  - constructor. assumption.
  - constructor.
Qed.

Lemma instantiate_locally_closed_at : forall theta gamma K k t,
  type_substitution_closed theta -> term_substitution_closed gamma ->
  lc_tm_at K k t -> lc_tm_at K k (instantiate theta gamma t).
Proof.
  intros theta gamma K k t Htheta Hgamma Hlc.
  induction Hlc; simpl.
  - constructor. assumption.
  - eapply lc_tm_at_monotone.
    + apply Hgamma.
    + lia.
    + lia.
  - apply lc_tm_abs.
    + eapply instantiate_ty_locally_closed_at; eauto.
    + assumption.
  - apply lc_tm_app; assumption.
  - apply lc_tm_tabs. assumption.
  - apply lc_tm_tapp.
    + assumption.
    + eapply instantiate_ty_locally_closed_at; eauto.
  - constructor.
  - constructor.
  - apply lc_tm_if; assumption.
Qed.

Lemma instantiate_locally_closed : forall theta gamma t,
  type_substitution_closed theta -> term_substitution_closed gamma ->
  locally_closed_tm t -> locally_closed_tm (instantiate theta gamma t).
Proof. intros; eapply instantiate_locally_closed_at; eauto. Qed.

Lemma instantiate_ty_open_commute : forall T k X U theta,
  type_substitution_closed theta -> ~ In X (fv_ty T) ->
  instantiate_ty (type_subst_update theta X U)
      (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k U (instantiate_ty theta T).
Proof.
  induction T; intros k X U theta Htheta Hfresh; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + unfold type_subst_update. simpl. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - simpl in Hfresh.
    unfold type_subst_update. simpl.
    destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E. exfalso. apply Hfresh. left. symmetry. exact E.
    + erewrite open_ty_rec_lc_at.
      * reflexivity.
      * eapply lc_ty_at_monotone; [apply Htheta|lia].
  - simpl. f_equal.
    + apply IHT1; [exact Htheta|].
      rewrite in_app_iff in Hfresh; tauto.
    + apply IHT2; [exact Htheta|].
      rewrite in_app_iff in Hfresh; tauto.
  - simpl. f_equal. apply IHT; assumption.
  - reflexivity.
Qed.

Lemma instantiate_tm_ty_open_commute_rec : forall t k X U theta gamma,
  type_substitution_closed theta -> term_substitution_closed gamma ->
  ~ In X (ftv_tm t) ->
  instantiate (type_subst_update theta X U) gamma
      (open_tm_ty_rec k (Ty_FVar X) t) =
  open_tm_ty_rec k U (instantiate theta gamma t).
Proof.
  induction t; intros k X U theta gamma Htheta Hgamma Hfresh; simpl in *.
  - reflexivity.
  - erewrite open_tm_ty_rec_lc_at.
    + reflexivity.
    + eapply lc_tm_at_monotone.
      * apply Hgamma.
      * lia.
      * lia.
  - simpl in Hfresh. rewrite in_app_iff in Hfresh.
    assert (~ In X (fv_ty t) /\ ~ In X (ftv_tm t0)) as [Hty Hbody].
    { tauto. }
    f_equal.
    + eapply instantiate_ty_open_commute; eauto.
    + eapply IHt; eauto.
  - simpl in Hfresh. repeat rewrite in_app_iff in Hfresh.
    assert (~ In X (ftv_tm t1) /\ ~ In X (ftv_tm t2)) as [H1 H2].
    { tauto. }
    f_equal.
    + eapply IHt1; eauto.
    + eapply IHt2; eauto.
  - f_equal. eapply IHt with (k := S k); eauto.
  - simpl in Hfresh. rewrite in_app_iff in Hfresh.
    assert (~ In X (ftv_tm t) /\ ~ In X (fv_ty t0)) as [Hterm Hty].
    { tauto. }
    f_equal.
    + eapply IHt; eauto.
    + eapply instantiate_ty_open_commute; eauto.
  - reflexivity.
  - reflexivity.
  - simpl in Hfresh. repeat rewrite in_app_iff in Hfresh.
    assert (~ In X (ftv_tm t1) /\ ~ In X (ftv_tm t2) /\ ~ In X (ftv_tm t3))
      as [H1 [H2 H3]] by tauto.
    rewrite (IHt1 k X U theta gamma Htheta Hgamma H1).
    rewrite (IHt2 k X U theta gamma Htheta Hgamma H2).
    rewrite (IHt3 k X U theta gamma Htheta Hgamma H3).
    reflexivity.
  Unshelve.
  all: try assumption.
Qed.

Lemma instantiate_tm_open_commute_rec : forall t k x arg theta gamma,
  term_substitution_closed gamma -> ~ In x (fv_tm t) ->
  instantiate theta (term_subst_update gamma x arg)
      (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k arg (instantiate theta gamma t).
Proof.
  induction t; intros k x arg theta gamma Hgamma Hfresh; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + unfold term_subst_update. simpl. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - simpl in Hfresh.
    unfold term_subst_update. simpl.
    destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E. exfalso. apply Hfresh. left. symmetry. exact E.
    + erewrite open_tm_rec_lc_at.
      * reflexivity.
      * eapply lc_tm_at_monotone.
        -- apply Hgamma.
        -- lia.
        -- lia.
  - simpl in Hfresh. f_equal. apply IHt with (k := S k); assumption.
  - simpl in Hfresh. repeat rewrite in_app_iff in Hfresh.
    assert (~ In x (fv_tm t1) /\ ~ In x (fv_tm t2)) as [H1 H2] by tauto.
    f_equal.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
  - f_equal. apply IHt; assumption.
  - f_equal. apply IHt; assumption.
  - reflexivity.
  - reflexivity.
  - simpl in Hfresh. repeat rewrite in_app_iff in Hfresh.
    assert (~ In x (fv_tm t1) /\ ~ In x (fv_tm t2) /\ ~ In x (fv_tm t3))
      as [H1 [H2 H3]] by tauto.
    rewrite (IHt1 k x arg theta gamma Hgamma H1).
    rewrite (IHt2 k x arg theta gamma Hgamma H2).
    rewrite (IHt3 k x arg theta gamma Hgamma H3). reflexivity.
  Unshelve.
  all: try assumption.
Qed.

Lemma instantiate_tm_open_commute : forall t x a theta gamma,
  term_substitution_closed gamma -> ~ In x (fv_tm t) ->
  instantiate theta (term_subst_update gamma x a)
      (open_tm t (tm_fvar x)) =
  open_tm (instantiate theta gamma t) a.
Proof. intros; apply instantiate_tm_open_commute_rec; assumption. Qed.

Lemma evaluates_application_function : forall f a w,
  evaluates (tm_app f a) w ->
  exists A body, evaluates f (tm_abs A body).
Proof.
  intros f a w H. inversion H; subst.
  - inversion H0.
  - eexists. eexists. eassumption.
Qed.

Lemma evaluates_value_source : forall v w,
  value v -> evaluates v w -> v = w.
Proof.
  intros v w Hv He. inversion Hv; subst; inversion He; subst; reflexivity.
Qed.

Lemma evaluates_abs_app_body : forall A body v w,
  value v -> evaluates (tm_app (tm_abs A body) v) w ->
  evaluates (open_tm body v) w.
Proof.
  intros A body v w Hv H. inversion H; subst.
  - inversion H0.
  - assert (tm_abs A body = tm_abs U body0) as Eabs.
    { eapply evaluates_value_source.
      - apply v_abs. eapply evaluates_local_closed. exact H2.
      - exact H2. }
    assert (v = v0) as Ev.
    { eapply evaluates_value_source; eauto. }
    inversion Eabs; subst. exact H5.
Qed.

Lemma evaluates_tapp_function : forall f U w,
  evaluates (tm_tapp f U) w ->
  exists body, evaluates f (tm_tabs body).
Proof.
  intros f U w H. inversion H; subst.
  - inversion H0.
  - eexists. eassumption.
Qed.

Lemma evaluates_tabs_tapp_body : forall body U w,
  evaluates (tm_tapp (tm_tabs body) U) w ->
  evaluates (open_tm_ty body U) w.
Proof.
  intros body U w H. inversion H; subst.
  - inversion H0.
  - pose proof (evaluates_local_closed _ _ H2) as Hlc.
    assert (value (tm_tabs body)) as Hv by (apply v_tabs; exact Hlc).
    assert (tm_tabs body = tm_tabs body0) as E.
    { eapply evaluates_value_source; eauto. }
    inversion E; subst. exact H5.
Qed.

Lemma logical_identity_gives_path : forall t U v,
  logical_value (fun _ _ => False) []
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) t ->
  locally_closed_ty U -> value v ->
  tm_app (tm_tapp t U) v -->* v.
Proof.
  intros t U v Hrel HU Hv.
  simpl in Hrel.
  destruct Hrel as [Htv Hall].
  specialize (Hall U (fun a => a = v) HU).
  assert (forall a, a = v -> value a) as Hpred.
  { intros a Ha. subst. exact Hv. }
  specialize (Hall Hpred).
  destruct Hall as [f [Htf Hfrel]].
  simpl in Hfrel. destruct Hfrel as [Hfv Hfun].
  specialize (Hfun v Hv).
  assert (logical_value (fun _ _ => False) [fun a => a = v]
      (Ty_BVar 0) v) as Hvr by (simpl; reflexivity).
  specialize (Hfun Hvr).
  destruct Hfun as [w [Happ Hwrel]].
  simpl in Hwrel. subst w.
  destruct (evaluates_application_function _ _ _ Happ)
    as [A [body Hfvalue]].
  assert (f = tm_abs A body) as Hfshape.
  { eapply evaluates_value_source; eauto. }
  subst f.
  eapply evaluates_multi.
  eapply EvalApp with (U := A) (body := body) (v := v).
  - exact Htf.
  - apply EvalValue. exact Hv.
  - eapply evaluates_abs_app_body; eauto.
Qed.

Lemma fundamental_theorem : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall rho bound theta gamma,
    unary_env_value_property rho ->
    bound_value_property bound ->
    type_substitution_closed theta ->
    term_substitution_closed gamma ->
    logical_context rho bound Gamma gamma ->
    exists v, evaluates (instantiate theta gamma t) v /\
      logical_value rho bound T v.
Proof.
  intros Delta Gamma t T HT. induction HT;
    intros rho bound theta gamma Hrho Hbound Htheta Hgamma Hctx.
  - destruct (Hctx x T H) as [v [E [Hv Hrel]]].
    exists v. split.
    + simpl. rewrite E. apply EvalValue. exact Hv.
    + exact Hrel.
  - set (x := fresh (L ++ fv_tm t2)).
    assert (~ In x L) as HnotL.
    { unfold x. intro Hin. apply fresh_notin with (L := L ++ fv_tm t2).
      apply in_or_app. left. exact Hin. }
    assert (~ In x (fv_tm t2)) as Hnotfv.
    { unfold x. intro Hin. apply fresh_notin with (L := L ++ fv_tm t2).
      apply in_or_app. right. exact Hin. }
    assert (locally_closed_tm (tm_abs T1 t2)) as HabsLC.
    { apply lc_tm_abs.
      - eapply wf_ty_locally_closed. exact H.
      - eapply lc_tm_at_open_tm_inv.
        apply has_type_locally_closed with (Delta := Delta)
          (Gamma := update Gamma x T1) (T := T2).
        apply H0. exact HnotL. }
    assert (value (instantiate theta gamma (tm_abs T1 t2))) as HabsValue.
    { apply v_abs.
      change (locally_closed_tm (instantiate theta gamma (tm_abs T1 t2))).
      eapply instantiate_locally_closed; eauto. }
    exists (instantiate theta gamma (tm_abs T1 t2)). split.
    + simpl. apply EvalValue. exact HabsValue.
    + simpl. split; [exact HabsValue|]. intros a Ha Hra.
      assert (logical_context rho bound (update Gamma x T1)
          (term_subst_update gamma x a)) as Hctx'.
      { eapply logical_context_term_update; eauto. }
      destruct (H1 x HnotL rho bound theta (term_subst_update gamma x a)
          Hrho Hbound Htheta
          (term_subst_update_closed gamma x a Hgamma (value_regular _ Ha))
          Hctx') as [w [He Hwr]].
      assert (instantiate theta (term_subst_update gamma x a)
          (open_tm t2 (tm_fvar x)) = open_tm (instantiate theta gamma t2) a)
        as Eopen.
      { apply instantiate_tm_open_commute; assumption. }
      rewrite Eopen in He.
      exists w. split.
      * eapply EvalApp with (U := instantiate_ty theta T1)
            (body := instantiate theta gamma t2) (v := a).
        -- apply EvalValue. exact HabsValue.
        -- apply EvalValue. exact Ha.
        -- exact He.
      * exact Hwr.
  - destruct (IHHT1 rho bound theta gamma Hrho Hbound Htheta Hgamma Hctx)
      as [f [Hf Hfr]].
    destruct (IHHT2 rho bound theta gamma Hrho Hbound Htheta Hgamma Hctx)
      as [a [Ha Har]].
    simpl in Hfr. destruct Hfr as [Hfv Hfun].
    pose proof (Hfun a (evaluates_value _ _ Ha) Har) as Happ.
    destruct Happ as [w [Happ Hwr]].
    destruct (evaluates_application_function _ _ _ Happ) as [A [body Hfapp]].
    assert (f = tm_abs A body) as Ef.
    { eapply evaluates_value_source; eauto using evaluates_value. }
    subst f.
    assert (evaluates (open_tm body a) w) as Hbody.
    { eapply evaluates_abs_app_body; eauto using evaluates_value. }
    exists w. split.
    + simpl. eapply EvalApp with (U := A) (body := body) (v := a); eauto.
    + exact Hwr.
  - set (X := fresh (L ++ fv_ty T ++ ftv_context Gamma ++ ftv_tm t)).
    assert (~ In X L) as HnotL.
    { unfold X. intro Hin. apply fresh_notin with
        (L := L ++ fv_ty T ++ ftv_context Gamma ++ ftv_tm t).
      repeat rewrite in_app_iff. tauto. }
    assert (~ In X (fv_ty T)) as HnotT.
    { unfold X. intro Hin. apply fresh_notin with
        (L := L ++ fv_ty T ++ ftv_context Gamma ++ ftv_tm t).
      repeat rewrite in_app_iff. tauto. }
    assert (~ In X (ftv_context Gamma)) as HnotGamma.
    { unfold X. intro Hin. apply fresh_notin with
        (L := L ++ fv_ty T ++ ftv_context Gamma ++ ftv_tm t).
      repeat rewrite in_app_iff. tauto. }
    assert (~ In X (ftv_tm t)) as Hnotterm.
    { unfold X. intro Hin. apply fresh_notin with
        (L := L ++ fv_ty T ++ ftv_context Gamma ++ ftv_tm t).
      repeat rewrite in_app_iff. tauto. }
    assert (locally_closed_tm (tm_tabs t)) as HtabsLC.
    { apply lc_tm_tabs. eapply lc_tm_at_open_ty_inv.
      apply has_type_locally_closed with (Delta := X :: Delta)
        (Gamma := Gamma) (T := open_ty T (Ty_FVar X)).
      apply H. exact HnotL. }
    assert (value (instantiate theta gamma (tm_tabs t))) as HtabsValue.
    { apply v_tabs.
      change (locally_closed_tm (instantiate theta gamma (tm_tabs t))).
      eapply instantiate_locally_closed; eauto. }
    exists (instantiate theta gamma (tm_tabs t)). split.
    + simpl. apply EvalValue. exact HtabsValue.
    + simpl. split; [exact HtabsValue|]. intros U P HU HP.
      assert (unary_env_value_property (unary_type_env_update rho X P)) as Hrho'.
      { intros Y a Hrel. unfold unary_type_env_update in Hrel.
        destruct (Nat.eqb X Y) eqn:E.
        - apply Nat.eqb_eq in E. subst. eapply HP. exact Hrel.
        - eapply Hrho. exact Hrel. }
      assert (type_substitution_closed (type_subst_update theta X U)) as Htheta'.
      { eapply type_subst_update_closed; eauto. }
      assert (logical_context (unary_type_env_update rho X P) bound
          Gamma gamma) as Hctx'.
      { apply logical_context_type_env_update; [|exact Hctx].
        intros y S Hlook Hin.
        apply HnotGamma. eapply lookup_context_ftv; eauto. }
      destruct (H0 X HnotL (unary_type_env_update rho X P) bound
          (type_subst_update theta X U) gamma Hrho' Hbound Htheta' Hgamma Hctx')
        as [w [Hbody Hwr]].
      assert (lc_ty_at 1 T) as HTlc.
      { pose proof (has_type_locally_closed_type (X :: Delta) Gamma
          (open_tm_ty t (Ty_FVar X)) (open_ty T (Ty_FVar X))
          (H X HnotL)) as HlcOpen.
        eapply lc_ty_at_open_inv. exact HlcOpen. }
      assert (logical_value (unary_type_env_update rho X P) bound
          (open_ty T (Ty_FVar X)) w <->
          logical_value rho (P :: bound) T w) as HopenTy.
      { unfold open_ty. eapply logical_value_open_ty_free.
        - exact HTlc.
        - simpl. lia.
        - exact HnotT. }
      apply (proj1 HopenTy) in Hwr.
      pose proof (instantiate_tm_ty_open_commute_rec t 0 X U theta gamma
          Htheta Hgamma Hnotterm) as Ecomm.
      unfold open_tm_ty in Hbody.
      rewrite Ecomm in Hbody.
      exists w. split.
      * simpl. eapply EvalTApp with (body := instantiate theta gamma t).
        -- apply EvalValue. exact HtabsValue.
        -- exact HU.
        -- exact Hbody.
      * exact Hwr.
  - destruct (IHHT rho bound theta gamma Hrho Hbound Htheta Hgamma Hctx)
      as [f [Hf Hfr]].
    simpl in Hfr. destruct Hfr as [Hfv Hall].
    assert (locally_closed_ty (instantiate_ty theta U)) as HUinst.
    { eapply instantiate_ty_locally_closed_at; eauto.
      eapply wf_ty_locally_closed. exact H. }
    set (P := fun a => logical_value rho bound U a).
    assert (forall a, P a -> value a) as HP.
    { intros a Ha. unfold P in Ha.
      eapply logical_value_is_value; eauto. }
    destruct (Hall (instantiate_ty theta U) P HUinst HP) as [w [Happ Hwr]].
    assert (lc_ty_at 1 T) as HTlc.
    { pose proof (has_type_locally_closed_type _ _ _ _ HT) as HtypeLC.
      inversion HtypeLC; assumption. }
    assert (logical_value rho (insert_bound 0 P bound) T w <->
        logical_value rho bound (open_ty T U) w) as HopenTy.
    { unfold open_ty. eapply logical_value_open_ty_subst; eauto; try lia.
      - eapply wf_ty_locally_closed. exact H.
      - intros a. unfold P. tauto. }
    apply (proj1 HopenTy) in Hwr.
    destruct (evaluates_tapp_function _ _ _ Happ) as [body Hftapp].
    assert (f = tm_tabs body) as Ef.
    { eapply evaluates_value_source; eauto using evaluates_value. }
    subst f.
    assert (evaluates (open_tm_ty body (instantiate_ty theta U)) w) as Hbody.
    { eapply evaluates_tabs_tapp_body. exact Happ. }
    exists w. split.
    + simpl. eapply EvalTApp with (body := body).
      * exact Hf.
      * exact HUinst.
      * exact Hbody.
    + exact Hwr.
  - exists tm_true. split; [apply EvalValue; constructor|]. simpl. left. reflexivity.
  - exists tm_false. split; [apply EvalValue; constructor|]. simpl. right. reflexivity.
  - destruct (IHHT1 rho bound theta gamma Hrho Hbound Htheta Hgamma Hctx)
      as [c [Hc Hcr]].
    destruct (IHHT2 rho bound theta gamma Hrho Hbound Htheta Hgamma Hctx)
      as [v [Hv Hvr]].
    destruct (IHHT3 rho bound theta gamma Hrho Hbound Htheta Hgamma Hctx)
      as [w [Hw Hwr]].
    simpl in Hcr. destruct Hcr as [Etrue|Efalse].
    + subst c. exists v. split.
      * eapply EvalIfTrue.
        -- exact Hc.
        -- exact Hv.
        -- eapply instantiate_locally_closed; [exact Htheta|exact Hgamma|].
           eapply has_type_locally_closed. exact HT3.
      * exact Hvr.
    + subst c. exists w. split.
      * eapply EvalIfFalse.
        -- exact Hc.
        -- eapply instantiate_locally_closed; [exact Htheta|exact Hgamma|].
           eapply has_type_locally_closed. exact HT2.
        -- exact Hw.
      * exact Hwr.
Qed.

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
  intros t HT U v HU Hv HTv.
  destruct (fundamental_theorem _ _ _ _ HT
      (fun _ _ => False) [] identity_type_substitution
      identity_term_substitution) as [w [Heval Hrel]].
  - intros X a Ha. contradiction.
  - intros i a Hi. destruct i; simpl in Hi; contradiction.
  - apply identity_type_substitution_closed.
  - apply identity_term_substitution_closed.
  - intros x T Hlookup. unfold empty in Hlookup. simpl in Hlookup. discriminate.
  - rewrite instantiate_identity in Heval.
    pose proof (evaluates_multi _ _ Heval) as Ht.
    eapply multi_trans.
    + eapply multi_trans.
      * eapply multi_app_left.
        -- eapply multi_tapp; [exact Ht|].
           eapply wf_ty_locally_closed. exact HU.
        -- eapply value_regular. exact Hv.
      * eapply logical_identity_gives_path; eauto.
        eapply wf_ty_locally_closed. exact HU.
    + constructor.
Qed.

End SystemFParametricityIfEasyTask.
