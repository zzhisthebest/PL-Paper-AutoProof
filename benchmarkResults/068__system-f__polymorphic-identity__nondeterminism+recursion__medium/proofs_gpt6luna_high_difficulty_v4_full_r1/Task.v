(** System F parametricity benchmark, Easy variant.
    Features: nondeterminism-recursion. *)

From Stdlib Require Import Arith.PeanoNat Arith.Wf_nat Lists.List Lia.
Import ListNotations.

Module SystemFParametricityNondeterminismRecursionEasyTask.

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
  | Ty_Nat : ty.

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
  | tm_zero : tm
  | tm_succ : tm -> tm
  | tm_natrec : tm -> tm -> tm -> tm
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

Notation "'Nat'" := Ty_Nat (in custom systemf_ty at level 0) : systemf_scope.
Notation "'zero'" := tm_zero (in custom systemf_tm at level 0) : systemf_scope.
Notation "'succ' t" := (tm_succ t) (in custom systemf_tm at level 9, t custom systemf_tm at level 0) : systemf_scope.
Notation "'rec' n b s" := (tm_natrec n b s)
  (in custom systemf_tm at level 9, n custom systemf_tm at level 0, b custom systemf_tm at level 0, s custom systemf_tm at level 0) : systemf_scope.
Notation "'choice' t1 'or' t2" := (tm_choice t1 t2)
  (in custom systemf_tm at level 200, t1 custom systemf_tm, t2 custom systemf_tm at level 200) : systemf_scope.

Fixpoint open_ty_rec (k : nat) (U T : ty) : ty :=
  match T with
  | Ty_BVar i => if Nat.eqb k i then U else Ty_BVar i
  | Ty_FVar X => Ty_FVar X
  | Ty_Arrow T1 T2 =>
      Ty_Arrow (open_ty_rec k U T1) (open_ty_rec k U T2)
  | Ty_All T1 => Ty_All (open_ty_rec (S k) U T1)
  | Ty_Nat => Ty_Nat
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
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (open_tm_rec k u t1)
  | tm_natrec n b f => tm_natrec (open_tm_rec k u n) (open_tm_rec k u b) (open_tm_rec k u f)
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
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (open_tm_ty_rec k U t1)
  | tm_natrec n b f => tm_natrec (open_tm_ty_rec k U n) (open_tm_ty_rec k U b) (open_tm_ty_rec k U f)
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
  | Ty_Nat => Ty_Nat
  end.

Fixpoint tm_ty_subst (X : atom) (U : ty) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T t1 => tm_abs (ty_subst X U T) (tm_ty_subst X U t1)
  | tm_app t1 t2 => tm_app (tm_ty_subst X U t1) (tm_ty_subst X U t2)
  | tm_tabs t1 => tm_tabs (tm_ty_subst X U t1)
  | tm_tapp t1 T => tm_tapp (tm_ty_subst X U t1) (ty_subst X U T)
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (tm_ty_subst X U t1)
  | tm_natrec n b f => tm_natrec (tm_ty_subst X U n) (tm_ty_subst X U b) (tm_ty_subst X U f)
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
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (tm_subst x s t1)
  | tm_natrec n b f => tm_natrec (tm_subst x s n) (tm_subst x s b) (tm_subst x s f)
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
  | lc_ty_nat : forall k, lc_ty_at k Ty_Nat.

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
  | lc_tm_zero : forall K k, lc_tm_at K k tm_zero
  | lc_tm_succ : forall K k t, lc_tm_at K k t -> lc_tm_at K k (tm_succ t)
  | lc_tm_rec : forall K k n b s,
      lc_tm_at K k n -> lc_tm_at K k b -> lc_tm_at K k s -> lc_tm_at K k (tm_natrec n b s)
  | lc_tm_choice : forall K k t1 t2,
      lc_tm_at K k t1 -> lc_tm_at K k t2 -> lc_tm_at K k (tm_choice t1 t2).

Definition locally_closed_tm (t : tm) : Prop := lc_tm_at 0 0 t.

Inductive numeric_value : tm -> Prop :=
  | nv_zero : numeric_value tm_zero
  | nv_succ : forall (n : tm), numeric_value n -> numeric_value (tm_succ n).

Fixpoint numeral (n : nat) : tm :=
  match n with O => tm_zero | S m => tm_succ (numeral m) end.

Inductive value : tm -> Prop :=
  | v_abs : forall T t,
      locally_closed_tm (tm_abs T t) ->
      value (tm_abs T t)
  | v_tabs : forall t,
      locally_closed_tm (tm_tabs t) ->
      value (tm_tabs t)
  | v_nat : forall n, numeric_value n -> value n.

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
  | ST_Succ : forall t t',
      t --> t' -> tm_succ t --> tm_succ t'
  | ST_RecArg : forall n n' b s,

      n --> n' -> locally_closed_tm b -> locally_closed_tm s ->
      tm_natrec n b s --> tm_natrec n' b s
  | ST_RecBase : forall n b b' s,

      numeric_value n -> b --> b' -> locally_closed_tm s ->
      tm_natrec n b s --> tm_natrec n b' s
  | ST_RecStep : forall n b s s',

      numeric_value n -> value b -> s --> s' ->
      tm_natrec n b s --> tm_natrec n b s'
  | ST_RecZero : forall b s,

      value b -> value s -> tm_natrec tm_zero b s --> b
  | ST_RecSucc : forall n b s,

      numeric_value n -> value b -> value s ->
      tm_natrec (tm_succ n) b s -->
        tm_app (tm_app s n) (tm_natrec n b s)
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
  | WF_Nat : forall Delta, wf_ty Delta Ty_Nat.

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
  | T_Zero : forall Delta Gamma, has_type Delta Gamma tm_zero Ty_Nat
  | T_Succ : forall Delta Gamma n,
      has_type Delta Gamma n Ty_Nat -> has_type Delta Gamma (tm_succ n) Ty_Nat
  | T_Rec : forall Delta Gamma n b s T,
      has_type Delta Gamma n Ty_Nat -> has_type Delta Gamma b T ->
      has_type Delta Gamma s (Ty_Arrow Ty_Nat (Ty_Arrow T T)) ->
      has_type Delta Gamma (tm_natrec n b s) T
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
  | Ty_Nat => []
  end.

Fixpoint fv_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs _ t1 => fv_tm t1
  | tm_app t1 t2 => fv_tm t1 ++ fv_tm t2
  | tm_tabs t1 => fv_tm t1
  | tm_tapp t1 _ => fv_tm t1
  | tm_zero => []
  | tm_succ t => fv_tm t
  | tm_natrec n b s => fv_tm n ++ fv_tm b ++ fv_tm s
  | tm_choice t1 t2 => fv_tm t1 ++ fv_tm t2
  end.

Fixpoint ftv_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_fvar _ => []
  | tm_abs T t1 => fv_ty T ++ ftv_tm t1
  | tm_app t1 t2 => ftv_tm t1 ++ ftv_tm t2
  | tm_tabs t1 => ftv_tm t1
  | tm_tapp t1 T => ftv_tm t1 ++ fv_ty T
  | tm_zero => []
  | tm_succ t => ftv_tm t
  | tm_natrec n b s => ftv_tm n ++ ftv_tm b ++ ftv_tm s
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
  - apply lc_ty_nat.
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
  - apply lc_tm_zero.
  - eauto using lc_tm_at.
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
  - rewrite IHHlc. reflexivity.
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
  - apply lc_ty_nat.
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
  - apply lc_ty_nat.
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
  - apply lc_tm_zero.
  - inversion Hlc; subst; eauto using lc_tm_at.
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
  - apply lc_tm_zero.
  - inversion Hlc; subst; eauto using lc_tm_at.
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
  | Ty_Nat => Ty_Nat
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
  | tm_zero => tm_zero
  | tm_succ t => tm_succ (instantiate theta gamma t)
  | tm_natrec n b s => tm_natrec (instantiate theta gamma n) (instantiate theta gamma b) (instantiate theta gamma s)
  | tm_choice t1 t2 => tm_choice (instantiate theta gamma t1) (instantiate theta gamma t2)
  end.

Lemma instantiate_ty_open_rec : forall theta k U T,
  (forall X, locally_closed_ty (theta X)) ->
  instantiate_ty theta (open_ty_rec k U T) =
  open_ty_rec k (instantiate_ty theta U) (instantiate_ty theta T).
Proof.
  intros theta k U T Hclosed. generalize dependent k.
  induction T; intros k; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - specialize (Hclosed a). simpl in Hclosed.
    symmetry.
    eapply open_ty_rec_lc_at.
    eapply lc_ty_at_monotone; [exact Hclosed|lia].
  - rewrite (IHT1 k), (IHT2 k). reflexivity.
  - rewrite (IHT (S k)). reflexivity.
  - reflexivity.
Qed.

Lemma instantiate_open_ty_rec : forall theta gamma K U t,
  (forall X, locally_closed_ty (theta X)) ->
  (forall x, locally_closed_tm (gamma x)) ->
  instantiate theta gamma (open_tm_ty_rec K U t) =
  open_tm_ty_rec K (instantiate_ty theta U) (instantiate theta gamma t).
Proof.
  intros theta gamma K U t Hclosed Hgamma. generalize dependent K.
  induction t; intros K; simpl.
  - reflexivity.
  - specialize (Hgamma a). unfold locally_closed_tm in Hgamma.
    symmetry.
    assert (Hlc : lc_tm_at K 0 (gamma a)).
    { eapply lc_tm_at_monotone; [exact Hgamma|lia|lia]. }
    rewrite (open_tm_ty_rec_lc_at (gamma a) K 0
      (instantiate_ty theta U) Hlc). reflexivity.
  - rewrite instantiate_ty_open_rec by exact Hclosed.
    rewrite IHt by assumption. reflexivity.
  - rewrite IHt1, IHt2; try assumption. reflexivity.
  - rewrite IHt; try assumption. reflexivity.
  - rewrite IHt by assumption. rewrite instantiate_ty_open_rec by exact Hclosed.
    reflexivity.
  - reflexivity.
  - rewrite IHt; try assumption. reflexivity.
  - rewrite IHt1, IHt2, IHt3; try assumption. reflexivity.
  - rewrite IHt1, IHt2; try assumption. reflexivity.
Qed.

Lemma instantiate_open_tm_rec : forall theta gamma k u t,
  (forall x, locally_closed_tm (gamma x)) ->
  instantiate theta gamma (open_tm_rec k u t) =
  open_tm_rec k (instantiate theta gamma u) (instantiate theta gamma t).
Proof.
  intros theta gamma k u t Hgamma. generalize dependent k.
  induction t; intros k; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - specialize (Hgamma a). unfold locally_closed_tm in Hgamma.
    symmetry.
    assert (Hlc : lc_tm_at 0 k (gamma a)).
    { eapply lc_tm_at_monotone; [exact Hgamma|lia|lia]. }
    rewrite (open_tm_rec_lc_at (gamma a) 0 k
      (instantiate theta gamma u) Hlc). reflexivity.
  - rewrite IHt by assumption. reflexivity.
  - rewrite IHt1, IHt2; try assumption. reflexivity.
  - rewrite IHt by assumption. reflexivity.
  - rewrite IHt by assumption. reflexivity.
  - reflexivity.
  - rewrite IHt by assumption. reflexivity.
  - rewrite IHt1, IHt2, IHt3; try assumption. reflexivity.
  - rewrite IHt1, IHt2; try assumption. reflexivity.
Qed.

Lemma instantiate_term_update_irrelevant : forall theta gamma x u t,
  ~ In x (fv_tm t) ->
  instantiate theta (term_subst_update gamma x u) t =
  instantiate theta gamma t.
Proof.
  intros theta gamma x u t. induction t; intros Hnot; simpl in *.
  - reflexivity.
  - destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply Hnot. simpl. auto.
    + unfold term_subst_update. rewrite E. reflexivity.
  - f_equal. apply IHt. exact Hnot.
  - f_equal.
    + apply IHt1. intro Hin. apply Hnot. apply in_or_app. left. exact Hin.
    + apply IHt2. intro Hin. apply Hnot. apply in_or_app. right. exact Hin.
  - f_equal. apply IHt. exact Hnot.
  - f_equal. apply IHt. exact Hnot.
  - reflexivity.
  - f_equal. apply IHt. exact Hnot.
  - f_equal.
    + apply IHt1. intro Hin. apply Hnot. apply in_or_app. left. exact Hin.
    + apply IHt2. intro Hin. apply Hnot. apply in_or_app. right. apply in_or_app. left. exact Hin.
    + apply IHt3. intro Hin. apply Hnot. apply in_or_app. right. apply in_or_app. right. exact Hin.
  - f_equal.
    + apply IHt1. intro Hin. apply Hnot. apply in_or_app. left. exact Hin.
    + apply IHt2. intro Hin. apply Hnot. apply in_or_app. right. exact Hin.
Qed.

Lemma instantiate_ty_update_irrelevant : forall theta X U T,
  ~ In X (fv_ty T) ->
  instantiate_ty (type_subst_update theta X U) T = instantiate_ty theta T.
Proof.
  intros theta X U T. induction T; intros Hnot; simpl in *.
  - reflexivity.
  - destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply Hnot. simpl. auto.
    + unfold type_subst_update. rewrite E. reflexivity.
  - f_equal.
    + apply IHT1. intro Hin. apply Hnot. apply in_or_app. left. exact Hin.
    + apply IHT2. intro Hin. apply Hnot. apply in_or_app. right. exact Hin.
  - f_equal. apply IHT. exact Hnot.
  - reflexivity.
Qed.

Lemma instantiate_update_irrelevant : forall theta gamma X U t,
  ~ In X (ftv_tm t) ->
  instantiate (type_subst_update theta X U) gamma t =
  instantiate theta gamma t.
Proof.
  intros theta gamma X U t. induction t; intros Hnot; simpl in *.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply instantiate_ty_update_irrelevant.
      intro Hin. apply Hnot. apply in_or_app. left. exact Hin.
    + apply IHt. intro Hin. apply Hnot. apply in_or_app. right. exact Hin.
  - f_equal.
    + apply IHt1. intro Hin. apply Hnot. apply in_or_app. left. exact Hin.
    + apply IHt2. intro Hin. apply Hnot. apply in_or_app. right. exact Hin.
  - f_equal. apply IHt. exact Hnot.
  - f_equal.
    + apply IHt. intro Hin. apply Hnot. apply in_or_app. left. exact Hin.
    + apply instantiate_ty_update_irrelevant.
      intro Hin. apply Hnot. apply in_or_app. right. exact Hin.
  - reflexivity.
  - f_equal. apply IHt. exact Hnot.
  - f_equal.
    + apply IHt1. intro Hin. apply Hnot. apply in_or_app. left. exact Hin.
    + apply IHt2. intro Hin. apply Hnot. apply in_or_app. right. apply in_or_app. left. exact Hin.
    + apply IHt3. intro Hin. apply Hnot. apply in_or_app. right. apply in_or_app. right. exact Hin.
  - f_equal.
    + apply IHt1. intro Hin. apply Hnot. apply in_or_app. left. exact Hin.
    + apply IHt2. intro Hin. apply Hnot. apply in_or_app. right. exact Hin.
Qed.

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

Lemma type_subst_update_eq : forall theta X U,
  type_subst_update theta X U X = U.
Proof. intros. unfold type_subst_update. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma term_subst_update_closed : forall gamma x u,
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  term_substitution_closed (term_subst_update gamma x u).
Proof.
  intros gamma x u Hgamma Hu y. unfold term_subst_update.
  destruct (Nat.eqb x y); auto.
Qed.

Lemma term_subst_update_eq : forall gamma x u,
  term_subst_update gamma x u x = u.
Proof. intros. unfold term_subst_update. rewrite Nat.eqb_refl. reflexivity. Qed.

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

Lemma numeric_value_lc : forall n, numeric_value n -> locally_closed_tm n.
Proof. intros n H. induction H; constructor; assumption. Qed.

Lemma value_regular : forall v, value v -> locally_closed_tm v.
Proof. intros v H. destruct H; try assumption; try constructor. apply numeric_value_lc. assumption. Qed.

Inductive evaluates : tm -> tm -> Prop :=
  | EvalValue : forall v, value v -> evaluates v v
  | EvalApp : forall f arg U body v result,
      evaluates f (tm_abs U body) -> evaluates arg v ->
      evaluates (open_tm body v) result -> evaluates (tm_app f arg) result
  | EvalTApp : forall f U body result,
      evaluates f (tm_tabs body) -> locally_closed_ty U ->
      evaluates (open_tm_ty body U) result -> evaluates (tm_tapp f U) result
  | EvalSucc : forall t n,
      evaluates t n -> numeric_value n -> evaluates (tm_succ t) (tm_succ n)
  | EvalRecZero : forall n b s vb vs,
      evaluates n tm_zero -> evaluates b vb -> evaluates s vs ->
      evaluates (tm_natrec n b s) vb
  | EvalRecSucc : forall n b s k vb vs result,
      evaluates n (tm_succ k) -> numeric_value k ->
      evaluates b vb -> evaluates s vs ->
      evaluates (tm_app (tm_app vs k) (tm_natrec k vb vs)) result ->
      evaluates (tm_natrec n b s) result
  | EvalChoiceLeft : forall t1 t2 v,
      evaluates t1 v -> locally_closed_tm t2 -> evaluates (tm_choice t1 t2) v
  | EvalChoiceRight : forall t1 t2 v,
      locally_closed_tm t1 -> evaluates t2 v -> evaluates (tm_choice t1 t2) v.

Lemma multi_succ : forall t u, t -->* u -> tm_succ t -->* tm_succ u.
Proof. intros t u H. induction H; eauto using multi, step. Qed.
Lemma multi_rec_arg : forall n n' b s,
  n -->* n' -> locally_closed_tm b -> locally_closed_tm s ->
  tm_natrec n b s -->* tm_natrec n' b s.
Proof. intros n n' b s H. induction H; eauto using multi, step. Qed.
Lemma multi_rec_base : forall n b b' s,
  numeric_value n -> b -->* b' -> locally_closed_tm s ->
  tm_natrec n b s -->* tm_natrec n b' s.
Proof. intros n b b' s Hn H. induction H; eauto using multi, step. Qed.
Lemma multi_rec_step : forall n b s s',
  numeric_value n -> value b -> s -->* s' ->
  tm_natrec n b s -->* tm_natrec n b s'.
Proof. intros n b s s' Hn Hb H. induction H; eauto using multi, step. Qed.

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

Fixpoint ty_size (T : ty) : nat :=
  match T with
  | Ty_BVar _ | Ty_FVar _ | Ty_Nat => 1
  | Ty_Arrow A B => S (ty_size A + ty_size B)
  | Ty_All A => S (ty_size A)
  end.

Lemma ty_size_open_rec : forall T k U,
  ty_size U = 1 ->
  ty_size (open_ty_rec k U T) = ty_size T.
Proof.
  induction T; intros k U HU; simpl.
  - destruct (Nat.eqb k n); simpl; [exact HU|reflexivity].
  - reflexivity.
  - rewrite (IHT1 k U HU), (IHT2 k U HU). reflexivity.
  - rewrite (IHT (S k) U HU). reflexivity.
  - reflexivity.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  assert (P : forall n T, ty_size T < n ->
      forall Delta, wf_ty Delta T -> locally_closed_ty T).
  { apply (well_founded_induction lt_wf
      (fun n => forall T, ty_size T < n ->
        forall Delta, wf_ty Delta T -> locally_closed_ty T)).
    intros n IH T Hsize Delta Hwf.
    destruct T as [i|Y|A B|B|]; simpl in *.
    - inversion Hwf.
    - inversion Hwf; constructor.
    - inversion Hwf; subst. constructor.
      + eapply (IH (S (ty_size A))).
        * simpl in Hsize. lia.
        * simpl. lia.
        * eauto.
      + eapply (IH (S (ty_size B))).
        * simpl in Hsize. lia.
        * simpl. lia.
        * eauto.
    - inversion Hwf; subst.
      constructor. set (X := fresh L).
      assert (HX : ~ In X L) by (unfold X; apply fresh_notin).
      match goal with
      | Hbody : forall Z, ~ In Z L ->
          wf_ty (Z :: ?D) (open_ty ?Body (Ty_FVar Z)) |- _ =>
          pose proof (Hbody X HX) as Hopened
      end.
      apply lc_ty_at_open_inv with (X := X).
      eapply (IH (S (ty_size (open_ty B (Ty_FVar X))))).
      + unfold open_ty. rewrite ty_size_open_rec by reflexivity.
        simpl in Hsize. lia.
      + change (ty_size (open_ty B (Ty_FVar X)) <
          S (ty_size (open_ty B (Ty_FVar X)))).
        apply Nat.lt_succ_diag_r.
      + exact Hopened.
    - inversion Hwf; constructor. }
  intros Delta T Hwf. unfold locally_closed_ty.
  exact (@P (S (ty_size T)) T (Nat.lt_succ_diag_r _) Delta Hwf).
Qed.

Lemma has_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T Hty. induction Hty.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + eapply wf_ty_lc; eassumption.
    + set (x := fresh L).
      assert (Hx : ~ In x L) by (unfold x; apply fresh_notin).
      specialize (H1 x Hx).
      unfold locally_closed_tm in *.
      eapply lc_tm_at_open_tm_inv. exact H1.
  - apply lc_tm_app; assumption.
  - apply lc_tm_tabs.
    set (X := fresh L).
    assert (HX : ~ In X L) by (unfold X; apply fresh_notin).
    unfold locally_closed_tm in H0.
    specialize (H0 X HX).
    eapply lc_tm_at_open_ty_inv. exact H0.
  - apply lc_tm_tapp.
    + assumption.
    + eapply wf_ty_lc; eassumption.
  - apply lc_tm_zero.
  - apply lc_tm_succ. assumption.
  - apply lc_tm_rec; assumption.
  - apply lc_tm_choice; assumption.
Qed.

Lemma has_type_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_ty T.
Proof.
  intros Delta Gamma t T Hty. induction Hty.
  - eapply wf_ty_lc; eassumption.
  - apply lc_ty_arrow.
    + eapply wf_ty_lc; eassumption.
    + set (x := fresh L).
      assert (Hx : ~ In x L) by (unfold x; apply fresh_notin).
      match goal with
      | Hlc : forall z, ~ In z L -> locally_closed_ty T2 |- _ =>
          exact (Hlc x Hx)
      end.
  - inversion IHHty1; subst. assumption.
  - unfold locally_closed_ty. apply lc_ty_all.
    set (X := fresh L).
    assert (HX : ~ In X L) by (unfold X; apply fresh_notin).
    match goal with
    | Hlc : forall Y, ~ In Y L -> locally_closed_ty (open_ty T (Ty_FVar Y)) |- _ =>
        pose proof (Hlc X HX) as Hopen
    end.
    eapply lc_ty_at_open_inv. exact Hopen.
  - inversion IHHty; subst.
    eapply lc_ty_at_open; [eassumption|].
    eapply wf_ty_lc; eassumption.
  - apply lc_ty_nat.
  - apply lc_ty_nat.
  - assumption.
  - assumption.
Qed.

Lemma instantiate_ty_lc : forall theta K T,
  (forall X, locally_closed_ty (theta X)) -> lc_ty_at K T ->
  lc_ty_at K (instantiate_ty theta T).
Proof.
  intros theta K T Htheta Hlc. induction Hlc; simpl.
  - apply lc_ty_bvar. assumption.
  - eapply lc_ty_at_monotone; [apply Htheta|lia].
  - apply lc_ty_arrow; assumption.
  - apply lc_ty_all. assumption.
  - apply lc_ty_nat.
Qed.

Lemma instantiate_lc : forall theta gamma K k t,
  (forall X, locally_closed_ty (theta X)) ->
  (forall x, locally_closed_tm (gamma x)) ->
  lc_tm_at K k t -> lc_tm_at K k (instantiate theta gamma t).
Proof.
  intros theta gamma K k t Htheta Hgamma Hlc.
  induction Hlc; simpl.
  - apply lc_tm_bvar. assumption.
  - unfold locally_closed_tm in Hgamma.
    eapply lc_tm_at_monotone; [apply Hgamma|lia|lia].
  - apply lc_tm_abs.
    + eapply instantiate_ty_lc; eauto.
    + assumption.
  - apply lc_tm_app; assumption.
  - apply lc_tm_tabs. assumption.
  - apply lc_tm_tapp.
    + assumption.
    + eapply instantiate_ty_lc; eauto.
  - apply lc_tm_zero.
  - apply lc_tm_succ. assumption.
  - apply lc_tm_rec; assumption.
  - apply lc_tm_choice; assumption.
Qed.

(* A value relation is stated over the outcomes of evaluation, rather than over
   source terms.  This is important here: choice has two possible outcomes,
   and the fundamental theorem only needs to exhibit one related outcome. *)
Definition reaches_value (t v : tm) : Prop :=
  value v /\ t -->* v.

Definition outcome_related (R : tm -> tm -> Prop) (t u : tm) : Prop :=
  exists v w, reaches_value t v /\ reaches_value u w /\ R v w.

(* Closed-type instance of the logical relation.  The universal case quantifies
   over a relation supplied by the interpretation of the bound type variable. *)
Fixpoint value_relation (T : ty)
    (xi : atom -> tm -> tm -> Prop)
    (rho : list (tm -> tm -> Prop)) : tm -> tm -> Prop :=
  match T with
  | Ty_BVar i => fun x y => nth i rho (fun _ _ => False) x y
  | Ty_FVar X => fun x y => xi X x y
  | Ty_Nat => fun x y =>
      numeric_value x /\ x = y
  | Ty_Arrow A B => fun x y =>
      value x /\ value y /\
      forall a b, outcome_related (value_relation A xi rho) a b ->
        outcome_related (value_relation B xi rho)
          (tm_app x a) (tm_app y b)
  | Ty_All B => fun x y =>
      value x /\ value y /\
      forall A C (Srel : tm -> tm -> Prop),
        locally_closed_ty A -> locally_closed_ty C ->
        (forall a b, Srel a b -> locally_closed_tm a /\ locally_closed_tm b) ->
        outcome_related (value_relation B xi (Srel :: rho))
          (tm_tapp x A) (tm_tapp y C)
  end.

Definition logical_relation (T : ty)
    (xi : atom -> tm -> tm -> Prop)
    (rho : list (tm -> tm -> Prop)) : tm -> tm -> Prop :=
  outcome_related (value_relation T xi rho).

Definition relation_update (xi : atom -> tm -> tm -> Prop)
    (X : atom) (R : tm -> tm -> Prop) : atom -> tm -> tm -> Prop :=
  fun Y => if Nat.eqb X Y then R else xi Y.

Lemma outcome_related_ext : forall R S t u,
  (forall a b, R a b <-> S a b) ->
  (outcome_related R t u <-> outcome_related S t u).
Proof.
  intros R S t u H. unfold outcome_related. split.
  - intros [v [w [Hv [Hw Hrel]]]]. exists v, w. split; [exact Hv|].
    split; [exact Hw|]. apply (proj1 (H v w)). exact Hrel.
  - intros [v [w [Hv [Hw Hrel]]]]. exists v, w. split; [exact Hv|].
    split; [exact Hw|]. apply (proj2 (H v w)). exact Hrel.
Qed.

Fixpoint relation_insert (k : nat) (R : tm -> tm -> Prop)
    (rho : list (tm -> tm -> Prop)) : list (tm -> tm -> Prop) :=
  match k, rho with
  | 0, _ => R :: rho
  | S k', [] => (fun _ _ => False) :: relation_insert k' R []
  | S k', r :: rho' => r :: relation_insert k' R rho'
  end.

Lemma nth_relation_insert_at : forall k rho R,
  nth k (relation_insert k R rho) (fun _ _ => False) = R.
Proof.
  induction k as [|k IH]; intros rho R; simpl.
  - reflexivity.
  - destruct rho; simpl; apply IH.
Qed.

Lemma nth_empty : forall A (d : A) i, nth i [] d = d.
Proof. intros A d i. destruct i; reflexivity. Qed.

Lemma nth_relation_insert_before : forall k rho R i,
  i < k ->
  nth i (relation_insert k R rho) (fun _ _ => False) =
  nth i rho (fun _ _ => False).
Proof.
  induction k as [|k IH]; intros rho R i Hi; [lia|].
  destruct rho as [|r rho]; destruct i as [|i]; simpl in *.
  - reflexivity.
  - rewrite IH; [rewrite nth_empty; reflexivity|lia].
  - reflexivity.
  - rewrite IH; [reflexivity|lia].
Qed.

Lemma nth_relation_insert : forall k rho R i,
  i < S k ->
  (if Nat.eqb i k then R else nth i rho (fun _ _ => False)) =
  nth i (relation_insert k R rho) (fun _ _ => False).
Proof.
  intros k rho R i Hi. destruct (Nat.eqb i k) eqn:E.
  - apply Nat.eqb_eq in E. subst. symmetry. apply nth_relation_insert_at.
  - apply Nat.eqb_neq in E. rewrite nth_relation_insert_before; [reflexivity|lia].
Qed.

Lemma value_relation_open_fvar : forall T (k : nat) X (Q : tm -> tm -> Prop)
    (xi : atom -> tm -> tm -> Prop) (rho : list (tm -> tm -> Prop)) a b,
  lc_ty_at (S k) T -> ~ In X (fv_ty T) ->
  (value_relation (open_ty_rec k (Ty_FVar X) T)
       (relation_update xi X Q) rho a b <->
   value_relation T xi (relation_insert k Q rho) a b).
Proof.
  induction T as [i|Y|A IHA B IHB|Body IHBody|];
    intros k X Q xi rho a b Hlc Hnot; simpl in *.
  - inversion Hlc; subst.
    destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst i.
      simpl. unfold relation_update. rewrite Nat.eqb_refl.
      rewrite nth_relation_insert_at. reflexivity.
    + apply Nat.eqb_neq in E.
      rewrite nth_relation_insert_before by lia. reflexivity.
  - destruct (Nat.eqb X Y) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply Hnot. simpl. auto.
    + unfold relation_update. rewrite E. tauto.
  - inversion Hlc; subst.
    assert (HnotA : ~ In X (fv_ty A)).
    { intro Hin. apply Hnot. apply in_or_app. left. exact Hin. }
    assert (HnotB : ~ In X (fv_ty B)).
    { intro Hin. apply Hnot. apply in_or_app. right. exact Hin. }
    split; intros [Hva [Hvb Hfun]]; repeat split; try assumption;
      intros a' b' Hargs.
    + apply (proj2 (outcome_related_ext
        (value_relation (open_ty_rec k (Ty_FVar X) A) (relation_update xi X Q) rho)
        (value_relation A xi (relation_insert k Q rho)) a' b'
        (fun x y => IHA k X Q xi rho x y H2 HnotA))) in Hargs.
      specialize (Hfun a' b' Hargs).
      apply (proj1 (outcome_related_ext
        (value_relation (open_ty_rec k (Ty_FVar X) B) (relation_update xi X Q) rho)
        (value_relation B xi (relation_insert k Q rho))
        (tm_app a a') (tm_app b b')
        (fun x y => IHB k X Q xi rho x y H3 HnotB))). exact Hfun.
    + apply (proj1 (outcome_related_ext
        (value_relation (open_ty_rec k (Ty_FVar X) A) (relation_update xi X Q) rho)
        (value_relation A xi (relation_insert k Q rho)) a' b'
        (fun x y => IHA k X Q xi rho x y H2 HnotA))) in Hargs.
      specialize (Hfun a' b' Hargs).
      apply (proj2 (outcome_related_ext
        (value_relation (open_ty_rec k (Ty_FVar X) B) (relation_update xi X Q) rho)
        (value_relation B xi (relation_insert k Q rho))
        (tm_app a a') (tm_app b b')
        (fun x y => IHB k X Q xi rho x y H3 HnotB))). exact Hfun.
  - inversion Hlc; subst.
    split; intros [Hva [Hvb Hfun]]; repeat split; try assumption;
      intros A C R HA HC Hclosed.
    + specialize (Hfun A C R HA HC Hclosed).
      apply (proj1 (outcome_related_ext
        (value_relation (open_ty_rec (S k) (Ty_FVar X) Body)
          (relation_update xi X Q) (R :: rho))
        (value_relation Body xi (R :: relation_insert k Q rho))
        (tm_tapp a A) (tm_tapp b C)
        (fun x y => IHBody (S k) X Q xi (R :: rho) x y H1 Hnot))). exact Hfun.
    + specialize (Hfun A C R HA HC Hclosed).
      apply (proj2 (outcome_related_ext
        (value_relation (open_ty_rec (S k) (Ty_FVar X) Body)
          (relation_update xi X Q) (R :: rho))
        (value_relation Body xi (R :: relation_insert k Q rho))
        (tm_tapp a A) (tm_tapp b C)
        (fun x y => IHBody (S k) X Q xi (R :: rho) x y H1 Hnot))). exact Hfun.
  - tauto.
Qed.

Lemma value_relation_env_ext : forall T k xi rho1 rho2 a b,
  lc_ty_at k T ->
  (forall i, i < k -> nth i rho1 (fun _ _ => False) =
                         nth i rho2 (fun _ _ => False)) ->
  (value_relation T xi rho1 a b <-> value_relation T xi rho2 a b).
Proof.
  induction T as [i|X|A IHA B IHB|Body IHBody|];
    intros k xi rho1 rho2 a b Hlc Hagree; simpl in *.
  - inversion Hlc; subst. pose proof (Hagree i H1) as Heq.
    rewrite Heq. tauto.
  - tauto.
  - inversion Hlc; subst.
    split; intros [Hva [Hvb Hfun]]; repeat split; try assumption;
      intros a' b' Hargs.
    + apply (proj2 (outcome_related_ext (value_relation A xi rho1)
        (value_relation A xi rho2) a' b'
        (fun x y => IHA k xi rho1 rho2 x y H2 Hagree))) in Hargs.
      specialize (Hfun a' b' Hargs).
      apply (proj1 (outcome_related_ext (value_relation B xi rho1)
        (value_relation B xi rho2) (tm_app a a') (tm_app b b')
        (fun x y => IHB k xi rho1 rho2 x y H3 Hagree))). exact Hfun.
    + apply (proj1 (outcome_related_ext (value_relation A xi rho1)
        (value_relation A xi rho2) a' b'
        (fun x y => IHA k xi rho1 rho2 x y H2 Hagree))) in Hargs.
      specialize (Hfun a' b' Hargs).
      apply (proj2 (outcome_related_ext (value_relation B xi rho1)
        (value_relation B xi rho2) (tm_app a a') (tm_app b b')
        (fun x y => IHB k xi rho1 rho2 x y H3 Hagree))). exact Hfun.
  - inversion Hlc; subst.
    split; intros [Hva [Hvb Hfun]]; repeat split; try assumption;
      intros A C R HA HC Hclosed.
    + assert (Hagree' : forall i, i < S k ->
          nth i (R :: rho1) (fun _ _ => False) =
          nth i (R :: rho2) (fun _ _ => False)).
      { intros [|i] Hi; simpl; [reflexivity|]. apply Hagree. lia. }
      specialize (Hfun A C R HA HC Hclosed).
      apply (proj1 (outcome_related_ext (value_relation Body xi (R :: rho1))
        (value_relation Body xi (R :: rho2)) (tm_tapp a A) (tm_tapp b C)
        (fun x y => IHBody (S k) xi (R :: rho1) (R :: rho2) x y H1 Hagree'))). exact Hfun.
    + assert (Hagree' : forall i, i < S k ->
          nth i (R :: rho1) (fun _ _ => False) =
          nth i (R :: rho2) (fun _ _ => False)).
      { intros [|i] Hi; simpl; [reflexivity|]. apply Hagree. lia. }
      specialize (Hfun A C R HA HC Hclosed).
      apply (proj2 (outcome_related_ext (value_relation Body xi (R :: rho1))
        (value_relation Body xi (R :: rho2)) (tm_tapp a A) (tm_tapp b C)
        (fun x y => IHBody (S k) xi (R :: rho1) (R :: rho2) x y H1 Hagree'))). exact Hfun.
  - tauto.
Qed.

Lemma value_relation_open : forall T k U xi rho a b,
  lc_ty_at (S k) T -> locally_closed_ty U ->
  (value_relation (open_ty_rec k U T) xi rho a b <->
   value_relation T xi (relation_insert k (value_relation U xi []) rho) a b).
Proof.
  induction T as [i|X|A IHA B IHB|Body IHBody|];
    intros k U xi rho a b Hlc HU; simpl in *.
  - inversion Hlc; subst. destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst i. simpl.
      assert (Heq : value_relation U xi rho a b <-> value_relation U xi [] a b).
      { apply value_relation_env_ext with (k:=0); [exact HU|intros; lia]. }
      rewrite Heq. rewrite nth_relation_insert_at. reflexivity.
    + apply Nat.eqb_neq in E. rewrite nth_relation_insert_before by lia. tauto.
  - tauto.
  - inversion Hlc; subst.
    split; intros [Hva [Hvb Hfun]]; repeat split; try assumption;
      intros a' b' Hargs.
    + apply (proj2 (outcome_related_ext
        (value_relation (open_ty_rec k U A) xi rho)
        (value_relation A xi (relation_insert k (value_relation U xi []) rho))
        a' b' (fun x y => IHA k U xi rho x y H2 HU))) in Hargs.
      specialize (Hfun a' b' Hargs).
      apply (proj1 (outcome_related_ext
        (value_relation (open_ty_rec k U B) xi rho)
        (value_relation B xi (relation_insert k (value_relation U xi []) rho))
        (tm_app a a') (tm_app b b')
        (fun x y => IHB k U xi rho x y H3 HU))). exact Hfun.
    + apply (proj1 (outcome_related_ext
        (value_relation (open_ty_rec k U A) xi rho)
        (value_relation A xi (relation_insert k (value_relation U xi []) rho))
        a' b' (fun x y => IHA k U xi rho x y H2 HU))) in Hargs.
      specialize (Hfun a' b' Hargs).
      apply (proj2 (outcome_related_ext
        (value_relation (open_ty_rec k U B) xi rho)
        (value_relation B xi (relation_insert k (value_relation U xi []) rho))
        (tm_app a a') (tm_app b b')
        (fun x y => IHB k U xi rho x y H3 HU))). exact Hfun.
  - inversion Hlc; subst.
    split; intros [Hva [Hvb Hfun]]; repeat split; try assumption;
      intros A C R HA HC Hclosed.
    + specialize (Hfun A C R HA HC Hclosed).
      apply (proj1 (outcome_related_ext
        (value_relation (open_ty_rec (S k) U Body) xi (R :: rho))
        (value_relation Body xi (R :: relation_insert k (value_relation U xi []) rho))
        (tm_tapp a A) (tm_tapp b C)
        (fun x y => IHBody (S k) U xi (R :: rho) x y H1 HU))). exact Hfun.
    + specialize (Hfun A C R HA HC Hclosed).
      apply (proj2 (outcome_related_ext
        (value_relation (open_ty_rec (S k) U Body) xi (R :: rho))
        (value_relation Body xi (R :: relation_insert k (value_relation U xi []) rho))
        (tm_tapp a A) (tm_tapp b C)
        (fun x y => IHBody (S k) U xi (R :: rho) x y H1 HU))). exact Hfun.
  - tauto.
Qed.

Lemma value_relation_update_irrelevant : forall T xi X S rho a b,
  ~ In X (fv_ty T) ->
  (value_relation T xi rho a b <->
   value_relation T (relation_update xi X S) rho a b).
Proof.
  induction T as [i|Y|A IHA B IHB|Body IHBody|];
    intros xi X S rho a b Hnot; simpl in *.
  - tauto.
  - destruct (Nat.eqb X Y) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply Hnot. simpl. auto.
    + unfold relation_update. rewrite E. tauto.
  - assert (HnotA : ~ In X (fv_ty A)).
    { intro Hin. apply Hnot. apply in_or_app. left. exact Hin. }
    assert (HnotB : ~ In X (fv_ty B)).
    { intro Hin. apply Hnot. apply in_or_app. right. exact Hin. }
    split; intros [Hva [Hvb Hfun]]; repeat split; try assumption;
      intros a' b' Hargs.
    + apply (proj2 (outcome_related_ext
        (value_relation A xi rho) (value_relation A (relation_update xi X S) rho)
        a' b' (fun x y => IHA xi X S rho x y HnotA))) in Hargs.
      specialize (Hfun a' b' Hargs).
      apply (proj1 (outcome_related_ext
        (value_relation B xi rho) (value_relation B (relation_update xi X S) rho)
        (tm_app a a') (tm_app b b')
        (fun x y => IHB xi X S rho x y HnotB))). exact Hfun.
    + apply (proj1 (outcome_related_ext
        (value_relation A xi rho) (value_relation A (relation_update xi X S) rho)
        a' b' (fun x y => IHA xi X S rho x y HnotA))) in Hargs.
      specialize (Hfun a' b' Hargs).
      apply (proj2 (outcome_related_ext
        (value_relation B xi rho) (value_relation B (relation_update xi X S) rho)
        (tm_app a a') (tm_app b b')
        (fun x y => IHB xi X S rho x y HnotB))). exact Hfun.
  - split; intros [Hva [Hvb Hfun]]; repeat split; try assumption;
      intros A C R HA HC Hclosed.
    + specialize (Hfun A C R HA HC Hclosed).
      apply (proj1 (outcome_related_ext
        (value_relation Body xi (R :: rho))
        (value_relation Body (relation_update xi X S) (R :: rho))
        (tm_tapp a A) (tm_tapp b C)
        (fun x y => IHBody xi X S (R :: rho) x y Hnot))). exact Hfun.
    + specialize (Hfun A C R HA HC Hclosed).
      apply (proj2 (outcome_related_ext
        (value_relation Body xi (R :: rho))
        (value_relation Body (relation_update xi X S) (R :: rho))
        (tm_tapp a A) (tm_tapp b C)
        (fun x y => IHBody xi X S (R :: rho) x y Hnot))). exact Hfun.
  - tauto.
Qed.

Lemma logical_relation_update_irrelevant : forall T xi X S rho a b,
  ~ In X (fv_ty T) ->
  (logical_relation T xi rho a b <->
   logical_relation T (relation_update xi X S) rho a b).
Proof.
  intros. unfold logical_relation. apply outcome_related_ext.
  intros x y. apply value_relation_update_irrelevant. assumption.
Qed.

Definition related_context (Gamma : context)
    (xi : atom -> tm -> tm -> Prop)
    (gamma1 gamma2 : term_substitution) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    logical_relation T xi [] (gamma1 x) (gamma2 x).

Lemma related_context_term_update : forall Gamma xi gamma1 gamma2 x T a b,
  related_context Gamma xi gamma1 gamma2 ->
  logical_relation T xi [] a b ->
  related_context (update Gamma x T) xi
    (term_subst_update gamma1 x a) (term_subst_update gamma2 x b).
Proof.
  intros Gamma xi gamma1 gamma2 x T a b Hctx Hab y S Hlookup.
  unfold term_subst_update.
  destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. subst y. simpl in Hlookup.
    rewrite Nat.eqb_refl in Hlookup. inversion Hlookup; subst. exact Hab.
  - apply Nat.eqb_neq in E.
    rewrite lookup_context_update_neq in Hlookup; [|exact E].
    eapply Hctx. exact Hlookup.
Qed.

Lemma lookup_fv_ty_in_context : forall Gamma x T X,
  lookup_context x Gamma = Some T -> In X (fv_ty T) ->
  In X (ftv_context Gamma).
Proof.
  induction Gamma as [|[y U] Gamma IH]; intros x T X Hlookup Hin; simpl in *.
  - discriminate.
  - unfold lookup_context in Hlookup. simpl in Hlookup.
    destruct (Nat.eqb x y) eqn:E.
    + inversion Hlookup; subst. apply in_or_app. left. exact Hin.
    + apply in_or_app. right. eapply IH; eauto.
Qed.

Lemma related_context_type_update : forall Gamma xi X R gamma1 gamma2,
  related_context Gamma xi gamma1 gamma2 ->
  ~ In X (ftv_context Gamma) ->
  related_context Gamma (relation_update xi X R) gamma1 gamma2.
Proof.
  intros Gamma xi X R gamma1 gamma2 Hctx Hfresh x T Hlook.
  specialize (Hctx x T Hlook).
  assert (Hnot : ~ In X (fv_ty T)).
  { intro Hin. apply Hfresh. eapply lookup_fv_ty_in_context; eauto. }
  apply (proj1 (logical_relation_update_irrelevant T xi X R []
    (gamma1 x) (gamma2 x) Hnot)). exact Hctx.
Qed.

Lemma outcome_related_precompose : forall R t t' u u',
  t -->* t' -> u -->* u' -> outcome_related R t' u' ->
  outcome_related R t u.
Proof.
  intros R t t' u u' Ht Hu [v [w [Hv [Hw HR]]]].
  destruct Hv as [Vv Htv]. destruct Hw as [Vw Huw].
  exists v, w. split.
  - split; [exact Vv|eapply multi_trans; eassumption].
  - split; [split; [exact Vw|eapply multi_trans; eassumption]|exact HR].
Qed.

Lemma multi_choice_left : forall t1 t2,
  locally_closed_tm t1 -> locally_closed_tm t2 ->
  tm_choice t1 t2 -->* t1.
Proof. intros. eapply multi_step; [apply ST_ChoiceLeft; assumption|constructor]. Qed.

Lemma multi_choice_right : forall t1 t2,
  locally_closed_tm t1 -> locally_closed_tm t2 ->
  tm_choice t1 t2 -->* t2.
Proof. intros. eapply multi_step; [apply ST_ChoiceRight; assumption|constructor]. Qed.

Lemma multi_abs_app : forall T body arg v,
  locally_closed_tm (tm_abs T body) -> value v -> arg -->* v ->
  tm_app (tm_abs T body) arg -->* open_tm body v.
Proof.
  intros T body arg v Habs Hv Harg.
  eapply multi_trans.
  - eapply multi_app_right; eauto using value.
  - eapply multi_step.
    + apply ST_AppAbs; assumption.
    + apply multi_refl.
Qed.

Lemma instantiate_typed_lc : forall Delta Gamma t T theta gamma,
  has_type Delta Gamma t T ->
  (forall X, locally_closed_ty (theta X)) ->
  (forall x, locally_closed_tm (gamma x)) ->
  locally_closed_tm (instantiate theta gamma t).
Proof.
  intros Delta Gamma t T theta gamma Hty Htheta Hgamma.
  unfold locally_closed_tm. eapply instantiate_lc; eauto.
  unfold locally_closed_tm. eapply has_type_lc; eauto.
Qed.

Lemma wf_value_relation_lc : forall Delta T,
  wf_ty Delta T -> forall xi rho a b,
    (forall X x y, xi X x y -> locally_closed_tm x /\ locally_closed_tm y) ->
    (forall R x y, In R rho -> R x y -> locally_closed_tm x /\ locally_closed_tm y) ->
    value_relation T xi rho a b -> locally_closed_tm a /\ locally_closed_tm b.
Proof.
  intros Delta T Hwf. induction Hwf; intros xi rho a b Hxi Hr Hrel;
    simpl in Hrel.
  - apply (Hxi X a b). exact Hrel.
  - destruct Hrel as [Ha [Hb _]]. split; apply value_regular; assumption.
  - destruct Hrel as [Ha [Hb _]]. split; apply value_regular; assumption.
  - destruct Hrel as [Hnum Heq]. subst b.
    split; apply numeric_value_lc; exact Hnum.
Qed.

Lemma logical_relation_numeral : forall xi n,
  numeric_value n -> logical_relation Ty_Nat xi [] n n.
Proof.
  intros xi n Hn. unfold logical_relation, outcome_related, reaches_value.
  exists n, n. split; [split; [constructor; exact Hn|apply multi_refl]|].
  split; [split; [constructor; exact Hn|apply multi_refl]|].
  simpl. split; [exact Hn|reflexivity].
Qed.

Lemma natrec_related_values : forall T xi n vb1 vb2 sf1 sf2,
  numeric_value n -> value vb1 -> value vb2 -> value sf1 -> value sf2 ->
  value_relation T xi [] vb1 vb2 ->
  value_relation (Ty_Arrow Ty_Nat (Ty_Arrow T T)) xi [] sf1 sf2 ->
  outcome_related (value_relation T xi [])
    (tm_natrec n vb1 sf1) (tm_natrec n vb2 sf2).
Proof.
  intros T xi n vb1 vb2 sf1 sf2 Hn.
  induction Hn as [|n Hn IH]; intros Hvb1 Hvb2 Hsf1 Hsf2 Hbase Hstep.
  - unfold outcome_related, reaches_value.
    exists vb1, vb2. split; [split; [exact Hvb1|]|].
    + eapply multi_step; [apply ST_RecZero; assumption|constructor].
    + split; [split; [exact Hvb2|]|exact Hbase].
      eapply multi_step; [apply ST_RecZero; assumption|constructor].
  - pose proof Hstep as Hstep0.
    simpl in Hstep. destruct Hstep as [Hsv1 [Hsv2 Hstepfun]].
    specialize (Hstepfun n n (logical_relation_numeral xi n Hn)) as Hstepapp.
    unfold outcome_related in Hstepapp.
    destruct Hstepapp as [g1 [g2 [Hg1reach [Hg2reach Hgrel]]]].
    destruct Hg1reach as [Hvg1 Hg1path].
    destruct Hg2reach as [Hvg2 Hg2path].
    simpl in Hgrel. destruct Hgrel as [Hvgfun1 [Hvgfun2 Hgfun]].
    pose proof (IH Hvb1 Hvb2 Hsv1 Hsv2 Hbase Hstep0) as Hrec.
    specialize (Hgfun (tm_natrec n vb1 sf1) (tm_natrec n vb2 sf2) Hrec).
    assert (Hreclc1 : locally_closed_tm (tm_natrec n vb1 sf1)).
    { apply lc_tm_rec; [apply numeric_value_lc; exact Hn|apply value_regular; exact Hvb1|apply value_regular; exact Hsf1]. }
    assert (Hreclc2 : locally_closed_tm (tm_natrec n vb2 sf2)).
    { apply lc_tm_rec; [apply numeric_value_lc; exact Hn|apply value_regular; exact Hvb2|apply value_regular; exact Hsf2]. }
    pose proof (outcome_related_precompose (value_relation T xi [])
      (tm_app (tm_app sf1 n) (tm_natrec n vb1 sf1))
      (tm_app g1 (tm_natrec n vb1 sf1))
      (tm_app (tm_app sf2 n) (tm_natrec n vb2 sf2))
      (tm_app g2 (tm_natrec n vb2 sf2))
      (@multi_app_left (tm_app sf1 n) g1 (tm_natrec n vb1 sf1) Hg1path Hreclc1)
      (@multi_app_left (tm_app sf2 n) g2 (tm_natrec n vb2 sf2) Hg2path Hreclc2)
      Hgfun) as Happs.
    (* The constructor step is followed by the application computation. *)
    eapply outcome_related_precompose.
    + eapply multi_step.
      * apply ST_RecSucc; assumption.
      * apply multi_refl.
    + eapply multi_step.
      * apply ST_RecSucc; assumption.
      * apply multi_refl.
    + exact Happs.
Qed.

Lemma fundamental_relation : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall theta1 theta2 xi gamma1 gamma2,
    (forall X, locally_closed_ty (theta1 X)) ->
    (forall X, locally_closed_ty (theta2 X)) ->
    (forall x, locally_closed_tm (gamma1 x)) ->
    (forall x, locally_closed_tm (gamma2 x)) ->
    (forall X a b, xi X a b -> locally_closed_tm a /\ locally_closed_tm b) ->
    related_context Gamma xi gamma1 gamma2 ->
    logical_relation T xi []
      (instantiate theta1 gamma1 t) (instantiate theta2 gamma2 t).
Proof.
  intros Delta Gamma t T Hty. induction Hty;
    intros theta1 theta2 xi gamma1 gamma2 Htheta1 Htheta2 Hgamma1 Hgamma2 Hxi Hctx.
  - simpl. eapply Hctx. eassumption.
  - simpl.
    assert (Habs_lc : locally_closed_tm (tm_abs T1 t2)).
    { eapply has_type_lc. econstructor; eauto. }
    assert (Habs1 : value (instantiate theta1 gamma1 (tm_abs T1 t2))).
    { apply v_abs. unfold locally_closed_tm in Habs_lc.
      exact (instantiate_lc theta1 gamma1 0 0 (tm_abs T1 t2)
        Htheta1 Hgamma1 Habs_lc). }
    assert (Habs2 : value (instantiate theta2 gamma2 (tm_abs T1 t2))).
    { apply v_abs. exact (instantiate_lc theta2 gamma2 0 0 (tm_abs T1 t2)
        Htheta2 Hgamma2 Habs_lc). }
    unfold logical_relation, outcome_related, reaches_value.
    exists (instantiate theta1 gamma1 (tm_abs T1 t2)),
           (instantiate theta2 gamma2 (tm_abs T1 t2)).
    split; [split; [exact Habs1|apply multi_refl]|].
    split; [split; [exact Habs2|apply multi_refl]|].
    simpl. split; [exact Habs1|]. split; [exact Habs2|].
    intros a b Hargs.
    unfold outcome_related in Hargs.
    destruct Hargs as [av [bv [Hav [Hbv Harel]]]].
    destruct Hav as [Havv Havpath]. destruct Hbv as [Hbvv Hbpath].
    assert (Habrel : logical_relation T1 xi [] av bv).
    { unfold logical_relation, outcome_related, reaches_value.
      exists av, bv. split.
      - split; [exact Havv|apply multi_refl].
      - split.
        + split; [exact Hbvv|apply multi_refl].
        + exact Harel. }
    set (x := fresh (L ++ fv_tm t2)).
    assert (HxL : ~ In x L).
    { intro Hin. apply (fresh_notin (L ++ fv_tm t2)).
      unfold x. apply in_or_app. left. exact Hin. }
    assert (Hxbody : ~ In x (fv_tm t2)).
    { intro Hin. apply (fresh_notin (L ++ fv_tm t2)).
      unfold x. apply in_or_app. right. exact Hin. }
    set (g1 := term_subst_update gamma1 x av).
    set (g2 := term_subst_update gamma2 x bv).
    assert (Hg1 : forall z, locally_closed_tm (g1 z)).
    { unfold g1. apply term_subst_update_closed.
      - exact Hgamma1.
      - apply value_regular. exact Havv. }
    assert (Hg2 : forall z, locally_closed_tm (g2 z)).
    { unfold g2. apply term_subst_update_closed.
      - exact Hgamma2.
      - apply value_regular. exact Hbvv. }
    assert (Hctx' : related_context (update Gamma x T1) xi g1 g2).
    { unfold g1, g2. eapply related_context_term_update; eauto. }
    specialize (H1 x HxL theta1 theta2 xi g1 g2
      Htheta1 Htheta2 Hg1 Hg2 Hxi Hctx').
    unfold g1, g2 in H1.
    unfold open_tm in H1.
    rewrite (instantiate_open_tm_rec theta1 (term_subst_update gamma1 x av)
      0 (tm_fvar x) t2 Hg1) in H1.
    rewrite (instantiate_open_tm_rec theta2 (term_subst_update gamma2 x bv)
      0 (tm_fvar x) t2 Hg2) in H1.
    change (logical_relation T2 xi []
      (open_tm_rec 0 ((term_subst_update gamma1 x av) x)
        (instantiate theta1 (term_subst_update gamma1 x av) t2))
      (open_tm_rec 0 ((term_subst_update gamma2 x bv) x)
        (instantiate theta2 (term_subst_update gamma2 x bv) t2))) in H1.
    rewrite term_subst_update_eq in H1.
    rewrite term_subst_update_eq in H1.
    rewrite (instantiate_term_update_irrelevant theta1 gamma1 x av t2 Hxbody) in H1.
    rewrite (instantiate_term_update_irrelevant theta2 gamma2 x bv t2 Hxbody) in H1.
    assert (Hbodyrel : logical_relation T2 xi []
      (open_tm (instantiate theta1 gamma1 t2) av)
      (open_tm (instantiate theta2 gamma2 t2) bv)).
    { exact H1. }
    eapply outcome_related_precompose.
    + eapply multi_abs_app.
      * apply value_regular. exact Habs1.
      * exact Havv.
      * exact Havpath.
    + eapply multi_abs_app.
      * apply value_regular. exact Habs2.
      * exact Hbvv.
      * exact Hbpath.
    + exact Hbodyrel.
  - simpl.
    pose proof (IHHty1 theta1 theta2 xi gamma1 gamma2
      Htheta1 Htheta2 Hgamma1 Hgamma2 Hxi Hctx) as Hfrel.
    pose proof (IHHty2 theta1 theta2 xi gamma1 gamma2
      Htheta1 Htheta2 Hgamma1 Hgamma2 Hxi Hctx) as Hargrel.
    unfold logical_relation in Hfrel.
    destruct Hfrel as [f1 [f2 [Hf1reach [Hf2reach Hrel]]]].
    destruct Hf1reach as [Hf1 Hf1path].
    destruct Hf2reach as [Hf2 Hf2path].
    simpl in Hrel. destruct Hrel as [Hfv1 [Hfv2 Happly]].
    specialize (Happly (instantiate theta1 gamma1 t2)
      (instantiate theta2 gamma2 t2) Hargrel).
    unfold outcome_related in Happly.
    assert (Harglc1 : locally_closed_tm (instantiate theta1 gamma1 t2)).
    { eapply instantiate_typed_lc; eauto. }
    assert (Harglc2 : locally_closed_tm (instantiate theta2 gamma2 t2)).
    { eapply instantiate_typed_lc; eauto. }
    eapply outcome_related_precompose.
    + eapply multi_app_left; eassumption.
    + eapply multi_app_left; eassumption.
    + exact Happly.
  - simpl.
    assert (Htabs_lc : locally_closed_tm (tm_tabs t)).
    { eapply has_type_lc. econstructor; eauto. }
    assert (Htabs1 : value (instantiate theta1 gamma1 (tm_tabs t))).
    { constructor. exact (instantiate_lc theta1 gamma1 0 0 (tm_tabs t)
        Htheta1 Hgamma1 Htabs_lc). }
    assert (Htabs2 : value (instantiate theta2 gamma2 (tm_tabs t))).
    { constructor. exact (instantiate_lc theta2 gamma2 0 0 (tm_tabs t)
        Htheta2 Hgamma2 Htabs_lc). }
    unfold logical_relation, outcome_related, reaches_value.
    exists (instantiate theta1 gamma1 (tm_tabs t)),
           (instantiate theta2 gamma2 (tm_tabs t)).
    split; [split; [exact Htabs1|apply multi_refl]|].
    split; [split; [exact Htabs2|apply multi_refl]|].
    simpl. split; [exact Htabs1|]. split; [exact Htabs2|].
    intros A C R HA HC Hclosed.
    set (X := fresh (L ++ ftv_context Gamma ++ fv_ty T ++ ftv_tm t)).
    assert (HXall : ~ In X (L ++ ftv_context Gamma ++ fv_ty T ++ ftv_tm t)).
    { unfold X. apply fresh_notin. }
    assert (HXL : ~ In X L).
    { intro Hin. apply HXall. apply in_or_app. left. exact Hin. }
    assert (HXctx : ~ In X (ftv_context Gamma)).
    { intro Hin. apply HXall. apply in_or_app. right. apply in_or_app. left. exact Hin. }
    assert (HXty : ~ In X (fv_ty T)).
    { intro Hin. apply HXall. apply in_or_app. right. apply in_or_app. right.
      apply in_or_app. left. exact Hin. }
    assert (HXtm : ~ In X (ftv_tm t)).
    { intro Hin. apply HXall. apply in_or_app. right. apply in_or_app. right.
      apply in_or_app. right. exact Hin. }
    set (th1 := type_subst_update theta1 X A).
    set (th2 := type_subst_update theta2 X C).
    set (xi' := relation_update xi X R).
    assert (Hth1 : forall Y, locally_closed_ty (th1 Y)).
    { unfold th1. apply type_subst_update_closed; assumption. }
    assert (Hth2 : forall Y, locally_closed_ty (th2 Y)).
    { unfold th2. apply type_subst_update_closed; assumption. }
    assert (Hctx' : related_context Gamma xi' gamma1 gamma2).
    { unfold xi'. eapply related_context_type_update; eauto. }
    assert (Hxi' : forall Y a b, xi' Y a b ->
        locally_closed_tm a /\ locally_closed_tm b).
    { intros Y a b Hrel. unfold xi', relation_update in Hrel.
      destruct (Nat.eqb X Y) eqn:E.
      - apply Hclosed. exact Hrel.
      - apply (Hxi Y a b). exact Hrel. }
    specialize (H0 X HXL th1 th2 xi' gamma1 gamma2
      Hth1 Hth2 Hgamma1 Hgamma2 Hxi' Hctx').
    unfold th1, th2, xi' in H0.
    unfold open_tm_ty in H0.
    rewrite (instantiate_open_ty_rec
      (type_subst_update theta1 X A) gamma1 0 (Ty_FVar X) t
      (type_subst_update_closed theta1 X A Htheta1 HA) Hgamma1) in H0.
    rewrite (instantiate_open_ty_rec
      (type_subst_update theta2 X C) gamma2 0 (Ty_FVar X) t
      (type_subst_update_closed theta2 X C Htheta2 HC) Hgamma2) in H0.
    change (logical_relation (open_ty_rec 0 (Ty_FVar X) T)
      (relation_update xi X R) []
      (open_tm_ty_rec 0
        (instantiate_ty (type_subst_update theta1 X A) (Ty_FVar X))
        (instantiate (type_subst_update theta1 X A) gamma1 t))
      (open_tm_ty_rec 0
        (instantiate_ty (type_subst_update theta2 X C) (Ty_FVar X))
        (instantiate (type_subst_update theta2 X C) gamma2 t))) in H0.
    cbn [instantiate_ty] in H0.
    rewrite (type_subst_update_eq theta1 X A) in H0.
    rewrite (type_subst_update_eq theta2 X C) in H0.
    rewrite (instantiate_update_irrelevant theta1 gamma1 X A t HXtm) in H0.
    rewrite (instantiate_update_irrelevant theta2 gamma2 X C t HXtm) in H0.
    assert (Hopenlc : lc_ty_at 1 T).
    { pose proof (has_type_type_lc (X :: Delta) Gamma
        (open_tm_ty t (Ty_FVar X)) (open_ty T (Ty_FVar X))
        (H X HXL)) as Hlcopen.
      eapply lc_ty_at_open_inv. exact Hlcopen. }
    unfold logical_relation in H0.
    pose proof (proj1 (outcome_related_ext
      (value_relation (open_ty_rec 0 (Ty_FVar X) T) xi' [])
      (value_relation T xi [R])
      (open_tm_ty_rec 0 A (instantiate theta1 gamma1 t))
      (open_tm_ty_rec 0 C (instantiate theta2 gamma2 t))
      (fun a b => value_relation_open_fvar T 0 X R xi [] a b Hopenlc HXty)) H0)
      as Hbodyout.
    eapply outcome_related_precompose.
    + eapply multi_step.
      * apply ST_TAppTabs.
        -- apply value_regular. exact Htabs1.
        -- exact HA.
      * constructor.
    + eapply multi_step.
      * apply ST_TAppTabs.
        -- apply value_regular. exact Htabs2.
        -- exact HC.
      * constructor.
    + exact Hbodyout.
  - simpl.
    pose proof (IHHty theta1 theta2 xi gamma1 gamma2
      Htheta1 Htheta2 Hgamma1 Hgamma2 Hxi Hctx) as Hpoly.
    unfold logical_relation in Hpoly.
    destruct Hpoly as [f1 [f2 [Hf1reach [Hf2reach Hfr]]]].
    destruct Hf1reach as [Hf1 Hf1path].
    destruct Hf2reach as [Hf2 Hf2path].
    simpl in Hfr. destruct Hfr as [Hvf1 [Hvf2 Hall]].
    set (A1 := instantiate_ty theta1 U).
    set (A2 := instantiate_ty theta2 U).
    set (RU := value_relation U xi []).
    assert (HUlc : locally_closed_ty U) by (eapply wf_ty_lc; eassumption).
    assert (HA1 : locally_closed_ty A1).
    { unfold A1. unfold locally_closed_ty.
      eapply instantiate_ty_lc; [exact Htheta1|].
      unfold locally_closed_ty in HUlc. exact HUlc. }
    assert (HA2 : locally_closed_ty A2).
    { unfold A2. unfold locally_closed_ty.
      eapply instantiate_ty_lc; [exact Htheta2|].
      unfold locally_closed_ty in HUlc. exact HUlc. }
    assert (HRUclosed : forall a b, RU a b ->
        locally_closed_tm a /\ locally_closed_tm b).
    { intros a b Hrel. unfold RU in Hrel.
      eapply wf_value_relation_lc; [exact H|exact Hxi| |exact Hrel].
      intros R a0 b0 Hin. contradiction. }
    specialize (Hall A1 A2 RU HA1 HA2 HRUclosed).
    assert (HlcT : lc_ty_at 1 T).
    { pose proof (has_type_type_lc Delta Gamma t (Ty_All T) Hty) as Halllc.
      unfold locally_closed_ty in Halllc. inversion Halllc; assumption. }
    pose proof (proj2 (outcome_related_ext
      (value_relation (open_ty T U) xi [])
      (value_relation T xi (RU :: []))
      (tm_tapp f1 A1) (tm_tapp f2 A2)
      (fun a b => value_relation_open T 0 U xi [] a b HlcT HUlc)) Hall)
      as Hbodyout.
    unfold logical_relation. eapply outcome_related_precompose.
    + eapply multi_tapp; [exact Hf1path|exact HA1].
    + eapply multi_tapp; [exact Hf2path|exact HA2].
    + exact Hbodyout.
  - simpl. unfold logical_relation, outcome_related, reaches_value. simpl.
    exists tm_zero, tm_zero.
    split; [split; [constructor; constructor|apply multi_refl]|].
    split; [split; [constructor; constructor|apply multi_refl]|].
    split; [constructor|reflexivity].
  - simpl.
    pose proof (IHHty theta1 theta2 xi gamma1 gamma2
      Htheta1 Htheta2 Hgamma1 Hgamma2 Hxi Hctx) as Hnrel.
    unfold logical_relation, outcome_related in Hnrel.
    destruct Hnrel as [n1 [n2 [Hn1 [Hn2 Hnr]]]].
    destruct Hn1 as [Hvn1 Hpath1]. destruct Hn2 as [Hvn2 Hpath2].
    simpl in Hnr. destruct Hnr as [Hnum Heq]. subst n2.
    assert (Hsucc : outcome_related (value_relation Ty_Nat xi [])
      (tm_succ n1) (tm_succ n1)).
    { unfold outcome_related, reaches_value. simpl.
      exists (tm_succ n1), (tm_succ n1).
      split; [split; [apply v_nat; apply nv_succ; exact Hnum|apply multi_refl]|].
      split; [split; [apply v_nat; apply nv_succ; exact Hnum|apply multi_refl]|].
      simpl. split; [apply nv_succ; exact Hnum|reflexivity]. }
    unfold logical_relation. eapply outcome_related_precompose.
    + apply multi_succ. exact Hpath1.
    + apply multi_succ. exact Hpath2.
    + exact Hsucc.
  - simpl.
    pose proof (IHHty1 theta1 theta2 xi gamma1 gamma2
      Htheta1 Htheta2 Hgamma1 Hgamma2 Hxi Hctx) as Hnrel.
    pose proof (IHHty2 theta1 theta2 xi gamma1 gamma2
      Htheta1 Htheta2 Hgamma1 Hgamma2 Hxi Hctx) as Hbaserel.
    pose proof (IHHty3 theta1 theta2 xi gamma1 gamma2
      Htheta1 Htheta2 Hgamma1 Hgamma2 Hxi Hctx) as Hsteprel.
    unfold logical_relation, outcome_related in Hnrel.
    destruct Hnrel as [n1 [n2 [Hn1 [Hn2 Hnr]]]].
    destruct Hn1 as [Hvn1 Hnpath1]. destruct Hn2 as [Hvn2 Hnpath2].
    simpl in Hnr. destruct Hnr as [Hnum Heq]. subst n2.
    unfold logical_relation, outcome_related in Hbaserel.
    destruct Hbaserel as [vb1 [vb2 [Hvb1r [Hvb2r Hbr]]]].
    destruct Hvb1r as [Hvb1 Hbasepath1].
    destruct Hvb2r as [Hvb2 Hbasepath2].
    unfold logical_relation, outcome_related in Hsteprel.
    destruct Hsteprel as [sf1 [sf2 [Hsf1r [Hsf2r Hsr]]]].
    destruct Hsf1r as [Hsf1 Hsteppath1].
    destruct Hsf2r as [Hsf2 Hsteppath2].
    assert (Hblc1 : locally_closed_tm (instantiate theta1 gamma1 b)).
    { eapply instantiate_typed_lc; eauto. }
    assert (Hblc2 : locally_closed_tm (instantiate theta2 gamma2 b)).
    { eapply instantiate_typed_lc; eauto. }
    assert (Hslc1 : locally_closed_tm (instantiate theta1 gamma1 s)).
    { eapply instantiate_typed_lc; eauto. }
    assert (Hslc2 : locally_closed_tm (instantiate theta2 gamma2 s)).
    { eapply instantiate_typed_lc; eauto. }
    pose proof (natrec_related_values T xi n1 vb1 vb2 sf1 sf2
      Hnum Hvb1 Hvb2 Hsf1 Hsf2 Hbr Hsr) as Hrec.
    assert (Hprefix1 : tm_natrec (instantiate theta1 gamma1 n)
        (instantiate theta1 gamma1 b) (instantiate theta1 gamma1 s) -->*
        tm_natrec n1 vb1 sf1).
    { eapply multi_trans.
      - eapply multi_rec_arg; eauto.
      - eapply multi_trans.
        + eapply multi_rec_base; eauto.
        + eapply multi_rec_step; eauto. }
    assert (Hprefix2 : tm_natrec (instantiate theta2 gamma2 n)
        (instantiate theta2 gamma2 b) (instantiate theta2 gamma2 s) -->*
        tm_natrec n1 vb2 sf2).
    { eapply multi_trans.
      - eapply multi_rec_arg; eauto.
      - eapply multi_trans.
        + eapply multi_rec_base; eauto.
        + eapply multi_rec_step; eauto. }
    unfold logical_relation. eapply outcome_related_precompose; eauto.
  - simpl.
    pose proof (IHHty1 theta1 theta2 xi gamma1 gamma2
      Htheta1 Htheta2 Hgamma1 Hgamma2 Hxi Hctx) as Hleft.
    assert (Hlc11 : locally_closed_tm (instantiate theta1 gamma1 t1)).
    { eapply instantiate_typed_lc; eauto. }
    assert (Hlc12 : locally_closed_tm (instantiate theta1 gamma1 t2)).
    { eapply instantiate_typed_lc; eauto. }
    assert (Hlc21 : locally_closed_tm (instantiate theta2 gamma2 t1)).
    { eapply instantiate_typed_lc; eauto. }
    assert (Hlc22 : locally_closed_tm (instantiate theta2 gamma2 t2)).
    { eapply instantiate_typed_lc; eauto. }
    unfold logical_relation. eapply outcome_related_precompose.
    + apply multi_choice_left; assumption.
    + apply multi_choice_left; assumption.
    + exact Hleft.
Qed.

Lemma instantiate_ty_identity : forall T,
  instantiate_ty identity_type_substitution T = T.
Proof.
  induction T; simpl; try rewrite IHT1, IHT2; try rewrite IHT; reflexivity.
Qed.

Lemma instantiate_identity : forall t,
  instantiate identity_type_substitution identity_term_substitution t = t.
Proof.
  induction t; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite instantiate_ty_identity, IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt, instantiate_ty_identity. reflexivity.
  - reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2, IHt3. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma logical_relation_identity_adequacy : forall xi t U v,
  logical_relation
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) xi [] t t ->
  locally_closed_ty U -> value v ->
  tm_app (tm_tapp t U) v -->* v.
Proof.
  intros xi t U v Hrel HU Hv.
  unfold logical_relation, outcome_related in Hrel.
  destruct Hrel as [tabs1 [tabs2 [Hfirst [Hsecond Htabsrel]]]].
  destruct Hfirst as [Htabs1 Ht1].
  simpl in Htabsrel.
  destruct Htabsrel as [Hvtabs1 [Hvtabs2 Hall]].
  specialize (Hall U U (fun a b => a = v /\ b = v)).
  assert (Hclosed : forall a b, (a = v /\ b = v) ->
      locally_closed_tm a /\ locally_closed_tm b).
  { intros a b [-> ->]. split; apply value_regular; assumption. }
  specialize (Hall HU HU Hclosed).
  unfold outcome_related in Hall.
  destruct Hall as [f1 [f2 [Hthird [Hfourth Hfrelation]]]].
  destruct Hthird as [Hf1 Htypeapp1].
  destruct Hfrelation as [Hvf1 [Hvf2 Harrow]].
  specialize (Harrow v v).
  assert (Hvv : outcome_related (value_relation (Ty_BVar 0) xi
      ((fun a b => a = v /\ b = v) :: [])) v v).
  { unfold outcome_related, reaches_value. simpl.
    exists v, v. split.
    - split; [exact Hv|apply multi_refl].
    - split.
      + split; [exact Hv|apply multi_refl].
      + split; reflexivity. }
  specialize (Harrow Hvv).
  unfold outcome_related in Harrow.
  destruct Harrow as [w1 [w2 [Hfifth [Hsixth Hpair]]]].
  destruct Hfifth as [Hw1 Hbody1].
  simpl in Hpair. destruct Hpair as [-> ->].
  eapply multi_trans.
  - eapply multi_app_left.
    + eapply multi_trans.
      * apply multi_tapp; [exact Ht1|exact HU].
      * exact Htypeapp1.
    + apply value_regular; exact Hv.
  - exact Hbody1.
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
  intros t Hty U v HwfU Hv Htypedv.
  set (xi := fun (_ : atom) (_ _ : tm) => False).
  assert (Hxi : forall X a b, xi X a b ->
      locally_closed_tm a /\ locally_closed_tm b).
  { intros X a b Hfalse. contradiction. }
  assert (Hctx : related_context empty xi identity_term_substitution
      identity_term_substitution).
  { unfold related_context, empty. intros x T Hlook. discriminate. }
  pose proof (@fundamental_relation [] empty t
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) Hty
    identity_type_substitution identity_type_substitution xi
    identity_term_substitution identity_term_substitution
    identity_type_substitution_closed identity_type_substitution_closed
    identity_term_substitution_closed identity_term_substitution_closed
    Hxi Hctx) as Hfund.
  rewrite instantiate_identity in Hfund.
  eapply logical_relation_identity_adequacy.
  - exact Hfund.
  - eapply wf_ty_lc. exact HwfU.
  - exact Hv.
Qed.

End SystemFParametricityNondeterminismRecursionEasyTask.
