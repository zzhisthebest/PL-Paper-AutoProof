(** System F CBV strong-normalization benchmark, Easy variant.
    Features: nondeterminism-recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFNormalizationNondeterminismRecursionEasyTask.

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
  - apply lc_ty_nat.
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
  - apply lc_tm_zero.
  - apply lc_tm_succ; assumption.
  - apply lc_tm_rec; assumption.
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
  - apply lc_ty_nat.
  - apply lc_ty_nat.
  - exact IHHty2.
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
  - apply lc_ty_nat.
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
  - apply lc_tm_zero.
  - eauto using lc_tm_at.
  - eauto using lc_tm_at.
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
  - reflexivity.
  - rewrite IHt by assumption. reflexivity.
  - repeat rewrite in_app_iff in Hfresh.
    rewrite IHt1, IHt2, IHt3 by (try assumption; intuition). reflexivity.
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
  - reflexivity.
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
      |  | n IHn | n IHn b IHb s IHs | a IHa b IHb];
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
  - reflexivity.
  - rewrite IHn by assumption. reflexivity.
  - repeat rewrite in_app_iff in Hfresh.
    rewrite IHn, IHb, IHs by (try assumption; intuition). reflexivity.
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

Definition relation := tm -> Prop.
Record value_candidate := {
  candidate_relation : relation;
  candidate_values : forall v, candidate_relation v -> value v
}.
Definition relation_env := atom -> option value_candidate.
Definition relation_update (rho : relation_env) (X : atom) (a : value_candidate) :=
  fun Y => if Nat.eqb X Y then Some a else rho Y.

Definition expression_lifting (R : relation) (t : tm) : Prop :=
  locally_closed_tm t /\ strongly_normalizing t /\
  forall v, t -->* v -> value v -> R v.

Fixpoint value_relation (eta : list value_candidate) (rho : relation_env)
    (T : ty) (v : tm) : Prop :=
  match T with
  | Ty_BVar i =>
      match nth_error eta i with Some a => a.(candidate_relation) v | None => False end
  | Ty_FVar X =>
      match rho X with Some a => a.(candidate_relation) v | None => False end
  | Ty_Arrow T1 T2 =>
      value v /\ exists U body, v = tm_abs U body /\
      forall arg, value_relation eta rho T1 arg ->
        expression_lifting (value_relation eta rho T2) (open_tm body arg)
  | Ty_All T =>
      value v /\ exists body, v = tm_tabs body /\
      forall (U : ty) (a : value_candidate), locally_closed_ty U ->
        expression_lifting (value_relation (a :: eta) rho T) (open_tm_ty body U)
  | Ty_Nat => value v /\ numeric_value v
  end.

Definition expression_relation eta rho T t :=
  expression_lifting (value_relation eta rho T) t.

Lemma value_relation_value : forall eta rho T v,
  value_relation eta rho T v -> value v.
Proof.
  intros eta rho T v H. destruct T; simpl in H.
  - destruct (nth_error eta n) as [a|]; try contradiction.
    exact (candidate_values a v H).
  - destruct (rho a) as [b|]; try contradiction.
    exact (candidate_values b v H).
  - exact (proj1 H).
  - exact (proj1 H).
  - exact (proj1 H).
Qed.

Definition interpreted_candidate eta rho T : value_candidate :=
  {| candidate_relation := value_relation eta rho T;
     candidate_values := value_relation_value eta rho T |}.

Lemma expression_lifting_equiv : forall R S,
  (forall v, R v <-> S v) ->
  forall t, expression_lifting R t <-> expression_lifting S t.
Proof.
  unfold expression_lifting. firstorder.
Qed.

Lemma value_arrow_equiv : forall eta1 eta2 rho1 rho2 A1 A2 B1 B2,
  (forall v, value_relation eta1 rho1 A1 v <-> value_relation eta2 rho2 A2 v) ->
  (forall v, value_relation eta1 rho1 B1 v <-> value_relation eta2 rho2 B2 v) ->
  forall v, value_relation eta1 rho1 (Ty_Arrow A1 B1) v <->
            value_relation eta2 rho2 (Ty_Arrow A2 B2) v.
Proof.
  intros eta1 eta2 rho1 rho2 A1 A2 B1 B2 HA HB v. cbn [value_relation].
  split; intros [Hv [U [body [Heq Hmap]]]]; split; [exact Hv| |exact Hv|];
    exists U, body; split; [exact Heq| |exact Heq|]; intros arg Harg.
  - apply (proj1 (expression_lifting_equiv _ _ HB _)).
    apply Hmap. apply (proj2 (HA arg)). exact Harg.
  - apply (proj2 (expression_lifting_equiv _ _ HB _)).
    apply Hmap. apply (proj1 (HA arg)). exact Harg.
Qed.

Lemma value_all_equiv : forall eta1 eta2 rho1 rho2 T1 T2,
  (forall a v, value_relation (a :: eta1) rho1 T1 v <->
               value_relation (a :: eta2) rho2 T2 v) ->
  forall v, value_relation eta1 rho1 (Ty_All T1) v <->
            value_relation eta2 rho2 (Ty_All T2) v.
Proof.
  intros eta1 eta2 rho1 rho2 T1 T2 H v. cbn [value_relation].
  split; intros [Hv [body [Heq Hmap]]]; split; [exact Hv| |exact Hv|];
    exists body; split; [exact Heq| |exact Heq|]; intros U a HU.
  - apply (proj1 (expression_lifting_equiv _ _ (H a) _)). apply Hmap. exact HU.
  - apply (proj2 (expression_lifting_equiv _ _ (H a) _)). apply Hmap. exact HU.
Qed.

Lemma value_relation_env_equiv : forall T k eta1 eta2 rho,
  lc_ty_at k T ->
  (forall i, i < k -> nth_error eta1 i = nth_error eta2 i) ->
  forall v, value_relation eta1 rho T v <-> value_relation eta2 rho T v.
Proof.
  induction T; intros k eta1 eta2 rho Hlc Henv v.
  - cbn [value_relation]. rewrite Henv; [reflexivity|inversion Hlc; assumption].
  - reflexivity.
  - apply value_arrow_equiv; intros u; eapply IHT1 || eapply IHT2;
      try (inversion Hlc; eassumption); exact Henv.
  - apply value_all_equiv. intros a u.
    apply (IHT (S k)); [inversion Hlc; assumption|].
    intros i Hi. destruct i; simpl; [reflexivity|apply Henv; lia].
  - reflexivity.
Qed.

Lemma value_relation_closed_env : forall T eta1 eta2 rho,
  locally_closed_ty T ->
  forall v, value_relation eta1 rho T v <-> value_relation eta2 rho T v.
Proof.
  intros T eta1 eta2 rho Hlc. apply (value_relation_env_equiv T 0); auto.
  intros i Hi. lia.
Qed.

Lemma value_relation_rho_update_irrelevant : forall T eta rho X a,
  ~ In X (fv_ty T) ->
  forall v, value_relation eta (relation_update rho X a) T v <->
            value_relation eta rho T v.
Proof.
  induction T; intros eta rho X b Hfresh v; simpl in Hfresh.
  - reflexivity.
  - cbn [value_relation]. unfold relation_update.
    destruct (Nat.eqb X a) eqn:E; [apply Nat.eqb_eq in E; subst; tauto|reflexivity].
  - rewrite in_app_iff in Hfresh. apply value_arrow_equiv.
    + apply IHT1. tauto.
    + apply IHT2. tauto.
  - apply value_all_equiv. intros a u. apply IHT. exact Hfresh.
  - reflexivity.
Qed.

Lemma nth_error_snoc_last : forall (A : Type) (xs : list A) x,
  nth_error (xs ++ [x]) (length xs) = Some x.
Proof.
  intros A xs x. induction xs; simpl; auto.
Qed.

Lemma value_relation_open_relation : forall T k eta rho X a,
  length eta = k -> lc_ty_at (S k) T -> ~ In X (fv_ty T) ->
  forall v, value_relation (eta ++ [a]) rho T v <->
    value_relation eta (relation_update rho X a) (open_ty_rec k (Ty_FVar X) T) v.
Proof.
  induction T; intros k eta rho X b Hlen Hlc Hfresh v.
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
  - cbn [open_ty_rec]. apply value_all_equiv. intros a u.
    apply (IHT (S k) (a :: eta)); simpl; try congruence; try assumption.
    inversion Hlc; assumption.
  - reflexivity.
Qed.

Lemma value_relation_open_type : forall T k eta rho U,
  length eta = k -> lc_ty_at (S k) T -> locally_closed_ty U ->
  forall v,
    value_relation (eta ++ [interpreted_candidate [] rho U]) rho T v <->
    value_relation eta rho (open_ty_rec k U T) v.
Proof.
  induction T; intros k eta rho U Hlen Hlc HU v.
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
  - cbn [open_ty_rec]. apply value_all_equiv. intros a u.
    apply (IHT (S k) (a :: eta)); simpl; try congruence; try assumption.
    inversion Hlc; assumption.
  - reflexivity.
Qed.

Lemma numeric_value_lc : forall n, numeric_value n -> locally_closed_tm n.
Proof. intros n H. induction H; constructor; assumption. Qed.
Lemma value_regular : forall v, value v -> locally_closed_tm v.
Proof. intros v H. destruct H; try assumption; try constructor. apply numeric_value_lc. assumption. Qed.
Lemma numeral_numeric : forall n, numeric_value (numeral n).
Proof.
  induction n; simpl; constructor; assumption.
Qed.

Lemma numeric_numeral : forall t,
  numeric_value t -> exists n : nat, t = numeral n.
Proof.
  intros t H. induction H.
  - exists 0. reflexivity.
  - destruct IHnumeric_value as [m ->]. exists (S m). reflexivity.
Qed.

Lemma numeric_no_step : forall n,
  numeric_value n -> forall t, ~ (n --> t).
Proof.
  intros n Hn. induction Hn; intros u Hs; inversion Hs; subst.
  eapply IHHn. eassumption.
Qed.

Lemma value_no_step : forall v,
  value v -> forall t, ~ (v --> t).
Proof.
  intros v Hv t Hs. destruct Hv; try solve [inversion Hs].
  eapply numeric_no_step; eauto.
Qed.

Lemma step_preserves_lc : forall t u,
  t --> u -> locally_closed_tm t -> locally_closed_tm u.
Proof.
  intros t u Hstep. induction Hstep; intros Hlc; unfold locally_closed_tm in *;
    inversion Hlc; subst; eauto 10 using lc_tm_at, numeric_value_lc, value_regular.
  - eapply open_tm_preserves_lc_at.
    + inversion H; eassumption.
    + apply value_regular. exact H0.
  - eapply open_tm_ty_preserves_lc_at.
    + inversion H; eassumption.
    + exact H0.
  - assert (Hn : lc_tm_at 0 0 n) by (apply numeric_value_lc; exact H).
    apply lc_tm_app.
    + apply lc_tm_app; assumption.
    + apply lc_tm_rec; assumption.
Qed.

Lemma sn_step : forall t t',
  strongly_normalizing t ->
  t --> t' ->
  strongly_normalizing t'.
Proof.
  intros t t' Hsn Hstep.
  inversion Hsn as [t0 Hnext].
  apply Hnext. exact Hstep.
Qed.

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

Lemma value_sn : forall v,
  value v ->
  strongly_normalizing v.
Proof.
  intros v Hv.
  apply SN_intro. intros t Hstep.
  exfalso. eapply value_no_step; eauto.
Qed.

Section Compatibility.
Variable eta : list value_candidate.
Variable rho : relation_env.
Local Notation strong_value_relation := (value_relation eta rho).
Local Notation strong_expression_relation := (expression_relation eta rho).

Lemma strong_value_relation_value : forall T v,
  strong_value_relation T v -> value v.
Proof. intros T v H. eapply value_relation_value. exact H. Qed.
Lemma strong_value_relation_lc : forall T v,
  strong_value_relation T v -> locally_closed_tm v.
Proof. intros T v H. apply value_regular. eapply strong_value_relation_value. exact H. Qed.
Lemma strong_value_is_expression : forall T v,
  strong_value_relation T v ->
  strong_expression_relation T v.
Proof.
  intros T v Hv.
  split.
  - eapply strong_value_relation_lc. exact Hv.
  - split.
    + apply value_sn. eapply strong_value_relation_value. exact Hv.
    + intros v' Hmulti Hvalue.
      assert (v' = v).
      {
        eapply value_multi_eq.
        - eapply strong_value_relation_value. exact Hv.
        - exact Hmulti.
      }
      subst v'. exact Hv.
Qed.

Lemma strong_expression_step : forall T t t',
  strong_expression_relation T t ->
  t --> t' ->
  strong_expression_relation T t'.
Proof.
  intros T t t' [Hlc [Hsn Hall]] Hstep.
  split.
  - eapply step_preserves_lc; eauto.
  - split.
    + eapply sn_step; eauto.
    + intros v Hmulti Hv.
      apply Hall with (v := v); auto.
      eapply multi_step; eauto.
Qed.

Lemma strong_expression_of_reducts : forall T t,
  locally_closed_tm t ->
  ~ value t ->
  (forall t', t --> t' -> strong_expression_relation T t') ->
  strong_expression_relation T t.
Proof.
  intros T t Hlc Hnotvalue Hnext.
  split. exact Hlc.
  split.
  - apply SN_intro. intros t' Hstep.
    destruct (Hnext t' Hstep) as [_ [Hsn _]]. exact Hsn.
  - intros v Hmulti Hv.
    inversion Hmulti; subst.
    + contradiction.
    + destruct (Hnext y H) as [_ [_ Hall]].
      eapply Hall; eauto.
Qed.

Lemma strong_expression_intro : forall T t,
  locally_closed_tm t ->
  (value t -> strong_value_relation T t) ->
  (forall u, t --> u -> strong_expression_relation T u) ->
  strong_expression_relation T t.
Proof.
  intros T t Hlc HV Hnext. split. exact Hlc.
  split.
  - apply SN_intro. intros u Hstep.
    destruct (Hnext u Hstep) as [_ [Hsn _]]. exact Hsn.
  - intros v Hsteps Hv. inversion Hsteps; subst.
    + apply HV. exact Hv.
    + destruct (Hnext y H) as [_ [_ Hall]]. eapply Hall; eauto.
Qed.

End Compatibility.

Definition related_substitution (rho : relation_env) (Gamma : context)
    (gamma : term_substitution) : Prop :=
  forall x T, lookup_context x Gamma = Some T -> value_relation [] rho T (gamma x).

Lemma expression_succ : forall eta rho t,
  expression_relation eta rho Ty_Nat t ->
  locally_closed_tm (tm_succ t) ->
  expression_relation eta rho Ty_Nat (tm_succ t).
Proof.
  intros eta rho t [Htlc [Hsn Hterm]] Hlc.
  revert Htlc Hterm Hlc.
  induction Hsn as [t Hnext IH]; intros Htlc Hterm Hlc.
  eapply strong_expression_intro.
  - exact Hlc.
  - intros Hv. inversion Hv; subst; try discriminate.
    match goal with Hnum : numeric_value (tm_succ t) |- _ => inversion Hnum; subst end.
    assert (Hnumt : numeric_value t) by assumption.
    destruct (Hterm t (multi_refl t) (v_nat t Hnumt)) as [Hnv Hnumeric].
    split; [constructor; constructor; exact Hnumeric|constructor; exact Hnumeric].
  - intros u Hstep. inversion Hstep; subst.
    eapply IH.
    + exact H0.
    + eapply step_preserves_lc; eauto.
    + assert (Hexpr : expression_relation eta rho Ty_Nat t).
      { split; [exact Htlc|split; [constructor; exact Hnext|exact Hterm]]. }
      eapply strong_expression_step; [exact Hexpr|exact H0].
    + eapply step_preserves_lc; eauto.
Qed.

Lemma expression_tapp : forall rho T Uarg Usem t,
  expression_relation [] rho (Ty_All T) t ->
  lc_ty_at 1 T -> locally_closed_ty Uarg -> locally_closed_ty Usem ->
  locally_closed_tm (tm_tapp t Uarg) ->
  expression_relation [] rho (open_ty T Usem) (tm_tapp t Uarg).
Proof.
  intros rho T Uarg Usem t [Htlc [Hsn Hterm]] HT HUarg HUsem Hlc.
  revert Htlc Hterm Hlc.
  induction Hsn as [t Hnext IH]; intros Htlc Hterm Hlc.
  eapply strong_expression_intro.
  - exact Hlc.
  - intros Hv. inversion Hv; subst; try discriminate;
      match goal with Hnum : numeric_value (tm_tapp _ _) |- _ => inversion Hnum end.
  - intros u Hstep. inversion Hstep; subst.
    + assert (Hpoly : value_relation [] rho (Ty_All T) (tm_tabs t0)).
      { apply Hterm with (v := tm_tabs t0); [apply multi_refl|constructor; assumption]. }
      destruct Hpoly as [Hvt [body [Heq Hmap]]]. injection Heq as Heqbody. subst body.
      pose (a := interpreted_candidate [] rho Usem).
      pose proof (Hmap Uarg a HUarg) as Hbody.
      eapply (proj1 (expression_lifting_equiv _ _
        (fun v => @value_relation_open_type T 0 [] rho Usem eq_refl HT HUsem v) _)).
      exact Hbody.
    + assert (Hexpr : expression_relation [] rho (Ty_All T) t).
      { split; [exact Htlc|split; [constructor; exact Hnext|exact Hterm]]. }
      eapply IH.
      * exact H1.
      * eapply step_preserves_lc; eauto.
      * eapply strong_expression_step; [exact Hexpr|exact H1].
      * eapply step_preserves_lc; eauto.
Qed.

Lemma expression_app_value : forall eta rho A B f a,
  value_relation eta rho (Ty_Arrow A B) f ->
  expression_relation eta rho A a ->
  locally_closed_tm (tm_app f a) ->
  expression_relation eta rho B (tm_app f a).
Proof.
  intros eta rho A B f a Hf [Halc [Hasn Haterm]] Hlc.
  destruct Hf as [Hfv [U [body [Hfeq Hmap]]]]. subst f.
  revert Halc Haterm Hlc.
  induction Hasn as [a Hnext IH]; intros Halc Haterm Hlc.
  eapply strong_expression_intro.
  - exact Hlc.
  - intros Hv. inversion Hv; subst; try discriminate;
      match goal with Hn : numeric_value (tm_app _ _) |- _ => inversion Hn end.
  - intros u Hstep. inversion Hstep; subst.
    + apply Hmap.
      apply Haterm with (v := a); [apply multi_refl|assumption].
    + exfalso. eapply value_no_step; [exact Hfv|eassumption].
    + eapply IH.
      * eassumption.
      * eapply step_preserves_lc; eauto.
      * assert (Hexpr : expression_relation eta rho A a).
        { split; [exact Halc|split; [constructor; exact Hnext|exact Haterm]]. }
        eapply strong_expression_step; [exact Hexpr|eassumption].
      * eapply step_preserves_lc; eauto.
Qed.

Lemma expression_application : forall eta rho A B f a,
  expression_relation eta rho (Ty_Arrow A B) f ->
  expression_relation eta rho A a ->
  locally_closed_tm (tm_app f a) ->
  expression_relation eta rho B (tm_app f a).
Proof.
  intros eta rho A B f a [Hflc [Hfsn Hfterm]] Harg Hlc.
  revert Hflc Hfterm Harg Hlc.
  induction Hfsn as [f Hnext IH]; intros Hflc Hfterm Harg Hlc.
  eapply strong_expression_intro.
  - exact Hlc.
  - intros Hv. inversion Hv; subst; try discriminate;
      match goal with Hn : numeric_value (tm_app _ _) |- _ => inversion Hn end.
  - intros u Hstep. inversion Hstep; subst.
    + assert (Hfrel : value_relation eta rho (Ty_Arrow A B) (tm_abs T t)).
      { apply Hfterm with (v := tm_abs T t); [apply multi_refl|constructor; assumption]. }
      assert (Hwhole : expression_relation eta rho B (tm_app (tm_abs T t) a)).
      { eapply expression_app_value; [exact Hfrel|exact Harg|].
        apply lc_tm_app; [exact H1|apply value_regular; exact H3]. }
      eapply strong_expression_step; [exact Hwhole|constructor; assumption].
    + assert (Hexpr : expression_relation eta rho (Ty_Arrow A B) f).
      { split; [exact Hflc|split; [constructor; exact Hnext|exact Hfterm]]. }
      assert (Hf' : expression_relation eta rho (Ty_Arrow A B) t1').
      { eapply strong_expression_step; eauto. }
      eapply IH; [exact H1|exact (proj1 Hf')|exact (proj2 (proj2 Hf'))|exact Harg|].
      eapply step_preserves_lc; eauto.
    + assert (Hfrel : value_relation eta rho (Ty_Arrow A B) f).
      { apply Hfterm with (v := f); [apply multi_refl|exact H1]. }
      assert (Hwhole : expression_relation eta rho B (tm_app f a)).
      { eapply expression_app_value; [exact Hfrel|exact Harg|exact Hlc]. }
      eapply strong_expression_step; [exact Hwhole|constructor; assumption].
Qed.

Lemma expression_natrec_fixed : forall eta rho T n b s,
  numeric_value n ->
  (forall m, n = tm_succ m -> forall b' s',
    expression_relation eta rho T b' ->
    expression_relation eta rho (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s' ->
    expression_relation eta rho T (tm_natrec m b' s')) ->
  expression_relation eta rho T b ->
  expression_relation eta rho (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  locally_closed_tm (tm_natrec n b s) ->
  expression_relation eta rho T (tm_natrec n b s).
Proof.
  intros eta rho T n b s Hn Hpred [Hblc [Hbsn Hbterm]]
    [Hslc [Hssn Hsterm]] Hlc.
  revert s Hssn Hslc Hsterm Hlc Hpred.
  induction Hbsn as [b Hnextb IHb]; intros s Hssn Hslc Hsterm Hlc Hpred.
  revert Hlc Hpred.
  induction Hssn as [s Hnexts IHs]; intros Hlc Hpred.
  eapply strong_expression_intro.
  - exact Hlc.
  - intros Hv. inversion Hv; subst; try discriminate;
      match goal with Hnum : numeric_value (tm_natrec _ _ _) |- _ => inversion Hnum end.
  - intros u Hstep. inversion Hstep; subst.
    + exfalso. eapply numeric_no_step; [exact Hn|exact H2].
    + eapply IHb.
      * exact H4.
      * eapply step_preserves_lc; [exact H4|exact Hblc].
      * eapply strong_expression_step.
        -- split; [exact Hblc|split; [constructor; exact Hnextb|exact Hbterm]].
        -- exact H4.
      * constructor. exact Hnexts.
      * exact Hslc.
      * exact Hsterm.
      * eapply step_preserves_lc; eauto.
      * exact Hpred.
    + eapply IHs.
      * exact H5.
      * eapply step_preserves_lc; [exact H5|exact Hslc].
      * eapply strong_expression_step.
        -- split; [exact Hslc|split; [constructor; exact Hnexts|exact Hsterm]].
        -- exact H5.
      * eapply step_preserves_lc; eauto.
      * exact Hpred.
    + assert (Hbr : value_relation eta rho T u).
      { apply Hbterm with (v := u); [apply multi_refl|exact H3]. }
      eapply strong_value_is_expression. exact Hbr.
    + assert (Hbr : value_relation eta rho T b).
      { apply Hbterm with (v := b); [apply multi_refl|exact H4]. }
      assert (Hsr : value_relation eta rho (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s).
      { apply Hsterm with (v := s); [apply multi_refl|exact H5]. }
      assert (Hbe : expression_relation eta rho T b) by (eapply strong_value_is_expression; exact Hbr).
      assert (Hse : expression_relation eta rho (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s)
        by (eapply strong_value_is_expression; exact Hsr).
      assert (Hnr : value_relation eta rho Ty_Nat n0).
      { split; [apply v_nat; exact H2|exact H2]. }
      assert (Hne : expression_relation eta rho Ty_Nat n0)
        by (eapply strong_value_is_expression; exact Hnr).
      assert (Hinner : expression_relation eta rho T (tm_natrec n0 b s)).
      { eapply (Hpred n0 eq_refl); eauto. }
      assert (Happ : expression_relation eta rho (Ty_Arrow T T) (tm_app s n0)).
      { eapply expression_application; [exact Hse|exact Hne|].
        apply lc_tm_app; [apply value_regular; eapply value_relation_value; exact Hsr|apply numeric_value_lc; exact H2]. }
      eapply expression_application; [exact Happ|exact Hinner|].
      eapply step_preserves_lc; eauto.
Qed.

Lemma expression_natrec_zero : forall eta rho T b s,
  expression_relation eta rho T b ->
  expression_relation eta rho (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  locally_closed_tm (tm_natrec tm_zero b s) ->
  expression_relation eta rho T (tm_natrec tm_zero b s).
Proof.
  intros eta rho T b s [Hblc [Hbsn Hbterm]] [Hslc [Hssn Hsterm]] Hlc.
  revert s Hssn Hslc Hsterm Hlc.
  induction Hbsn as [b Hnextb IHb]; intros s Hssn Hslc Hsterm Hlc.
  revert Hlc.
  induction Hssn as [s Hnexts IHs]; intros Hlc.
  eapply strong_expression_intro.
  - exact Hlc.
  - intros Hv. inversion Hv; subst; try discriminate;
      match goal with Hnum : numeric_value (tm_natrec _ _ _) |- _ => inversion Hnum end.
  - intros u Hstep. inversion Hstep; subst.
    + exfalso. eapply numeric_no_step; [constructor|exact H2].
    + eapply IHb.
      * exact H4.
      * eapply step_preserves_lc; [exact H4|exact Hblc].
      * eapply strong_expression_step.
        -- split; [exact Hblc|split; [constructor; exact Hnextb|exact Hbterm]].
        -- exact H4.
      * constructor. exact Hnexts.
      * exact Hslc.
      * exact Hsterm.
      * eapply step_preserves_lc; eauto.
    + eapply IHs.
      * exact H5.
      * eapply step_preserves_lc; [exact H5|exact Hslc].
      * eapply strong_expression_step.
        -- split; [exact Hslc|split; [constructor; exact Hnexts|exact Hsterm]].
        -- exact H5.
      * eapply step_preserves_lc; eauto.
    + assert (Hbr : value_relation eta rho T u).
      { apply Hbterm with (v := u); [apply multi_refl|exact H1]. }
      eapply strong_value_is_expression. exact Hbr.
Qed.

Lemma expression_natrec_numeric : forall eta rho T n,
  numeric_value n ->
  forall b s,
    expression_relation eta rho T b ->
    expression_relation eta rho (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
    locally_closed_tm (tm_natrec n b s) ->
    expression_relation eta rho T (tm_natrec n b s).
Proof.
  intros eta rho T n Hn. induction Hn; intros b s Hb Hs Hlc.
  - eapply expression_natrec_zero; eauto.
  - eapply expression_natrec_fixed.
    + constructor; assumption.
    + intros m Hm b' s' Hb' Hs'. injection Hm as Heq. subst m.
      eapply IHHn; [exact Hb'|exact Hs'|].
      apply lc_tm_rec; [apply numeric_value_lc; exact Hn|exact (proj1 Hb')|exact (proj1 Hs')].
    + exact Hb.
    + exact Hs.
    + exact Hlc.
Qed.

Lemma expression_natrec : forall eta rho T n b s,
  expression_relation eta rho Ty_Nat n ->
  expression_relation eta rho T b ->
  expression_relation eta rho (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  locally_closed_tm (tm_natrec n b s) ->
  expression_relation eta rho T (tm_natrec n b s).
Proof.
  intros eta rho T n b s [Hnlc [Hnsn Hnterm]] Hb Hs Hlc.
  revert b s Hb Hs Hlc.
  induction Hnsn as [n Hnext IH]; intros b s Hb Hs Hlc.
  eapply strong_expression_intro.
  - exact Hlc.
  - intros Hv. inversion Hv; subst; try discriminate;
      match goal with Hnum : numeric_value (tm_natrec _ _ _) |- _ => inversion Hnum end.
  - intros u Hstep. inversion Hstep; subst.
    + assert (Hexpr : expression_relation eta rho Ty_Nat n).
      { split; [exact Hnlc|split; [constructor; exact Hnext|exact Hnterm]]. }
      eapply IH.
      * exact H2.
      * eapply step_preserves_lc; [exact H2|exact Hnlc].
      * eapply strong_expression_step; [exact Hexpr|exact H2].
      * exact Hb.
      * exact Hs.
      * eapply step_preserves_lc; [exact Hstep|exact Hlc].
    + eapply strong_expression_step.
      * exact (@expression_natrec_numeric eta rho T n H2 b s Hb Hs Hlc).
      * exact Hstep.
    + eapply strong_expression_step.
      * exact (@expression_natrec_numeric eta rho T n H2 b s Hb Hs Hlc).
      * exact Hstep.
    + eapply strong_expression_step.
      * exact (@expression_natrec_numeric eta rho T tm_zero nv_zero u s Hb Hs Hlc).
      * exact Hstep.
    + eapply strong_expression_step.
      * exact (@expression_natrec_numeric eta rho T (tm_succ n0) (nv_succ n0 H2) b s Hb Hs Hlc).
      * exact Hstep.
Qed.

Lemma related_substitution_update : forall rho Gamma gamma x T v,
  related_substitution rho Gamma gamma -> value_relation [] rho T v ->
  related_substitution rho (update Gamma x T) (term_subst_update gamma x v).
Proof.
  intros rho Gamma gamma x T v Hrel HV y U Hy.
  unfold update, term_subst_update in *. simpl in Hy.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y. rewrite Nat.eqb_refl.
    injection Hy as ->. exact HV.
  - assert (E' : Nat.eqb x y = false) by (apply Nat.eqb_neq; apply Nat.eqb_neq in E; congruence).
    rewrite E'. apply Hrel. exact Hy.
Qed.

Lemma lookup_context_ftv : forall Gamma x T X,
  lookup_context x Gamma = Some T -> In X (fv_ty T) -> In X (ftv_context Gamma).
Proof.
  induction Gamma as [|[y U] Gamma IH]; intros x T X Hlookup Hin; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y).
    + injection Hlookup as ->. apply in_or_app. left. exact Hin.
    + apply in_or_app. right. eapply IH; eauto.
Qed.

Lemma related_substitution_relation_update : forall rho Gamma gamma X a,
  related_substitution rho Gamma gamma -> ~ In X (ftv_context Gamma) ->
  related_substitution (relation_update rho X a) Gamma gamma.
Proof.
  intros rho Gamma gamma X a Hrel Hfresh x T Hlookup.
  assert (Hnot : ~ In X (fv_ty T)).
  { intros Hin. apply Hfresh. eapply lookup_context_ftv; eauto. }
  apply (proj2 (value_relation_rho_update_irrelevant T [] rho X a Hnot (gamma x))).
  apply Hrel. exact Hlookup.
Qed.

(* Optional reference theorem statement.
Theorem fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall theta rho gamma,
    type_substitution_closed theta -> term_substitution_closed gamma ->
    related_substitution rho Gamma gamma ->
    expression_relation [] rho T (instantiate theta gamma t).
*)

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  (* The type environment records candidates for the free type variables. *)
  assert (Hfund : forall Delta Gamma t T,
      has_type Delta Gamma t T -> forall theta rho gamma,
      type_substitution_closed theta ->
      (forall X, In X Delta -> exists a, rho X = Some a) ->
      term_substitution_closed gamma ->
      related_substitution rho Gamma gamma ->
      expression_relation [] rho T (instantiate theta gamma t)).
  {
    intros Delta Gamma t T Hty. induction Hty; intros theta rho gamma Htheta Henv Hclosed Hsub.
    - simpl. specialize (Hsub x T H). apply strong_value_is_expression. exact Hsub.
    - simpl.
      assert (Habs : locally_closed_tm (tm_abs T1 t2)).
      { apply lc_tm_abs.
        - eapply wf_ty_lc. exact H.
        - set (x := fresh L).
          assert (Hfresh : ~ In x L) by (unfold x; apply fresh_notin).
          assert (Hbody : lc_tm_at 0 1 t2).
          { unfold open_tm. eapply lc_tm_at_open_tm_inv. eapply typing_lc. exact (H0 x Hfresh). }
          exact Hbody. }
      assert (Hinst : locally_closed_tm (instantiate theta gamma (tm_abs T1 t2))).
      { eapply instantiate_lc_at; [exact Habs|exact Htheta|exact Hclosed]. }
      eapply strong_expression_intro.
      + exact Hinst.
      + intros _. split.
        * constructor. exact Hinst.
        * exists (instantiate_ty theta T1), (instantiate theta gamma t2). split; [reflexivity|].
          intros arg Harg.
          set (x := fresh (L ++ fv_tm t2)).
          assert (HfreshL : ~ In x L).
          { unfold x. intro Hin. apply (fresh_notin (L ++ fv_tm t2)). apply in_or_app. left. exact Hin. }
          assert (HfreshT : ~ In x (fv_tm t2)).
          { unfold x. intro Hin. apply (fresh_notin (L ++ fv_tm t2)). apply in_or_app. right. exact Hin. }
          specialize (H1 x HfreshL theta rho (term_subst_update gamma x arg) Htheta Henv).
          assert (Hclosed' : term_substitution_closed (term_subst_update gamma x arg)).
          { apply term_subst_update_closed; [exact Hclosed|]. eapply value_regular. eapply value_relation_value. exact Harg. }
          assert (Hsub' : related_substitution rho (update Gamma x T1) (term_subst_update gamma x arg)).
          { eapply related_substitution_update; eauto. }
          specialize (H1 Hclosed' Hsub').
          rewrite (instantiate_open_tm t2 theta gamma x arg
            HfreshT Htheta Hclosed
            (@value_regular arg (@value_relation_value [] rho T1 arg Harg))) in H1.
          exact H1.
      + intros u Hstep. inversion Hstep.
    - specialize (IHHty1 theta rho gamma Htheta Henv Hclosed Hsub).
      specialize (IHHty2 theta rho gamma Htheta Henv Hclosed Hsub).
      eapply expression_application; [exact IHHty1|exact IHHty2|].
      apply lc_tm_app; [exact (proj1 IHHty1)|exact (proj1 IHHty2)].
    - set (x := fresh (L ++ Delta ++ fv_ty T ++ ftv_tm t ++ ftv_context Gamma)).
      assert (Havoid : ~ In x (L ++ Delta ++ fv_ty T ++ ftv_tm t ++ ftv_context Gamma)).
      { unfold x. apply fresh_notin. }
      assert (HfreshL : ~ In x L).
      { intro Hin. apply Havoid. apply in_or_app. left. exact Hin. }
      assert (HT : lc_ty_at 1 T).
      { pose proof (@typing_type_lc (x :: Delta) Gamma
          (open_tm_ty t (Ty_FVar x)) (open_ty T (Ty_FVar x)) (H x HfreshL)) as Htypelc.
        unfold locally_closed_ty in Htypelc. eapply lc_ty_at_open_inv; exact Htypelc. }
      assert (HfreshDelta : ~ In x Delta).
      { intro Hin. apply Havoid. apply in_or_app. right. apply in_or_app. left. exact Hin. }
      assert (HfreshTy : ~ In x (fv_ty T)).
      { intro Hin. apply Havoid. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hin. }
      assert (HfreshTerm : ~ In x (ftv_tm t)).
      { intro Hin. apply Havoid. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hin. }
      assert (HfreshCtx : ~ In x (ftv_context Gamma)).
      { intro Hin. apply Havoid. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact Hin. }
      assert (Htabs : locally_closed_tm (tm_tabs t)).
      { apply lc_tm_tabs. eapply lc_tm_at_open_ty_inv with (X := x).
        eapply typing_lc. exact (H x HfreshL). }
      assert (Hinst : locally_closed_tm (instantiate theta gamma (tm_tabs t))).
      { eapply instantiate_lc_at; [exact Htabs|exact Htheta|exact Hclosed]. }
      eapply strong_expression_intro.
      + exact Hinst.
      + intros _. split.
        * constructor. exact Hinst.
        * exists (instantiate theta gamma t). split; [reflexivity|].
          intros U a HU.
          set (theta' := type_subst_update theta x U).
          set (rho' := relation_update rho x a).
          assert (Htheta' : type_substitution_closed theta').
          { unfold theta'. apply type_subst_update_closed; assumption. }
          assert (Henv' : forall Y, In Y (x :: Delta) -> exists c, rho' Y = Some c).
          { intros Y HY. simpl in HY. destruct HY as [<-|HY].
            - exists a. unfold rho'. unfold relation_update. rewrite Nat.eqb_refl. reflexivity.
            - destruct (Henv Y HY) as [c Hc]. exists c. unfold rho', relation_update.
              assert (Heq : Nat.eqb x Y = false) by (apply Nat.eqb_neq; intro E; subst; contradiction).
              rewrite Heq. exact Hc. }
          assert (Hsub' : related_substitution rho' Gamma gamma).
          { unfold rho'. eapply related_substitution_relation_update; eauto. }
          specialize (H0 x HfreshL theta' rho' gamma Htheta' Henv' Hclosed Hsub').
          unfold theta' in H0.
          rewrite (instantiate_open_ty t theta gamma x U HfreshTerm Htheta Hclosed HU) in H0.
          eapply (proj1 (expression_lifting_equiv _ _
            (fun v => iff_sym (@value_relation_open_relation T 0 [] rho x a eq_refl HT HfreshTy v)) _)).
          exact H0.
      + intros u Hstep. inversion Hstep.
    - specialize (IHHty theta rho gamma Htheta Henv Hclosed Hsub).
      assert (HT : lc_ty_at 1 T).
      { pose proof (@typing_type_lc Delta Gamma t (Ty_All T) Hty) as Hclosedall. inversion Hclosedall; assumption. }
      assert (HU : locally_closed_ty U) by (eapply wf_ty_lc; eauto).
      assert (HUarg : locally_closed_ty (instantiate_ty theta U))
        by (eapply instantiate_ty_closed; eauto).
      eapply expression_tapp; [exact IHHty|exact HT|exact HUarg|exact HU|].
      apply lc_tm_tapp; [exact (proj1 IHHty)|exact HUarg].
    - simpl. eapply strong_expression_intro.
      + apply lc_tm_zero.
      + intros Hv. split; [exact Hv|constructor].
      + intros u Hs. inversion Hs.
    - specialize (IHHty theta rho gamma Htheta Henv Hclosed Hsub).
      eapply expression_succ; [exact IHHty|].
      apply lc_tm_succ. exact (proj1 IHHty).
    - specialize (IHHty1 theta rho gamma Htheta Henv Hclosed Hsub).
      specialize (IHHty2 theta rho gamma Htheta Henv Hclosed Hsub).
      specialize (IHHty3 theta rho gamma Htheta Henv Hclosed Hsub).
      eapply expression_natrec; [exact IHHty1|exact IHHty2|exact IHHty3|].
      apply lc_tm_rec; [exact (proj1 IHHty1)|exact (proj1 IHHty2)|exact (proj1 IHHty3)].
    - specialize (IHHty1 theta rho gamma Htheta Henv Hclosed Hsub).
      specialize (IHHty2 theta rho gamma Htheta Henv Hclosed Hsub).
      eapply strong_expression_intro.
      + apply lc_tm_choice; [exact (proj1 IHHty1)|exact (proj1 IHHty2)].
      + intros Hv. inversion Hv; subst; try discriminate; match goal with Hn : numeric_value _ |- _ => inversion Hn end.
      + intros u Hs. inversion Hs; subst; assumption.
  }
  intros t T Hty.
  assert (Hemptyenv : forall X, In X ([] : ty_context) -> exists a, (fun _ : atom => @None value_candidate) X = Some a).
  { intros X HX. inversion HX. }
  assert (Hemptysub : related_substitution (fun _ : atom => @None value_candidate) empty identity_term_substitution).
  { intros x U H. discriminate H. }
  specialize (Hfund [] empty t T Hty identity_type_substitution
    (fun _ : atom => @None value_candidate) identity_term_substitution
    identity_type_substitution_closed Hemptyenv identity_term_substitution_closed Hemptysub).
  rewrite instantiate_identity in Hfund.
  destruct Hfund as [_ [Hsn _]]. exact Hsn.
Qed.

End SystemFNormalizationNondeterminismRecursionEasyTask.
