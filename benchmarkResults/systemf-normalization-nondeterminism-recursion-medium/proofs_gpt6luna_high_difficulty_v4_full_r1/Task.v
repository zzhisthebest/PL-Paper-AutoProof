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

Lemma sn_of_successors : forall t,
  (forall u, t --> u -> strongly_normalizing u) -> strongly_normalizing t.
Proof. intros; constructor; assumption. Qed.

Lemma sn_step_inv : forall t u,
  strongly_normalizing t -> t --> u -> strongly_normalizing u.
Proof. intros t u H; inversion H; eauto. Qed.

Lemma sn_no_step : forall t,
  strongly_normalizing t -> (forall u, ~ t --> u) -> strongly_normalizing t.
Proof. auto. Qed.

Lemma canonical_nat_closed : forall v,
  has_type [] empty v Ty_Nat -> value v -> numeric_value v.
Proof.
  intros v Hty Hv. inversion Hv; subst; inversion Hty; subst; eauto using numeric_value.
Qed.

Lemma canonical_arrow_closed : forall v A B,
  has_type [] empty v (Ty_Arrow A B) -> value v ->
  exists t, v = tm_abs A t.
Proof.
  intros v A B Hty Hv. destruct Hv as [T t Hlc|t Hlc|n Hnum].
  - inversion Hty; subst. eexists; reflexivity.
  - inversion Hty.
  - inversion Hnum; subst; inversion Hty.
Qed.

Lemma canonical_all_closed : forall v T,
  has_type [] empty v (Ty_All T) -> value v ->
  exists t, v = tm_tabs t.
Proof.
  intros v T Hty Hv. destruct Hv as [A t Hlc|t Hlc|n Hnum].
  - inversion Hty.
  - inversion Hty; subst. eexists; reflexivity.
  - inversion Hnum; subst; inversion Hty.
Qed.

Lemma sn_succ : forall t,
  strongly_normalizing t -> strongly_normalizing (tm_succ t).
Proof.
  intros t H. induction H. constructor. intros u Hu. inversion Hu; subst.
  apply H0. assumption.
Qed.

Lemma sn_choice : forall t1 t2,
  strongly_normalizing t1 -> strongly_normalizing t2 ->
  strongly_normalizing (tm_choice t1 t2).
Proof.
  intros t1 t2 H1 H2. constructor. intros u Hu. inversion Hu; subst; assumption.
Qed.

Inductive etm : Type :=
| e_bvar : nat -> etm | e_fvar : atom -> etm
| e_abs : etm -> etm | e_app : etm -> etm -> etm
| e_tabs : etm -> etm | e_tapp : etm -> etm
| e_zero : etm | e_succ : etm -> etm
| e_natrec : etm -> etm -> etm -> etm
| e_choice : etm -> etm -> etm.

Inductive elc_at : nat -> etm -> Prop :=
| elc_bvar : forall k i, i < k -> elc_at k (e_bvar i)
| elc_fvar : forall k x, elc_at k (e_fvar x)
| elc_abs : forall k b, elc_at (S k) b -> elc_at k (e_abs b)
| elc_app : forall k a b, elc_at k a -> elc_at k b -> elc_at k (e_app a b)
| elc_tabs : forall k b, elc_at k b -> elc_at k (e_tabs b)
| elc_tapp : forall k a, elc_at k a -> elc_at k (e_tapp a)
| elc_zero : forall k, elc_at k e_zero
| elc_succ : forall k a, elc_at k a -> elc_at k (e_succ a)
| elc_natrec : forall k n b s, elc_at k n -> elc_at k b -> elc_at k s -> elc_at k (e_natrec n b s)
| elc_choice : forall k a b, elc_at k a -> elc_at k b -> elc_at k (e_choice a b).
Definition elc (t : etm) := elc_at 0 t.

Lemma elc_at_mono : forall k k' t, elc_at k t -> k <= k' -> elc_at k' t.
Proof.
  intros k k' t H; revert k'. induction H; intros k' Hle.
  - constructor; lia.
  - constructor.
  - constructor. apply IHelc_at. lia.
  - constructor; eauto.
  - constructor. apply IHelc_at. lia.
  - constructor; eauto.
  - constructor.
  - constructor; eauto.
  - constructor; eauto.
  - constructor; eauto.
Qed.

Fixpoint erase (t : tm) : etm :=
  match t with
  | tm_bvar i => e_bvar i | tm_fvar x => e_fvar x
  | tm_abs _ b => e_abs (erase b)
  | tm_app a b => e_app (erase a) (erase b)
  | tm_tabs b => e_tabs (erase b)
  | tm_tapp a _ => e_tapp (erase a)
  | tm_zero => e_zero | tm_succ a => e_succ (erase a)
  | tm_natrec n b s => e_natrec (erase n) (erase b) (erase s)
  | tm_choice a b => e_choice (erase a) (erase b)
  end.

Fixpoint eopen_rec (k : nat) (u t : etm) : etm :=
  match t with
  | e_bvar i => if Nat.eqb k i then u else e_bvar i
  | e_fvar x => e_fvar x
  | e_abs b => e_abs (eopen_rec (S k) u b)
  | e_app a b => e_app (eopen_rec k u a) (eopen_rec k u b)
  | e_tabs b => e_tabs (eopen_rec k u b)
  | e_tapp a => e_tapp (eopen_rec k u a)
  | e_zero => e_zero | e_succ a => e_succ (eopen_rec k u a)
  | e_natrec n b s => e_natrec (eopen_rec k u n) (eopen_rec k u b) (eopen_rec k u s)
  | e_choice a b => e_choice (eopen_rec k u a) (eopen_rec k u b)
  end.
Definition eopen (t u : etm) := eopen_rec 0 u t.

Lemma eopen_rec_preserves_elc : forall t k u,
  elc_at (S k) t -> elc u -> elc_at k (eopen_rec k u t).
Proof.
  induction t; intros k u Ht Hu; simpl; inversion Ht; subst; eauto using elc_at.
  destruct (Nat.eqb k n) eqn:E.
  - eapply elc_at_mono; [exact Hu|lia].
  - apply Nat.eqb_neq in E. constructor. lia.
Qed.

Lemma eopen_rec_lc_identity : forall t k u,
  elc_at k t -> eopen_rec k u t = t.
Proof.
  induction t; intros k u Hlc; inversion Hlc; subst; simpl.
  - destruct (Nat.eqb k n) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - reflexivity.
  - f_equal. eapply IHt. eassumption.
  - f_equal; [eapply IHt1|eapply IHt2]; eassumption.
  - f_equal. eapply IHt. eassumption.
  - f_equal. eapply IHt. eassumption.
  - reflexivity.
  - f_equal. eapply IHt. eassumption.
  - f_equal; [eapply IHt1|eapply IHt2|eapply IHt3]; eassumption.
  - f_equal; [eapply IHt1|eapply IHt2]; eassumption.
Qed.

Fixpoint esubst (x : atom) (u t : etm) : etm :=
  match t with
  | e_bvar i => e_bvar i
  | e_fvar y => if Nat.eqb x y then u else e_fvar y
  | e_abs b => e_abs (esubst x u b)
  | e_app a b => e_app (esubst x u a) (esubst x u b)
  | e_tabs b => e_tabs (esubst x u b)
  | e_tapp a => e_tapp (esubst x u a)
  | e_zero => e_zero | e_succ a => e_succ (esubst x u a)
  | e_natrec n b s => e_natrec (esubst x u n) (esubst x u b) (esubst x u s)
  | e_choice a b => e_choice (esubst x u a) (esubst x u b)
  end.

Inductive enumeric : etm -> Prop :=
| en_zero : enumeric e_zero
| en_succ : forall n, enumeric n -> enumeric (e_succ n).
Inductive evalue : etm -> Prop :=
| ev_abs : forall b, evalue (e_abs b)
| ev_tabs : forall b, evalue (e_tabs b)
| ev_nat : forall n, enumeric n -> evalue n.
Inductive eneutral : etm -> Prop :=
| en_bvar : forall i, eneutral (e_bvar i)
| en_fvar : forall x, eneutral (e_fvar x)
| en_app : forall a b, eneutral (e_app a b)
| en_tapp : forall a, eneutral (e_tapp a)
| en_natrec : forall n b s, eneutral (e_natrec n b s)
| en_choice : forall a b, eneutral (e_choice a b)
| ene_succ : forall n, ~ enumeric n -> eneutral (e_succ n).

Inductive estep : etm -> etm -> Prop :=
| ES_AppAbs : forall b v, evalue v -> estep (e_app (e_abs b) v) (eopen b v)
| ES_App1 : forall a a' b, estep a a' -> estep (e_app a b) (e_app a' b)
| ES_App2 : forall v b b', evalue v -> estep b b' -> estep (e_app v b) (e_app v b')
| ES_TAppTabs : forall b, estep (e_tapp (e_tabs b)) b
| ES_TApp : forall a a', estep a a' -> estep (e_tapp a) (e_tapp a')
| ES_Succ : forall a a', estep a a' -> estep (e_succ a) (e_succ a')
| ES_RecArg : forall n n' b s, estep n n' -> estep (e_natrec n b s) (e_natrec n' b s)
| ES_RecBase : forall n b b' s, enumeric n -> estep b b' -> estep (e_natrec n b s) (e_natrec n b' s)
| ES_RecStep : forall n b s s', enumeric n -> evalue b -> estep s s' -> estep (e_natrec n b s) (e_natrec n b s')
| ES_RecZero : forall b s, evalue b -> evalue s -> estep (e_natrec e_zero b s) b
| ES_RecSucc : forall n b s, enumeric n -> evalue b -> evalue s ->
    estep (e_natrec (e_succ n) b s) (e_app (e_app s n) (e_natrec n b s))
| ES_ChoiceLeft : forall a b, estep (e_choice a b) a
| ES_ChoiceRight : forall a b, estep (e_choice a b) b.

Inductive emulti : etm -> etm -> Prop :=
| em_refl : forall t, emulti t t
| em_step : forall t u v, estep t u -> emulti u v -> emulti t v.
Inductive esn : etm -> Prop :=
| esn_intro : forall t, (forall u, estep t u -> esn u) -> esn t.

Lemma enumeric_elc : forall n, enumeric n -> elc n.
Proof. intros n H; induction H as [|n Hn IH]; [apply elc_zero|apply elc_succ; exact IH]. Qed.

Lemma estep_preserves_elc : forall t u,
  estep t u -> elc t -> elc u.
Proof.
  intros t u Hs; induction Hs; intros Hlc; inversion Hlc; subst.
  - apply eopen_rec_preserves_elc with (k := 0).
    + inversion H3; assumption.
    + assumption.
  - apply elc_app; [eapply IHHs; eassumption|assumption].
  - apply elc_app; [assumption|eapply IHHs; eassumption].
  - match goal with Htabs : elc_at 0 (e_tabs _) |- _ => inversion Htabs; assumption end.
  - apply elc_tapp. eapply IHHs; eassumption.
  - apply elc_succ. eapply IHHs; eassumption.
  - apply elc_natrec; [eapply IHHs; eassumption|assumption|assumption].
  - apply elc_natrec; [assumption|eapply IHHs; eassumption|assumption].
  - apply elc_natrec; [assumption|assumption|eapply IHHs; eassumption].
  - assumption.
  - apply elc_app.
    + apply elc_app; [assumption|apply enumeric_elc; assumption].
    + apply elc_natrec; [apply enumeric_elc; assumption|assumption|assumption].
  - assumption.
  - assumption.
Qed.

Lemma erase_open_rec : forall t k u,
  erase (open_tm_rec k u t) = eopen_rec k (erase u) (erase t).
Proof.
  induction t; intros k u; simpl; try rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3; try reflexivity.
  destruct (Nat.eqb k n); reflexivity.
Qed.
Lemma erase_open : forall t u,
  erase (open_tm t u) = eopen (erase t) (erase u).
Proof. intros; apply erase_open_rec. Qed.
Lemma erase_open_tm_ty : forall t U,
  erase (open_tm_ty t U) = erase t.
Proof.
  intros t U; unfold open_tm_ty. generalize 0 as k. revert U.
  induction t; intros U k; simpl; rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3; reflexivity.
Qed.
Lemma erase_numeric : forall n, numeric_value n -> enumeric (erase n).
Proof. intros n H; induction H; simpl; constructor; assumption. Qed.
Lemma erase_value : forall v, value v -> evalue (erase v).
Proof. intros v H; destruct H; simpl; eauto using evalue, erase_numeric. Qed.

Lemma erase_step : forall t u, t --> u -> estep (erase t) (erase u).
Proof.
  intros t u H; induction H; simpl.
  - rewrite erase_open. constructor. eapply erase_value; eassumption.
  - constructor; assumption.
  - econstructor; eauto using erase_value.
  - rewrite erase_open_tm_ty. constructor.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
  - econstructor; eauto using erase_numeric.
  - econstructor; eauto using erase_numeric, erase_value.
  - econstructor; eauto using erase_value.
  - econstructor; eauto using erase_numeric, erase_value.
  - constructor.
  - constructor.
Qed.

Lemma erase_sn_reflect_gen : forall e,
  esn e -> forall t, erase t = e -> strongly_normalizing t.
Proof.
  intros e H. induction H as [e Hrec IH]. intros t He.
  constructor. intros u Hu. eapply (IH (erase u)).
  - rewrite <- He. eapply erase_step; eassumption.
  - reflexivity.
Qed.

Lemma erase_sn_reflect : forall t,
  esn (erase t) -> strongly_normalizing t.
Proof. intros; eapply erase_sn_reflect_gen; eauto. Qed.

Lemma esn_step_inv : forall t u, esn t -> estep t u -> esn u.
Proof. intros t u H; inversion H; eauto. Qed.
Lemma enumeric_no_step : forall n, enumeric n -> forall u, ~ estep n u.
Proof.
  intros n Hn. induction Hn; intros u Hu; inversion Hu; subst; eauto.
  eapply IHHn; eassumption.
Qed.
Lemma evalue_no_step : forall v, evalue v -> forall u, ~ estep v u.
Proof.
  intros v Hv u Hs. destruct Hv; try solve [inversion Hs].
  eapply enumeric_no_step; eauto.
Qed.
Lemma enumeric_value : forall n, enumeric n -> evalue n.
Proof. intros n H; induction H; [apply ev_nat; constructor|apply ev_nat; constructor; assumption]. Qed.
Lemma eneutral_not_value : forall t, eneutral t -> ~ evalue t.
Proof.
  intros t Hn Hv. inversion Hn; subst; inversion Hv; subst; try discriminate;
    try (inversion H).
  exfalso. inversion H0; subst. apply H. assumption.
Qed.

Lemma emulti_step_inv : forall t v, emulti t v ->
  t = v \/ exists u, estep t u /\ emulti u v.
Proof.
  intros t v H; inversion H; subst; eauto.
Qed.

Definition ends_numeric (t : etm) : Prop :=
  forall v, emulti t v -> evalue v -> enumeric v.

Definition candidate_ok (P : etm -> Prop) : Prop :=
  (forall t, P t -> esn t) /\
  (forall t, P t -> elc t) /\
  (forall t u, P t -> estep t u -> P u) /\
  (forall t, elc t -> eneutral t -> (forall u, estep t u -> P u) -> P t).

Definition cand_sn {P} (H : candidate_ok P) := proj1 H.
Definition cand_lc {P} (H : candidate_ok P) := proj1 (proj2 H).
Definition cand_step {P} (H : candidate_ok P) := proj1 (proj2 (proj2 H)).
Definition cand_neutral {P} (H : candidate_ok P) := proj2 (proj2 (proj2 H)).

Lemma sn_candidate_ok : candidate_ok (fun t => esn t /\ elc t).
Proof.
  split.
  - intros t [Hs _]; exact Hs.
  - split.
    + intros t [_ Hl]; exact Hl.
    + split.
      * intros t u [Hs Hl] Hstep. split.
        -- eapply esn_step_inv; eauto.
        -- eapply estep_preserves_elc; eauto.
      * intros t Hlc Hn Hsteps. split.
        -- apply esn_intro. intros u Hu. apply (proj1 (Hsteps u Hu)).
        -- exact Hlc.
Qed.

Fixpoint reducible (T : ty) (rho : list (etm -> Prop))
    (eta : atom -> etm -> Prop) : etm -> Prop :=
  match T with
  | Ty_BVar i => match nth_error rho i with Some P => P | None => fun t => esn t /\ elc t end
  | Ty_FVar X => eta X
  | Ty_Arrow A B => fun t => esn t /\ elc t /\
      (forall u, reducible A rho eta u -> reducible B rho eta (e_app t u))
  | Ty_All B => fun t => esn t /\ elc t /\
      (forall C, candidate_ok C -> reducible B (C :: rho) eta (e_tapp t))
  | Ty_Nat => fun t => esn t /\ elc t /\ ends_numeric t
  end.

Fixpoint insert_candidate (k : nat) (C : etm -> Prop)
    (rho : list (etm -> Prop)) : list (etm -> Prop) :=
  match k, rho with
  | 0, _ => C :: rho
  | S k', [] => []
  | S k', D :: rho' => D :: insert_candidate k' C rho'
  end.

Lemma nth_error_insert_candidate_lt : forall k C rho i,
  i < k -> nth_error (insert_candidate k C rho) i = nth_error rho i.
Proof.
  induction k as [|k IH]; intros C rho i Hi; [lia|].
  destruct rho as [|D rho']; simpl.
  - simpl. reflexivity.
  - destruct i; simpl; [reflexivity|]. apply IH. lia.
Qed.

Lemma nth_error_insert_candidate_eq : forall k C rho,
  k <= length rho ->
  nth_error (insert_candidate k C rho) k = Some C.
Proof.
  induction k as [|k IH]; intros C rho Hlen; simpl.
  - reflexivity.
  - destruct rho as [|D rho']; simpl in *; [lia|].
    change (nth_error (D :: insert_candidate k C rho') (S k) = Some C).
    simpl. apply IH. lia.
Qed.

Definition bound_agree (k : nat) (rho rho' : list (etm -> Prop)) : Prop :=
  forall i, i < k -> nth_error rho i = nth_error rho' i.

Lemma reducible_bound_irrelevant : forall T k rho rho' eta,
  lc_ty_at k T -> bound_agree k rho rho' ->
  forall t, reducible T rho eta t <-> reducible T rho' eta t.
Proof.
  induction T as [i|X|A IHA B IHB|B IHB|]; intros k rho rho' eta Hlc Hagree t; inversion Hlc; subst; simpl.
  - rewrite (Hagree i H1). destruct (nth_error rho i), (nth_error rho' i); simpl; tauto.
  - tauto.
  - split.
    + intros [HS [Hl Hfun]]. split; [exact HS|]. split; [exact Hl|]. intros u Hu.
      apply (proj1 (IHB k rho rho' eta ltac:(assumption) Hagree (e_app t u))).
      apply Hfun. apply (proj2 (IHA k rho rho' eta ltac:(assumption) Hagree u)). exact Hu.
    + intros [HS [Hl Hfun]]. split; [exact HS|]. split; [exact Hl|]. intros u Hu.
      apply (proj2 (IHB k rho rho' eta ltac:(assumption) Hagree (e_app t u))).
      apply Hfun. apply (proj1 (IHA k rho rho' eta ltac:(assumption) Hagree u)). exact Hu.
  - split.
    + intros [HS [Hl Hall]]. split; [exact HS|]. split; [exact Hl|]. intros C HC.
      apply (proj1 (IHB (S k) (C :: rho) (C :: rho') eta ltac:(assumption)
        ltac:(intros [|i] Hi; simpl; [reflexivity|apply Hagree; lia]) (e_tapp t))).
      apply Hall; exact HC.
    + intros [HS [Hl Hall]]. split; [exact HS|]. split; [exact Hl|]. intros C HC.
      apply (proj2 (IHB (S k) (C :: rho) (C :: rho') eta ltac:(assumption)
        ltac:(intros [|i] Hi; simpl; [reflexivity|apply Hagree; lia]) (e_tapp t))).
      apply Hall; exact HC.
  - tauto.
Qed.

Lemma reducible_closed_bound_irrelevant : forall T rho rho' eta,
  locally_closed_ty T -> forall t,
  reducible T rho eta t <-> reducible T rho' eta t.
Proof.
  intros T rho rho' eta HT t. eapply reducible_bound_irrelevant; eauto.
  intros i Hi. lia.
Qed.

Definition candidate_equiv (P Q : etm -> Prop) : Prop :=
  forall t, P t <-> Q t.
Inductive candidate_list_equiv : list (etm -> Prop) -> list (etm -> Prop) -> Prop :=
| cle_nil : candidate_list_equiv [] []
| cle_cons : forall P Q rho rho', candidate_equiv P Q ->
    candidate_list_equiv rho rho' -> candidate_list_equiv (P :: rho) (Q :: rho').

Lemma candidate_list_equiv_refl : forall rho, candidate_list_equiv rho rho.
Proof.
  induction rho as [|P rho IH]; [constructor|].
  apply cle_cons; [intro t; tauto|exact IH].
Qed.

Lemma candidate_lists_lookup : forall rho rho' i P,
  candidate_list_equiv rho rho' -> nth_error rho i = Some P ->
  exists Q, nth_error rho' i = Some Q /\ candidate_equiv P Q.
Proof.
  intros rho rho' i P Heq. revert i P.
  induction Heq; intros [|i] R Hnth; simpl in *; try discriminate.
  - inversion Hnth; subst. exists Q. split; [reflexivity|assumption].
  - eapply IHHeq; eassumption.
Qed.

Lemma candidate_lists_none : forall rho rho' i,
  candidate_list_equiv rho rho' -> nth_error rho i = None -> nth_error rho' i = None.
Proof.
  intros rho rho' i Heq. revert i.
  induction Heq; intros [|i] Hnth; simpl in *; try discriminate; auto.
Qed.

Lemma reducible_env_equiv : forall T rho rho' eta,
  candidate_list_equiv rho rho' -> forall t,
  reducible T rho eta t <-> reducible T rho' eta t.
Proof.
  induction T as [i|X|A IHA B IHB|B IHB|]; intros rho rho' eta Henv t; simpl.
  - destruct (nth_error rho i) as [P|] eqn:EP.
    + destruct (candidate_lists_lookup _ _ _ _ Henv EP) as [Q [EQ HEQ]].
      rewrite EQ. apply HEQ.
    + rewrite (candidate_lists_none _ _ _ Henv EP). tauto.
  - tauto.
  - split.
    + intros [HS [Hl HF]]. split; [exact HS|]. split; [exact Hl|]. intros u HU.
      apply (proj1 (IHB rho rho' eta Henv (e_app t u))).
      apply HF. apply (proj2 (IHA rho rho' eta Henv u)). exact HU.
    + intros [HS [Hl HF]]. split; [exact HS|]. split; [exact Hl|]. intros u HU.
      apply (proj2 (IHB rho rho' eta Henv (e_app t u))).
      apply HF. apply (proj1 (IHA rho rho' eta Henv u)). exact HU.
  - split.
    + intros [HS [Hl HF]]. split; [exact HS|]. split; [exact Hl|]. intros C HC.
      apply (proj1 (IHB (C :: rho) (C :: rho') eta
        (cle_cons C C rho rho' (fun z => iff_refl (C z)) Henv) (e_tapp t))).
      apply HF; exact HC.
    + intros [HS [Hl HF]]. split; [exact HS|]. split; [exact Hl|]. intros C HC.
      apply (proj2 (IHB (C :: rho) (C :: rho') eta
        (cle_cons C C rho rho' (fun z => iff_refl (C z)) Henv) (e_tapp t))).
      apply HF; exact HC.
  - tauto.
Qed.

Lemma candidate_insert_equiv : forall k C C' rho,
  candidate_equiv C C' ->
  candidate_list_equiv (insert_candidate k C rho) (insert_candidate k C' rho).
Proof.
  induction k as [|k IH]; intros C C' rho Heq; simpl.
  - apply cle_cons; [exact Heq|apply candidate_list_equiv_refl].
  - destruct rho as [|D rho']; simpl; [constructor|].
    apply cle_cons; [intro t; tauto|]. apply IH; exact Heq.
Qed.

Lemma reducible_open_ty_rec : forall T k rho eta U,
  k <= length rho -> locally_closed_ty U -> lc_ty_at (S k) T ->
  forall t,
    reducible (open_ty_rec k U T) rho eta t <->
    reducible T (insert_candidate k (reducible U rho eta) rho) eta t.
Proof.
  induction T as [i|X|A IHA B IHB|B IHB|]; intros k rho eta U Hlen HU HT t;
    inversion HT; subst; simpl.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst i.
      rewrite nth_error_insert_candidate_eq by lia. simpl. tauto.
    + apply Nat.eqb_neq in E.
      assert (Hi : i < k) by lia.
      rewrite nth_error_insert_candidate_lt by exact Hi.
      destruct (nth_error rho i) as [P|] eqn:E2; simpl; rewrite E2; tauto.
  - tauto.
  - split.
    + intros [HS [Hl HF]]. split; [exact HS|]. split; [exact Hl|]. intros u Hu.
      apply (proj1 (IHB k rho eta U Hlen HU ltac:(assumption) (e_app t u))).
      apply HF. apply (proj2 (IHA k rho eta U Hlen HU ltac:(assumption) u)). exact Hu.
    + intros [HS [Hl HF]]. split; [exact HS|]. split; [exact Hl|]. intros u Hu.
      apply (proj2 (IHB k rho eta U Hlen HU ltac:(assumption) (e_app t u))).
      apply HF. apply (proj1 (IHA k rho eta U Hlen HU ltac:(assumption) u)). exact Hu.
  - split.
    + intros [HS [Hl HF]]. split; [exact HS|]. split; [exact Hl|]. intros C HC.
      assert (HE : candidate_list_equiv
        (insert_candidate (S k) (reducible U (C :: rho) eta) (C :: rho))
        (C :: insert_candidate k (reducible U rho eta) rho)).
      { simpl. apply cle_cons.
        - intro z. tauto.
        - apply candidate_insert_equiv. intro z.
          exact (@reducible_closed_bound_irrelevant U (C :: rho) rho eta HU z).
      }
      apply (proj1 (reducible_env_equiv B
        (insert_candidate (S k) (reducible U (C :: rho) eta) (C :: rho))
        (C :: insert_candidate k (reducible U rho eta) rho) eta HE (e_tapp t))).
      apply (proj1 (IHB (S k) (C :: rho) eta U ltac:(simpl; lia) HU ltac:(assumption) (e_tapp t))).
      apply HF; exact HC.
    + intros [HS [Hl HF]]. split; [exact HS|]. split; [exact Hl|]. intros C HC.
      assert (HE : candidate_list_equiv
        (insert_candidate (S k) (reducible U (C :: rho) eta) (C :: rho))
        (C :: insert_candidate k (reducible U rho eta) rho)).
      { simpl. apply cle_cons.
        - intro z. tauto.
        - apply candidate_insert_equiv. intro z.
          exact (@reducible_closed_bound_irrelevant U (C :: rho) rho eta HU z).
      }
      apply (proj2 (IHB (S k) (C :: rho) eta U ltac:(simpl; lia) HU ltac:(assumption) (e_tapp t))).
      apply (proj2 (reducible_env_equiv B
        (insert_candidate (S k) (reducible U (C :: rho) eta) (C :: rho))
        (C :: insert_candidate k (reducible U rho eta) rho) eta HE (e_tapp t))).
      apply HF; exact HC.
  - tauto.
Qed.

Fixpoint efv (t : etm) : list atom :=
  match t with
  | e_bvar _ => [] | e_fvar x => [x]
  | e_abs b | e_tabs b => efv b
  | e_app a b | e_choice a b => efv a ++ efv b
  | e_tapp a | e_succ a => efv a
  | e_zero => []
  | e_natrec n b s => efv n ++ efv b ++ efv s
  end.

Fixpoint esubst_env (sigma : atom -> etm) (t : etm) : etm :=
  match t with
  | e_bvar i => e_bvar i | e_fvar x => sigma x
  | e_abs b => e_abs (esubst_env sigma b)
  | e_app a b => e_app (esubst_env sigma a) (esubst_env sigma b)
  | e_tabs b => e_tabs (esubst_env sigma b)
  | e_tapp a => e_tapp (esubst_env sigma a)
  | e_zero => e_zero | e_succ a => e_succ (esubst_env sigma a)
  | e_natrec n b s => e_natrec (esubst_env sigma n) (esubst_env sigma b) (esubst_env sigma s)
  | e_choice a b => e_choice (esubst_env sigma a) (esubst_env sigma b)
  end.

Definition esubst_env_update (sigma : atom -> etm) (x : atom) (u : etm) :=
  fun y => if Nat.eqb x y then u else sigma y.

Lemma efv_erase : forall t, efv (erase t) = fv_tm t.
Proof. induction t; simpl; rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3; reflexivity. Qed.

Lemma esubst_env_open_rec_update : forall t k sigma x u,
  (forall y, elc (sigma y)) ->
  ~ In x (efv t) ->
  esubst_env (esubst_env_update sigma x u) (eopen_rec k (e_fvar x) t) =
  eopen_rec k u (esubst_env sigma t).
Proof.
  induction t; intros k sigma x u Hclosed Hfresh; simpl in *.
  - destruct (Nat.eqb k n); simpl.
    + unfold esubst_env_update. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - unfold esubst_env_update. destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E. subst a. exfalso. apply Hfresh. simpl; auto.
    + rewrite (eopen_rec_lc_identity (sigma a) k u).
      * reflexivity.
      * eapply elc_at_mono; [apply Hclosed|lia].
  - f_equal. apply IHt; auto.
  - f_equal; [apply IHt1|apply IHt2]; try assumption; simpl in Hfresh; intro Hin; apply Hfresh; apply in_or_app; auto.
  - f_equal. apply IHt; auto.
  - f_equal. apply IHt; auto.
  - reflexivity.
  - f_equal. apply IHt; auto.
  - f_equal.
    + apply IHt1; auto. simpl in Hfresh. intro Hin. apply Hfresh. apply in_or_app. left; exact Hin.
    + apply IHt2; auto. simpl in Hfresh. intro Hin. apply Hfresh. apply in_or_app. right. apply in_or_app. left; exact Hin.
    + apply IHt3; auto. simpl in Hfresh. intro Hin. apply Hfresh. apply in_or_app. right. apply in_or_app. right; exact Hin.
  - f_equal; [apply IHt1|apply IHt2]; try assumption; simpl in Hfresh; intro Hin; apply Hfresh; apply in_or_app; auto.
Qed.

Lemma erase_choice_erased : forall t1 t2,
  erase (tm_choice t1 t2) = e_choice (erase t1) (erase t2).
Proof. reflexivity. Qed.

Definition term_env_related (rho : list (etm -> Prop)) (eta : atom -> etm -> Prop)
    (Gamma : context) (sigma : atom -> etm) : Prop :=
  forall x T, lookup_context x Gamma = Some T -> reducible T rho eta (sigma x).

Lemma term_env_related_update : forall rho eta Gamma sigma x T u,
  term_env_related rho eta Gamma sigma -> reducible T rho eta u ->
  term_env_related rho eta (update Gamma x T) (esubst_env_update sigma x u).
Proof.
  intros rho eta Gamma sigma x T u Henv Hu y A Hlookup.
  unfold update in Hlookup. simpl in Hlookup.
  destruct (Nat.eqb y x) eqn:E.
  - inversion Hlookup; subst. unfold esubst_env_update. rewrite Nat.eqb_sym, E. exact Hu.
  - unfold esubst_env_update. rewrite Nat.eqb_sym, E.
    apply Henv with (1 := Hlookup).
Qed.

Lemma lookup_fv_context : forall Gamma x T X,
  lookup_context x Gamma = Some T -> In X (fv_ty T) -> In X (ftv_context Gamma).
Proof.
  induction Gamma as [|[y A] Gamma IH]; intros x T X Hlookup Hin; simpl in *; try discriminate.
  destruct (Nat.eqb x y) eqn:E.
  - inversion Hlookup; subst. apply in_or_app. left; exact Hin.
  - apply in_or_app. right. eapply IH; eauto.
Qed.

Definition eta_update (eta : atom -> etm -> Prop) (X : atom) (C : etm -> Prop) :=
  fun Y => if Nat.eqb X Y then C else eta Y.

Lemma reducible_eta_update : forall T rho eta X C,
  ~ In X (fv_ty T) -> forall t,
  reducible T rho eta t <-> reducible T rho (eta_update eta X C) t.
Proof.
  induction T as [i|Y|A IHA B IHB|B IHB|]; intros rho eta X C Hfresh t; simpl in *.
  - tauto.
  - destruct (Nat.eqb X Y) eqn:E.
    + apply Nat.eqb_eq in E. subst Y. exfalso. apply Hfresh. simpl; auto.
    + unfold eta_update. rewrite E. tauto.
  - assert (Hfa : ~ In X (fv_ty A)).
    { intro Hin. apply Hfresh. apply in_or_app; left; exact Hin. }
    assert (Hfb : ~ In X (fv_ty B)).
    { intro Hin. apply Hfresh. apply in_or_app; right; exact Hin. }
    split.
    + intros [HS [Hl HF]]. split; [exact HS|]. split; [exact Hl|]. intros u Hu.
      apply (proj1 (IHB rho eta X C Hfb (e_app t u))). apply HF.
      apply (proj2 (IHA rho eta X C Hfa u)). exact Hu.
    + intros [HS [Hl HF]]. split; [exact HS|]. split; [exact Hl|]. intros u Hu.
      apply (proj2 (IHB rho eta X C Hfb (e_app t u))). apply HF.
      apply (proj1 (IHA rho eta X C Hfa u)). exact Hu.
  - split.
    + intros [HS [Hl Hall]]. split; [exact HS|]. split; [exact Hl|]. intros D HD.
      apply (proj1 (IHB (D :: rho) eta X C Hfresh (e_tapp t))). apply Hall; exact HD.
    + intros [HS [Hl Hall]]. split; [exact HS|]. split; [exact Hl|]. intros D HD.
      apply (proj2 (IHB (D :: rho) eta X C Hfresh (e_tapp t))). apply Hall; exact HD.
  - tauto.
Qed.

Definition env_candidates_ok (rho : list (etm -> Prop)) (eta : atom -> etm -> Prop) : Prop :=
  Forall candidate_ok rho /\ forall X, candidate_ok (eta X).

Lemma forall_nth_candidate : forall rho n P,
  Forall candidate_ok rho -> nth_error rho n = Some P -> candidate_ok P.
Proof.
  induction rho as [|Q rho IH]; intros [|n] P Hall Hnth; simpl in Hnth.
  - discriminate.
  - discriminate.
  - inversion Hall as [|q l Hq Hl]; subst.
    inversion Hnth; subst. exact Hq.
  - inversion Hall; subst. eapply IH; eassumption.
Qed.

Lemma reducible_candidate_ok : forall T rho eta,
  env_candidates_ok rho eta -> candidate_ok (reducible T rho eta).
Proof.
  induction T as [i|X|A IHA B IHB|B IHB|]; intros rho eta Henv; simpl.
  - destruct (nth_error rho i) as [P|] eqn:E.
    + destruct Henv as [Hr _]. eapply forall_nth_candidate; eassumption.
    + exact sn_candidate_ok.
  - destruct Henv as [_ He]. apply He.
  - destruct Henv as [Hr He].
    pose proof (IHA rho eta (conj Hr He)) as HA.
    pose proof (IHB rho eta (conj Hr He)) as HB.
    destruct HA as [HAS [HAL [HAstep HAneu]]].
    destruct HB as [HBS [HBL [HBstep HBneu]]].
    split.
    + intros t [Ht _]. exact Ht.
    + split.
      * intros t [Ht [Hlc Hfun]]. exact Hlc.
      * split.
        -- intros t u [Ht [Hlc Hfun]] Hstep. split.
           ++ eapply esn_step_inv; eauto.
           ++ split.
              ** eapply estep_preserves_elc; eauto.
              ** intros v Hv. apply HBstep with (t := e_app t v).
                 --- apply Hfun; exact Hv.
                 --- eapply ES_App1; eauto.
        -- intros t Hlc Hneutral Hsteps.
           split.
           ++ apply esn_intro. intros u Hu. destruct (Hsteps u Hu) as [Hs _]. exact Hs.
           ++ split; [exact Hlc|]. intros v HvA.
              assert (HvSN : esn v) by (apply HAS; exact HvA).
              revert HvA. induction HvSN as [v Hvred IHv]; intros HvA.
              apply HBneu.
              ** apply elc_app; [exact Hlc|exact (HAL v HvA)].
              ** constructor.
              ** intros z Hz. inversion Hz; subst.
                 --- exfalso. apply (eneutral_not_value _ Hneutral). constructor.
                 --- destruct (Hsteps _ H2) as [_ [_ Hfun]]. apply Hfun. exact HvA.
                 --- exfalso. apply (eneutral_not_value _ Hneutral). assumption.
  - destruct Henv as [Hr He].
    split.
    + intros t [Ht _]. exact Ht.
    + split.
      * intros t [Ht [Hlc Hall]]. exact Hlc.
      * split.
        -- intros t u [Ht [Hlc Hall]] Hstep. split.
           ++ eapply esn_step_inv; eauto.
           ++ split.
              ** eapply estep_preserves_elc; eauto.
              ** intros C HC.
                 pose proof (IHB (C :: rho) eta (conj (@Forall_cons (etm -> Prop) candidate_ok C rho HC Hr) He)) as HBC.
                 destruct HBC as [_ [_ [HBCstep _]]].
                 apply HBCstep with (t := e_tapp t).
                 --- apply Hall; exact HC.
                 --- eapply ES_TApp; eassumption.
        -- intros t Hlc Hneutral Hsteps.
           split.
           ++ apply esn_intro. intros u Hu. destruct (Hsteps u Hu) as [Hs _]. exact Hs.
           ++ split; [exact Hlc|]. intros C HC.
              pose proof (IHB (C :: rho) eta (conj (@Forall_cons (etm -> Prop) candidate_ok C rho HC Hr) He)) as HBC.
              destruct HBC as [_ [_ [_ HBCneu]]].
              apply HBCneu.
              ** apply elc_tapp; exact Hlc.
              ** constructor.
              ** intros z Hz. inversion Hz; subst.
                 --- exfalso. apply (eneutral_not_value _ Hneutral). constructor.
                 --- match goal with
                     | Hred : estep ?root ?u |- _ =>
                         destruct (Hsteps u Hred) as [_ [_ Hall]]; apply Hall; exact HC
                     end.
  - destruct Henv as [Hr He].
    split.
    + intros t [Ht _]. exact Ht.
    + split.
      * intros t [_ [Hlc _]]. exact Hlc.
      * split.
        -- intros t u [Ht [Hlc Hend]] Hstep. split.
           ++ eapply esn_step_inv; eauto.
           ++ split.
              ** eapply estep_preserves_elc; eauto.
              ** intros v Hmulti Hv. apply Hend with (v := v).
                 --- inversion Hmulti; subst; econstructor; eauto.
                 --- exact Hv.
        -- intros t Hlc Hneutral Hsteps.
           split.
           ++ apply esn_intro. intros u Hu. destruct (Hsteps u Hu) as [Hs _]. exact Hs.
           ++ split; [exact Hlc|]. intros v Hmulti Hv.
              destruct (emulti_step_inv _ _ Hmulti) as [Heq|[u [Hu Huv]]].
              ** subst. exfalso. apply (eneutral_not_value _ Hneutral). exact Hv.
              ** destruct (Hsteps u Hu) as [_ [_ Hend]]. eapply Hend; eauto.
Qed.

Lemma env_candidates_ok_eta_update : forall rho eta X C,
  env_candidates_ok rho eta -> candidate_ok C ->
  env_candidates_ok rho (eta_update eta X C).
Proof.
  intros rho eta X C [Hr He] HC. split; [exact Hr|]. intros Y.
  unfold eta_update. destruct (Nat.eqb X Y); [exact HC|apply He].
Qed.

Lemma term_env_related_eta_update : forall rho eta Gamma sigma X C,
  term_env_related rho eta Gamma sigma ->
  ~ In X (ftv_context Gamma) ->
  term_env_related rho (eta_update eta X C) Gamma sigma.
Proof.
  intros rho eta Gamma sigma X C Hrel Hfresh y T Hlookup.
  assert (Hft : ~ In X (fv_ty T)).
  { intro Hin. apply Hfresh. eapply lookup_fv_context; eassumption. }
  apply (proj1 (reducible_eta_update T rho eta X C Hft (sigma y))).
  apply Hrel with (1 := Hlookup).
Qed.

Lemma erase_lc_tm_at : forall K k t,
  lc_tm_at K k t -> elc_at k (erase t).
Proof.
  intros K k t Hlc. induction Hlc; simpl.
  - constructor; assumption.
  - constructor.
  - constructor. exact IHHlc.
  - constructor; assumption.
  - constructor. exact IHHlc.
  - constructor; assumption.
  - constructor.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
Qed.

Lemma esubst_env_elc_at : forall k t sigma,
  elc_at k t -> (forall x, elc (sigma x)) -> elc_at k (esubst_env sigma t).
Proof.
  intros k t. revert k. induction t; intros k sigma Hlc Hsigma; simpl in *.
  - inversion Hlc; subst. constructor; assumption.
  - eapply elc_at_mono; [apply Hsigma|lia].
  - inversion Hlc; subst. constructor. apply IHt with (k := S k); assumption.
  - inversion Hlc; subst. constructor; [eapply IHt1|eapply IHt2]; eassumption.
  - inversion Hlc; subst. constructor. apply IHt with (k := k); assumption.
  - inversion Hlc; subst. constructor. apply IHt with (k := k); assumption.
  - constructor.
  - inversion Hlc; subst. constructor. eapply IHt; eassumption.
  - inversion Hlc; subst. constructor; [eapply IHt1|eapply IHt2|eapply IHt3]; eassumption.
  - inversion Hlc; subst. constructor; [eapply IHt1|eapply IHt2]; eassumption.
Qed.

Lemma elc_at_eopen_inv : forall t k x,
  elc_at k (eopen_rec k (e_fvar x) t) -> elc_at (S k) t.
Proof.
  induction t; intros k x Hlc; simpl in Hlc.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. apply elc_bvar. lia.
    + inversion Hlc; subst. apply elc_bvar. lia.
  - apply elc_fvar.
  - inversion Hlc; subst. apply elc_abs. eapply IHt; eauto.
  - inversion Hlc; subst. apply elc_app; eauto.
  - inversion Hlc; subst. apply elc_tabs. eapply IHt; eauto.
  - inversion Hlc; subst. apply elc_tapp. eapply IHt; eauto.
  - constructor.
  - inversion Hlc; subst. apply elc_succ. eapply IHt; eauto.
  - inversion Hlc; subst. apply elc_natrec; eauto.
  - inversion Hlc; subst. apply elc_choice; eauto.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T Hwf. induction Hwf.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; assumption.
  - apply lc_ty_all. specialize (H0 (fresh L) (fresh_notin L)).
    unfold locally_closed_ty in H0. unfold open_ty in H0.
    eapply lc_ty_at_open_inv; exact H0.
  - apply lc_ty_nat.
Qed.

Lemma has_type_erased_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> elc (erase t).
Proof.
  intros Delta Gamma t T Hty.
  induction Hty as
    [Delta Gamma x T Hlookup Hwf
    |L Delta Gamma T1 body T2 Hwf Hbody IHbody
    |Delta Gamma a b T1 T2 IHa IHb
    |L Delta Gamma body T Hbody IHbody
    |Delta Gamma a U T Habs IHabs Hwf
    |Delta Gamma
    |Delta Gamma n IHn
    |Delta Gamma n b s T IHn IHb IHs
    |Delta Gamma a b T IHa IHb].
  - simpl. constructor.
  - simpl. apply elc_abs. specialize (IHbody (fresh L) (fresh_notin L)).
    rewrite erase_open in IHbody. eapply elc_at_eopen_inv; exact IHbody.
  - simpl. apply elc_app; assumption.
  - simpl. apply elc_tabs. specialize (IHbody (fresh L) (fresh_notin L)).
    rewrite erase_open_tm_ty in IHbody. exact IHbody.
  - simpl. apply elc_tapp. assumption.
  - simpl. constructor.
  - simpl. apply elc_succ. assumption.
  - simpl. apply elc_natrec; assumption.
  - simpl. apply elc_choice; assumption.
Qed.

Lemma has_type_lc_ty : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_ty T.
Proof.
  intros Delta Gamma t T Hty. induction Hty.
  - eapply wf_ty_lc; eassumption.
  - apply lc_ty_arrow; [eapply wf_ty_lc; eassumption|].
    match goal with
    | Hlc : forall x, ~ In x L -> locally_closed_ty T2 |- _ =>
        exact (Hlc (fresh L) (fresh_notin L))
    end.
  - match goal with
    | Hlc : locally_closed_ty (Ty_Arrow _ _) |- _ => inversion Hlc; assumption
    end.
  - apply lc_ty_all.
    match goal with
    | Hlc : forall X, ~ In X L -> locally_closed_ty (open_ty ?B (Ty_FVar X)) |- _ =>
        specialize (Hlc (fresh L) (fresh_notin L));
        unfold locally_closed_ty in Hlc; unfold open_ty in Hlc;
        eapply lc_ty_at_open_inv; exact Hlc
    end.
  - unfold locally_closed_ty. unfold open_ty.
    apply lc_ty_at_open; [|eapply wf_ty_lc; eassumption].
    match goal with
    | Hlc : locally_closed_ty (Ty_All _) |- _ => inversion Hlc; assumption
    end.
  - apply lc_ty_nat.
  - apply lc_ty_nat.
  - exact IHHty2.
  - assumption.
Qed.





Lemma enumeric_ends_numeric : forall n, enumeric n -> ends_numeric n.
Proof.
  intros n Hn v Hmulti Hv. induction Hmulti.
  - exact Hn.
  - exfalso. eapply enumeric_no_step; eauto.
Qed.

Lemma esn_succ : forall n, esn n -> esn (e_succ n).
Proof.
  intros n Hn. induction Hn as [n Hnext IH]. constructor. intros u Hu.
  inversion Hu; subst. eapply IH; eassumption.
Qed.

Lemma emulti_succ_inv : forall n v, emulti (e_succ n) v ->
  exists m, emulti n m /\ v = e_succ m.
Proof.
  intros n v H. remember (e_succ n) as root eqn:E. revert n E.
  induction H; intros n0 E; inversion E; subst.
  - exists n0. split; [apply em_refl|reflexivity].
  - inversion H; subst.
    destruct (IHemulti a' eq_refl) as [m [Hm ->]].
    exists m. split; [eapply em_step; [eassumption|exact Hm]|reflexivity].
Qed.

Lemma reducible_numeric : forall rho eta n,
  env_candidates_ok rho eta -> enumeric n -> reducible Ty_Nat rho eta n.
Proof.
  intros rho eta n _ Hn. change (esn n /\ elc n /\ ends_numeric n). split.
  - constructor. intros u Hu. exfalso. eapply enumeric_no_step; eauto.
  - split.
    + eapply enumeric_elc; eassumption.
    + apply enumeric_ends_numeric; assumption.
Qed.

Lemma reducible_succ : forall rho eta n,
  reducible Ty_Nat rho eta n -> reducible Ty_Nat rho eta (e_succ n).
Proof.
  intros rho eta n [Hsn [Hlc Hend]]. change (esn (e_succ n) /\ elc (e_succ n) /\ ends_numeric (e_succ n)). split.
  - apply esn_succ; exact Hsn.
  - split.
    + apply elc_succ; exact Hlc.
    + intros v Hmulti Hv.
      destruct (emulti_succ_inv _ _ Hmulti) as [m [Hm ->]].
      inversion Hv; subst. exact H.
Qed.

Lemma reducible_natrec_numeric : forall rho eta T n,
  env_candidates_ok rho eta -> enumeric n ->
  forall b s,
    reducible T rho eta b ->
    reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) rho eta s ->
    evalue b -> evalue s ->
    reducible T rho eta (e_natrec n b s).
Proof.
  intros rho eta T n Henv Hnum. induction Hnum; intros b s Hb Hs Hvb Hvs.
  - destruct Hs as [Hssn [Hslc Hsf]].
    destruct (reducible_candidate_ok T rho eta Henv) as [HsnP [HlcP [HstepP HneutralP]]].
    apply HneutralP.
    + apply elc_natrec.
      * apply elc_zero.
      * destruct (reducible_candidate_ok T rho eta Henv) as [_ [Hlb _]]. eapply Hlb; eassumption.
      * exact Hslc.
    + apply en_natrec.
    + intros z Hz. inversion Hz; subst.
      * exfalso. match goal with Hred : estep e_zero ?q |- _ => exact (enumeric_no_step e_zero en_zero q Hred) end.
      * exfalso. match goal with Hred : estep b ?q |- _ => exact (evalue_no_step b Hvb q Hred) end.
      * exfalso. match goal with Hred : estep s ?q |- _ => exact (evalue_no_step s Hvs q Hred) end.
      * exact Hb.
  - destruct Hs as [Hssn [Hslc Hsf]].
    destruct (reducible_candidate_ok T rho eta Henv) as [HsnP [HlcP [HstepP HneutralP]]].
    apply HneutralP.
    + apply elc_natrec.
      * apply elc_succ. eapply enumeric_elc; eassumption.
      * destruct (reducible_candidate_ok T rho eta Henv) as [_ [Hlb _]]. eapply Hlb; eassumption.
      * exact Hslc.
    + apply en_natrec.
    + intros z Hz. inversion Hz; subst.
      * exfalso. match goal with Hred : estep (e_succ n) ?q |- _ => exact (enumeric_no_step (e_succ n) (en_succ n Hnum) q Hred) end.
      * exfalso. match goal with Hred : estep b ?q |- _ => exact (evalue_no_step b Hvb q Hred) end.
      * exfalso. match goal with Hred : estep s ?q |- _ => exact (evalue_no_step s Hvs q Hred) end.
      * pose proof (reducible_numeric rho eta n Henv Hnum) as Hrn.
        pose proof (Hsf n Hrn) as Hsnapp.
        destruct Hsnapp as [_ [_ Hsnfun]].
        apply Hsnfun.
        apply IHHnum.
        -- exact Hb.
        -- split; [exact Hssn|]. split; assumption.
        -- exact Hvb.
        -- exact Hvs.
Qed.

Lemma reducible_natrec_general : forall rho eta T n b s,
  env_candidates_ok rho eta ->
  reducible Ty_Nat rho eta n ->
  reducible T rho eta b ->
  reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) rho eta s ->
  reducible T rho eta (e_natrec n b s).
Proof.
  intros rho eta T n b s Henv Hn Hb Hs.
  destruct (reducible_candidate_ok Ty_Nat rho eta Henv) as [HsnN [HlcN [HstepN _]]].
  destruct (reducible_candidate_ok T rho eta Henv) as [HsnT [HlcT [HstepT HneutralT]]].
  destruct (reducible_candidate_ok (Ty_Arrow Ty_Nat (Ty_Arrow T T)) rho eta Henv)
    as [HsnS [HlcS [HstepS _]]].
  assert (Gn : forall n, esn n -> forall b s,
      reducible Ty_Nat rho eta n -> reducible T rho eta b ->
      reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) rho eta s ->
      reducible T rho eta (e_natrec n b s)).
  { intros ncur HsnproofN. induction HsnproofN as [ncur HnextN IHn].
    intros bcur scur Hnrel Hbrel Hsrel.
    assert (Gb : forall b, esn b -> forall s,
        reducible Ty_Nat rho eta ncur -> reducible T rho eta b ->
        reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) rho eta s ->
        reducible T rho eta (e_natrec ncur b s)).
    { intros bnext HsnproofB. induction HsnproofB as [bnext HnextB IHb].
      intros snext HnrelB HbrelB HsrelB.
      assert (Gs : forall s, esn s ->
          reducible Ty_Nat rho eta ncur -> reducible T rho eta bnext ->
          reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) rho eta s ->
          reducible T rho eta (e_natrec ncur bnext s)).
      { intros sfinal HsnproofS. induction HsnproofS as [sfinal HnextS IHs].
        intros HnrelC HbrelC HsrelC.
        destruct (reducible_candidate_ok T rho eta Henv)
          as [HsnP [HlcP [HstepP HneutralP]]].
        apply HneutralP.
        - apply elc_natrec; [eapply HlcN; exact HnrelC|eapply HlcT; exact HbrelC|eapply HlcS; exact HsrelC].
        - apply en_natrec.
        - intros z Hz. inversion Hz; subst.
          + match goal with
            | Hr : estep ncur ?n' |- _ =>
                apply (IHn n' Hr);
                [eapply HstepN; eassumption|exact HbrelC|exact HsrelC]
            end.
          + match goal with
            | Hr : estep bnext ?b' |- _ =>
                apply (IHb b' Hr);
                [exact HnrelC|eapply HstepT; eassumption|exact HsrelC]
            end.
          + match goal with
            | Hr : estep sfinal ?s' |- _ =>
                apply (IHs s' Hr);
                [exact HnrelC|exact HbrelC|eapply HstepS; eassumption]
            end.
          + exact HbrelC.
          + match goal with
            | Hnum : enumeric ?np, HvalueB : evalue bnext,
              HvalueS : evalue sfinal |- _ =>
                pose proof (reducible_numeric rho eta np Henv Hnum) as Hrn;
                pose proof (reducible_natrec_numeric rho eta T np Henv Hnum
                  bnext sfinal HbrelC HsrelC HvalueB HvalueS) as Hrec;
                destruct HsrelC as [_ [_ Hsf]];
                pose proof (Hsf np Hrn) as Happ;
                destruct Happ as [_ [_ Hfun]];
                apply Hfun; exact Hrec
            end.
      }
      apply (Gs snext (HsnS snext HsrelB) HnrelB HbrelB HsrelB).
    }
    apply (Gb bcur (HsnT bcur Hbrel) scur Hnrel Hbrel Hsrel).
  }
  apply (Gn n (HsnN n Hn) b s Hn Hb Hs).
Qed.

Lemma fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall rho eta sigma,
    env_candidates_ok rho eta ->
    term_env_related rho eta Gamma sigma ->
    (forall x, elc (sigma x)) ->
    reducible T rho eta (esubst_env sigma (erase t)).
Proof.
  intros Delta Gamma t T Htyping.
  induction Htyping as
    [Delta Gamma x T Hlookup Hwf
    |L Delta Gamma T1 body T2 Hwf Hbody IHbody
    |Delta Gamma a b T1 T2 HtyA HtyB IHA IHB
    |L Delta Gamma body T Hbody IHbody
    |Delta Gamma a T U Hty IHty HwfU
    |Delta Gamma
    |Delta Gamma n Hty IHty
    |Delta Gamma n b s T HtyN HtyB HtyS IHN IHB IHS
    |Delta Gamma a b T HtyA HtyB IHA IHB];
    intros rho eta sigma Henv Hterms Hsigma.
  - simpl. eapply Hterms; eassumption.
  - pose proof (has_type_erased_lc _ _ _ _ (T_Abs L Delta Gamma T1 body T2 Hwf Hbody)) as Hsrc.
    assert (Habs : elc (e_abs (esubst_env sigma (erase body)))).
    { change (elc (esubst_env sigma (erase (tm_abs T1 body)))).
      eapply esubst_env_elc_at; eauto. }
    change (esn (e_abs (esubst_env sigma (erase body))) /\
      elc (e_abs (esubst_env sigma (erase body))) /\
      (forall u, reducible T1 rho eta u ->
        reducible T2 rho eta (e_app (e_abs (esubst_env sigma (erase body))) u))).
    split.
    + constructor. intros u Hu. inversion Hu.
    + split; [exact Habs|]. intros u Hu.
      destruct (reducible_candidate_ok T2 rho eta Henv) as [_ [_ [_ HneutralT2]]].
      destruct (reducible_candidate_ok T1 rho eta Henv) as [HsnT1 [HlcT1 [HstepT1 _]]].
      assert (HsnU : esn u) by (eapply HsnT1; exact Hu).
      revert Hu. induction HsnU as [u HnextU IHu]; intros Hu.
      apply HneutralT2.
      * apply elc_app; [exact Habs|eapply HlcT1; exact Hu].
      * apply en_app.
      * intros v Huv. inversion Huv; subst.
        -- assert (HxL : ~ In (fresh (L ++ fv_tm body)) L).
           { intro Hin. apply (fresh_notin (L ++ fv_tm body)). apply in_or_app; left; exact Hin. }
           assert (HxFV : ~ In (fresh (L ++ fv_tm body)) (fv_tm body)).
           { intro Hin. apply (fresh_notin (L ++ fv_tm body)). apply in_or_app; right; exact Hin. }
           assert (Hrel' : term_env_related rho eta (update Gamma (fresh (L ++ fv_tm body)) T1)
                  (esubst_env_update sigma (fresh (L ++ fv_tm body)) u)).
           { eapply term_env_related_update; eauto. }
           assert (Hsigma' : forall y, elc (esubst_env_update sigma (fresh (L ++ fv_tm body)) u y)).
           { intros y. unfold esubst_env_update. destruct (Nat.eqb (fresh (L ++ fv_tm body)) y).
             - eapply HlcT1; exact Hu.
             - apply Hsigma. }
           pose proof (IHbody (fresh (L ++ fv_tm body)) HxL rho eta
             (esubst_env_update sigma (fresh (L ++ fv_tm body)) u)
             Henv Hrel' Hsigma') as Hbeta.
           rewrite erase_open in Hbeta.
           unfold eopen in Hbeta.
           change (reducible T2 rho eta
             (esubst_env (esubst_env_update sigma (fresh (L ++ fv_tm body)) u)
               (eopen_rec 0 (e_fvar (fresh (L ++ fv_tm body))) (erase body)))) in Hbeta.
           rewrite (esubst_env_open_rec_update (erase body) 0 sigma
             (fresh (L ++ fv_tm body)) u Hsigma) in Hbeta.
           2: { rewrite efv_erase. exact HxFV. }
           exact Hbeta.
        -- exfalso. match goal with Hred : estep (e_abs _) _ |- _ => inversion Hred end.
        -- eapply IHu; [eassumption|].
           eapply HstepT1; eassumption.
  - simpl.
    destruct (HtyB rho eta sigma Henv Hterms Hsigma) as [_ [_ Hfun]].
    apply Hfun. eapply IHB; eassumption.
  - pose proof (has_type_erased_lc _ _ _ _ (T_TAbs L Delta Gamma body T Hbody)) as Hsrc.
    pose proof (has_type_lc_ty _ _ _ _ (T_TAbs L Delta Gamma body T Hbody)) as HTall.
    inversion HTall as [| | |HTbody|]; subst.
    assert (Htabs : elc (e_tabs (esubst_env sigma (erase body)))).
    { change (elc (esubst_env sigma (erase (tm_tabs body)))).
      eapply esubst_env_elc_at; eauto. }
    change (esn (e_tabs (esubst_env sigma (erase body))) /\
      elc (e_tabs (esubst_env sigma (erase body))) /\
      (forall C, candidate_ok C ->
        reducible T (C :: rho) eta (e_tapp (e_tabs (esubst_env sigma (erase body)))))).
    split.
    + constructor. intros u Hu. inversion Hu.
    + split; [exact Htabs|]. intros C HC.
      set (X := fresh (L ++ ftv_context Gamma ++ fv_ty T)).
      assert (HXnot : ~ In X L).
      { unfold X. intro Hin. apply (fresh_notin (L ++ ftv_context Gamma ++ fv_ty T)).
        apply in_or_app; left; exact Hin. }
      assert (HXctx : ~ In X (ftv_context Gamma)).
      { unfold X. intro Hin. apply (fresh_notin (L ++ ftv_context Gamma ++ fv_ty T)).
        apply in_or_app; right. apply in_or_app; left; exact Hin. }
      assert (HXty : ~ In X (fv_ty T)).
      { unfold X. intro Hin. apply (fresh_notin (L ++ ftv_context Gamma ++ fv_ty T)).
        apply in_or_app; right. apply in_or_app; right; exact Hin. }
      set (eta' := eta_update eta X C).
      assert (Henv' : env_candidates_ok rho eta')
        by (eapply env_candidates_ok_eta_update; eauto).
      assert (Hterms' : term_env_related rho eta' Gamma sigma)
        by (eapply term_env_related_eta_update; eauto).
      pose proof (IHbody X HXnot rho eta' sigma Henv' Hterms' Hsigma) as Hopened.
      rewrite erase_open_tm_ty in Hopened.
      unfold eta' in Hopened |- *.
      assert (HtypeCandidate : candidate_equiv (reducible (Ty_FVar X) rho (eta_update eta X C)) C).
      { intro z. unfold reducible, eta_update. rewrite Nat.eqb_refl. tauto. }
      assert (HtypeList : candidate_list_equiv
        (insert_candidate 0 (reducible (Ty_FVar X) rho (eta_update eta X C)) rho) (C :: rho)).
      { simpl. apply cle_cons; [exact HtypeCandidate|apply candidate_list_equiv_refl]. }
      assert (HbodyC : reducible T (C :: rho) eta (esubst_env sigma (erase body))).
      { apply (proj2 (reducible_eta_update T (C :: rho) eta X C HXty
           (esubst_env sigma (erase body)))).
        apply (proj1 (reducible_env_equiv T
          (insert_candidate 0 (reducible (Ty_FVar X) rho (eta_update eta X C)) rho)
          (C :: rho) (eta_update eta X C) HtypeList (esubst_env sigma (erase body)))).
        apply (proj1 (reducible_open_ty_rec T 0 rho (eta_update eta X C) (Ty_FVar X)
          (Nat.le_0_l _) (lc_ty_fvar 0 X) H
          (esubst_env sigma (erase body)))).
        change (reducible (open_ty_rec 0 (Ty_FVar X) T) rho (eta_update eta X C)
          (esubst_env sigma (erase body))) in Hopened.
        exact Hopened. }
      destruct (reducible_candidate_ok T (C :: rho) eta
        (conj (@Forall_cons (etm -> Prop) candidate_ok C rho HC (proj1 Henv)) (proj2 Henv)))
        as [_ [_ [_ HneutralT]]].
      apply HneutralT.
      * apply elc_tapp. exact Htabs.
      * apply en_tapp.
      * intros z Hz. inversion Hz; subst.
        -- exact HbodyC.
        -- exfalso. match goal with Hred : estep (e_tabs _) _ |- _ => inversion Hred end.
  - destruct (IHty rho eta sigma Henv Hterms Hsigma) as [_ [_ Hall]].
    pose proof (reducible_candidate_ok U rho eta Henv) as HC.
    pose proof (wf_ty_lc _ _ HwfU) as HU.
    pose proof (has_type_lc_ty _ _ _ _ Hty) as HTall.
    inversion HTall as [| | |HTbody|]; subst.
    apply (proj2 (reducible_open_ty_rec T 0 rho eta U
      (Nat.le_0_l _) HU H (e_tapp (esubst_env sigma (erase a))))).
    simpl. apply Hall. exact HC.
  - exact (reducible_numeric rho eta e_zero Henv en_zero).
  - exact (reducible_succ rho eta (esubst_env sigma (erase n))
      (IHty rho eta sigma Henv Hterms Hsigma)).
  - simpl. eapply reducible_natrec_general; eauto.
  - pose proof (has_type_erased_lc _ _ _ _ (T_Choice Delta Gamma a b T HtyA IHA)) as Hsrc.
    assert (Hchoice : elc (esubst_env sigma (erase (tm_choice a b))))
      by (eapply esubst_env_elc_at; eauto).
    destruct (reducible_candidate_ok T rho eta Henv) as [_ [_ [_ HneutralT]]].
    apply HneutralT.
    + exact Hchoice.
    + apply en_choice.
    + intros z Hz. inversion Hz; subst; [apply HtyB|apply IHB]; assumption.
Qed.

Lemma esubst_env_identity : forall t,
  esubst_env (fun x => e_fvar x) t = t.
Proof.
  induction t; simpl; rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3; reflexivity.
Qed.

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  intros t T Hty.
  set (eta := fun X : atom => fun e : etm => esn e /\ elc e).
  set (sigma := fun x : atom => e_fvar x).
  assert (Henv : env_candidates_ok [] eta).
  { split; [constructor|]. intros X. exact sn_candidate_ok. }
  assert (Hterms : term_env_related [] eta [] sigma).
  { intros x U Hlookup. discriminate. }
  assert (Hsigma : forall x, elc (sigma x)).
  { intros x. unfold sigma. constructor. }
  pose proof (fundamental [] [] t T Hty [] eta sigma Henv Hterms Hsigma) as Hred.
  rewrite esubst_env_identity in Hred.
  destruct (reducible_candidate_ok T [] eta Henv) as [HsnT _].
  apply erase_sn_reflect. eapply HsnT. exact Hred.
Qed.

End SystemFNormalizationNondeterminismRecursionEasyTask.
