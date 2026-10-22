(** System F CBV strong-normalization benchmark, Easy variant.
    Features: recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia Program.Equality.
Import ListNotations.

Module SystemFNormalizationRecursionEasyTask.

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
  | tm_natrec : tm -> tm -> tm -> tm.

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
  end.

Fixpoint erase_tm (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs _ t1 => tm_abs Ty_Nat (erase_tm t1)
  | tm_app t1 t2 => tm_app (erase_tm t1) (erase_tm t2)
  | tm_tabs t1 => tm_tabs (erase_tm t1)
  | tm_tapp t1 _ => tm_tapp (erase_tm t1) Ty_Nat
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (erase_tm t1)
  | tm_natrec n b s => tm_natrec (erase_tm n) (erase_tm b) (erase_tm s)
  end.

Lemma erase_tm_idempotent : forall t, erase_tm (erase_tm t) = erase_tm t.
Proof.
  induction t; simpl; try rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3; reflexivity.
Qed.

Lemma erase_open_tm_rec : forall t k u,
  erase_tm (open_tm_rec k u t) = open_tm_rec k (erase_tm u) (erase_tm t).
Proof.
  induction t; intros k u; simpl; try rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3;
    try reflexivity.
  destruct (Nat.eqb k n); reflexivity.
Qed.

Lemma erase_open_tm_ty_rec : forall t k U,
  erase_tm (open_tm_ty_rec k U t) = erase_tm t.
Proof.
  induction t; intros k U; simpl; try rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3;
    reflexivity.
Qed.

Lemma erase_tm_ty_subst : forall t X U,
  erase_tm (tm_ty_subst X U t) = erase_tm t.
Proof.
  induction t; intros X U; simpl; try rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3;
    reflexivity.
Qed.

Lemma open_erased_tm_ty_rec : forall t k U,
  open_tm_ty_rec k U (erase_tm t) = erase_tm t.
Proof.
  induction t; intros k U; simpl; try rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3;
    reflexivity.
Qed.

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
      lc_tm_at K k n -> lc_tm_at K k b -> lc_tm_at K k s -> lc_tm_at K k (tm_natrec n b s).

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
      has_type Delta Gamma (tm_natrec n b s) T.

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
  - apply lc_tm_succ. apply IHHlc; assumption.
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

Lemma erase_tm_lc_at : forall K k t,
  lc_tm_at K k t -> lc_tm_at K k (erase_tm t).
Proof.
  intros K k t Hlc. induction Hlc; simpl; eauto using lc_tm_at.
Qed.

Lemma erase_preserves_lc : forall t,
  locally_closed_tm t -> locally_closed_tm (erase_tm t).
Proof. intros t H; unfold locally_closed_tm in *; eapply erase_tm_lc_at; eauto. Qed.

Lemma erase_open_tm : forall t u,
  erase_tm (open_tm t u) = open_tm (erase_tm t) (erase_tm u).
Proof. intros; apply erase_open_tm_rec. Qed.

Lemma erase_open_tm_ty : forall t U, erase_tm (open_tm_ty t U) = erase_tm t.
Proof. intros; apply erase_open_tm_ty_rec. Qed.

Lemma numeric_value_lc : forall n, numeric_value n -> locally_closed_tm n.
Proof. intros n H. induction H; constructor; assumption. Qed.
Lemma value_regular : forall v, value v -> locally_closed_tm v.
Proof. intros v H. destruct H; try assumption; try constructor. apply numeric_value_lc. assumption. Qed.

Lemma erase_numeric_reflect : forall t,
  numeric_value (erase_tm t) -> numeric_value t.
Proof.
  induction t; simpl; intros H; try inversion H.
  - constructor.
  - inversion H; subst. constructor. eapply IHt. assumption.
Qed.

Lemma erase_value_reflect : forall t,
  locally_closed_tm t -> value (erase_tm t) -> value t.
Proof.
  intros t Hlc Hv. destruct t; simpl in *; dependent destruction Hv;
    try solve [inversion H].
  - apply v_abs. exact Hlc.
  - apply v_tabs. exact Hlc.
  - apply v_nat. constructor.
  - inversion H; subst. apply v_nat. constructor.
    eapply erase_numeric_reflect. eassumption.
Qed.

Lemma erase_numeric_forward : forall t,
  numeric_value t -> numeric_value (erase_tm t).
Proof. intros t H; induction H; simpl; constructor; assumption. Qed.

Lemma erase_value_forward : forall t,
  value t -> value (erase_tm t).
Proof.
  intros t Hv. destruct Hv.
  - apply v_abs. unfold locally_closed_tm in *.
    change (lc_tm_at 0 0 (erase_tm (tm_abs T t))).
    apply erase_tm_lc_at. exact H.
  - apply v_tabs. unfold locally_closed_tm in *.
    change (lc_tm_at 0 0 (erase_tm (tm_tabs t))).
    apply erase_tm_lc_at. exact H.
  - apply v_nat. eapply erase_numeric_forward. exact H.
Qed.

Lemma erase_step : forall t u, t --> u -> erase_tm t --> erase_tm u.
Proof.
  intros t u Hs. induction Hs; simpl.
  - rewrite erase_open_tm. apply ST_AppAbs.
    + change (locally_closed_tm (erase_tm (tm_abs T t))).
      apply erase_preserves_lc. exact H.
    + eapply erase_value_forward; eauto.
  - apply ST_App1.
    + exact IHHs.
    + apply erase_preserves_lc; assumption.
  - apply ST_App2.
    + eapply erase_value_forward; exact H.
    + exact IHHs.
  - rewrite erase_open_tm_ty.
    replace (erase_tm t) with (open_tm_ty (erase_tm t) Ty_Nat) at 2
      by (unfold open_tm_ty; exact (open_erased_tm_ty_rec t 0 Ty_Nat)).
    apply ST_TAppTabs.
    + change (locally_closed_tm (erase_tm (tm_tabs t))).
      apply erase_preserves_lc. exact H.
    + apply lc_ty_nat.
  - apply ST_TApp; [exact IHHs|apply lc_ty_nat].
  - apply ST_Succ. exact IHHs.
  - apply ST_RecArg; [exact IHHs|apply erase_preserves_lc; assumption|apply erase_preserves_lc; assumption].
  - apply ST_RecBase; [eapply erase_numeric_forward; exact H|exact IHHs|apply erase_preserves_lc; assumption].
  - apply ST_RecStep; [eapply erase_numeric_forward; exact H|eapply erase_value_forward; exact H0|exact IHHs].
  - apply ST_RecZero; eapply erase_value_forward; eassumption.
  - apply ST_RecSucc.
    + eapply erase_numeric_forward; eassumption.
    + eapply erase_value_forward; eassumption.
    + eapply erase_value_forward; eassumption.
Qed.

Lemma erase_step_reflect : forall t u,
  locally_closed_tm t -> erase_tm t --> u ->
  exists t', t --> t' /\ erase_tm t' = u.
Proof.
  induction t; intros u Hlc Hs; simpl in Hs; try solve [inversion Hs].
  - pose proof Hlc as Hlc_outer. inversion Hlc_outer; subst. dependent destruction Hs.
    + destruct t1; simpl in *; try discriminate.
      injection x as Hty Hbody. subst.
      exists (open_tm t1 t2). split.
      * apply ST_AppAbs.
        -- assumption.
        -- eapply erase_value_reflect; eassumption.
      * rewrite erase_open_tm. reflexivity.
    + assert (Hlc1 : locally_closed_tm t1) by (inversion Hlc; assumption).
      destruct (IHt1 _ Hlc1 Hs) as [t1new [Hred Heq]].
      exists (tm_app t1new t2). split.
      * apply ST_App1; assumption.
      * simpl. rewrite Heq. reflexivity.
    + match goal with Hlc2 : lc_tm_at 0 0 t2 |- _ =>
        destruct (IHt2 _ Hlc2 Hs) as [t2new [Hred Heq]]
      end.
      exists (tm_app t1 t2new). split.
      * apply ST_App2.
        -- eapply erase_value_reflect; eassumption.
        -- assumption.
      * simpl. rewrite Heq. reflexivity.
  - pose proof Hlc as Hlc_outer. inversion Hlc_outer; subst. dependent destruction Hs.
    + destruct t; simpl in *; try discriminate.
      injection x as Hbody. subst t1.
      exists (open_tm_ty t t0). split.
      * apply ST_TAppTabs; [inversion Hlc; assumption|inversion Hlc; assumption].
      * rewrite erase_open_tm_ty. unfold open_tm_ty. symmetry.
        exact (open_erased_tm_ty_rec t 0 Ty_Nat).
    + match goal with Hloc : lc_tm_at 0 0 t |- _ =>
        destruct (IHt _ Hloc Hs) as [tnew [Hred Heq]]
      end.
      exists (tm_tapp tnew t0). split.
      * apply ST_TApp; [assumption|inversion Hlc; assumption].
      * simpl. rewrite Heq. reflexivity.
  - pose proof Hlc as Hlc_outer. inversion Hlc_outer; subst. dependent destruction Hs.
    destruct (IHt _ H2 Hs) as [tnew [Hred Heq]].
    exists (tm_succ tnew). split; [apply ST_Succ; assumption|].
    simpl. rewrite Heq. reflexivity.
  - pose proof Hlc as Hlc_outer. inversion Hlc_outer; subst. dependent destruction Hs.
    + match goal with Hbody : lc_tm_at 0 0 t1 |- _ =>
        destruct (IHt1 _ Hbody Hs) as [nnew [Hred Heq]]
      end.
      exists (tm_natrec nnew t2 t3). split.
      * apply ST_RecArg; assumption.
      * simpl. rewrite Heq. reflexivity.
    + match goal with Hbody : lc_tm_at 0 0 t2 |- _ =>
        destruct (IHt2 _ Hbody Hs) as [bnew [Hred Heq]]
      end.
      exists (tm_natrec t1 bnew t3). split.
      * apply ST_RecBase.
        -- eapply erase_numeric_reflect; eassumption.
        -- exact Hred.
        -- assumption.
      * simpl. rewrite Heq. reflexivity.
    + match goal with Hbody : lc_tm_at 0 0 t3 |- _ =>
        destruct (IHt3 _ Hbody Hs) as [snew [Hred Heq]]
      end.
      exists (tm_natrec t1 t2 snew). split.
      * apply ST_RecStep.
        -- eapply erase_numeric_reflect; eassumption.
        -- eapply erase_value_reflect; eassumption.
        -- exact Hred.
      * simpl. rewrite Heq. reflexivity.
    + destruct t1; simpl in *; try discriminate.
      exists t2. split.
      * apply ST_RecZero; eapply erase_value_reflect; eassumption.
      * reflexivity.
    + destruct t1 as [idx|atom0|A0 body0|f0 a0|body1|f1 U0| |pred|rn0 rb0 rs0]; simpl in *; try discriminate.
      injection x as Hnum_eq. subst n.
      pose proof (erase_numeric_reflect pred H) as Hnum.
      exists (tm_app (tm_app t3 pred) (tm_natrec pred t2 t3)). split.
      * apply ST_RecSucc.
        -- exact Hnum.
        -- eapply erase_value_reflect; eassumption.
        -- eapply erase_value_reflect; eassumption.
      * reflexivity.
Qed.

Lemma lc_step : forall t u, locally_closed_tm t -> t --> u -> locally_closed_tm u.
Proof.
  intros t u Hlc Hs. revert Hlc. induction Hs; intros Hlc; inversion Hlc; subst.
  - match goal with
    | Habs : locally_closed_tm (tm_abs _ ?body), Hv : value ?v
        |- locally_closed_tm (open_tm ?body ?v) =>
        assert (Hb : lc_tm_at 0 1 body) by (inversion Habs; assumption);
        unfold locally_closed_tm, open_tm;
        eapply open_tm_preserves_lc_at with (K := 0) (k := 0);
        [exact Hb | eapply value_regular; exact Hv]
    end.
  - eapply lc_tm_app.
    + eapply IHHs; eassumption.
    + eassumption.
  - eapply lc_tm_app.
    + eapply value_regular; eassumption.
    + eapply IHHs; eassumption.
  - match goal with
    | Habs : locally_closed_tm (tm_tabs ?body) |- _ =>
        inversion Habs; subst; eapply open_tm_ty_preserves_lc_at; eauto
    end.
  - eapply lc_tm_tapp.
    + eapply IHHs; eassumption.
    + assumption.
  - eapply lc_tm_succ. eapply IHHs; eassumption.
  - eapply lc_tm_rec.
    + eapply IHHs; eassumption.
    + assumption.
    + assumption.
  - eapply lc_tm_rec.
    + assumption.
    + eapply IHHs; eassumption.
    + assumption.
  - eapply lc_tm_rec.
    + assumption.
    + assumption.
    + eapply IHHs; eassumption.
  - assumption.
  - eapply lc_tm_app.
    + eapply lc_tm_app.
      * eapply value_regular; eassumption.
      * eapply numeric_value_lc; eassumption.
    + eapply lc_tm_rec.
      * eapply numeric_value_lc; eassumption.
      * eapply value_regular; eassumption.
      * eapply value_regular; eassumption.
Qed.
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

Lemma value_strongly_normalizing : forall v,
  value v -> strongly_normalizing v.
Proof.
  intros v Hv. constructor. intros u Hstep.
  exfalso. eapply value_no_step; eauto.
Qed.

Lemma numeric_strongly_normalizing : forall n,
  numeric_value n -> strongly_normalizing n.
Proof.
  intros n Hn. constructor. intros u Hstep.
  exfalso. eapply numeric_no_step; eauto.
Qed.

Lemma sn_step : forall t, strongly_normalizing t -> forall u,
  t --> u -> strongly_normalizing u.
Proof. intros t H; inversion H; eauto. Qed.

Lemma multi_preserves_sn : forall t u,
  strongly_normalizing t -> t -->* u -> strongly_normalizing u.
Proof.
  intros t u Hsn Hmulti. induction Hmulti; auto.
  eapply IHHmulti. eapply sn_step; eauto.
Qed.

Lemma sn_induction : forall (P : tm -> Prop) t,
  strongly_normalizing t ->
  (forall t, (forall u, t --> u -> P u) -> P t) -> P t.
Proof.
  intros P t Hsn. induction Hsn as [t Hnext IH]. intros Hrec.
  apply Hrec. intros u Hu. apply IH; assumption.
Qed.

Lemma erase_sn_reflect : forall t,
  strongly_normalizing (erase_tm t) -> strongly_normalizing t.
Proof.
  intros t Hsn. remember (erase_tm t) as e eqn:E.
  revert t E. induction Hsn as [e Hred IH]. intros t E.
  constructor. intros u Hu.
  eapply IH with (u := erase_tm u) (t := u).
  - rewrite E. apply erase_step. exact Hu.
  - reflexivity.
Qed.

Definition candidate_ok (P : tm -> Prop) : Prop :=
  (forall t, P t -> strongly_normalizing t) /\
  (forall t, P t -> locally_closed_tm t) /\
  (forall t u, P t -> t --> u -> P u) /\
  (forall t, locally_closed_tm t -> ~ value t ->
     (forall u, t --> u -> P u) -> P t).

Definition base_candidate : tm -> Prop := fun t =>
  strongly_normalizing t /\ locally_closed_tm t.

Fixpoint semantic_type (rho : atom -> tm -> Prop)
    (bound : list (tm -> Prop)) (T : ty) : tm -> Prop :=
  match T with
  | Ty_BVar i => fun t => locally_closed_tm t /\ nth i bound base_candidate (erase_tm t)
  | Ty_FVar X => fun t => locally_closed_tm t /\ rho X (erase_tm t)
  | Ty_Arrow A B => fun t =>
       strongly_normalizing (erase_tm t) /\ locally_closed_tm t /\
       (forall v, semantic_type rho bound A v ->
                    semantic_type rho bound B
                      (tm_app (erase_tm t) (erase_tm v)))
  | Ty_All A => fun t =>
       strongly_normalizing (erase_tm t) /\ locally_closed_tm t /\
       (forall P, candidate_ok P ->
           semantic_type rho (P :: bound) A
             (tm_tapp (erase_tm t) Ty_Nat))
  | Ty_Nat => fun t => strongly_normalizing (erase_tm t) /\ locally_closed_tm t
  end.

Lemma lc_app : forall t u, locally_closed_tm t -> locally_closed_tm u ->
  locally_closed_tm (tm_app t u).
Proof. intros; unfold locally_closed_tm in *; eapply lc_tm_app; eassumption. Qed.

Lemma lc_tapp : forall t T, locally_closed_tm t -> locally_closed_ty T ->
  locally_closed_tm (tm_tapp t T).
Proof. intros; unfold locally_closed_tm, locally_closed_ty in *;
  eapply lc_tm_tapp; eassumption. Qed.

Lemma semantic_type_lc : forall T rho bound t,
  semantic_type rho bound T t -> locally_closed_tm t.
Proof. induction T; intros rho bound t H; simpl in H; tauto. Qed.

Lemma semantic_erasure_extensional : forall T rho bound t u,
  erase_tm t = erase_tm u -> locally_closed_tm t -> locally_closed_tm u ->
  semantic_type rho bound T t -> semantic_type rho bound T u.
Proof.
  induction T; intros rho bound t u Heq Hlt Hlu Hsem; simpl in *.
  - destruct Hsem as [Hlc HP]. split; [exact Hlu|]. rewrite <- Heq. exact HP.
  - destruct Hsem as [Hlc HP]. split; [exact Hlu|]. rewrite <- Heq. exact HP.
  - destruct Hsem as [Hsn [Hlc Hfun]]. split.
    + rewrite <- Heq. exact Hsn.
    + split; [exact Hlu|]. intros v Hv.
      pose proof (Hfun v Hv) as HB.
      eapply IHT2 with (t := tm_app (erase_tm t) (erase_tm v))
                       (u := tm_app (erase_tm u) (erase_tm v)).
      * simpl. rewrite Heq. reflexivity.
      * apply lc_app; apply erase_preserves_lc; [exact Hlt|apply semantic_type_lc with (T := T1) (rho := rho) (bound := bound); exact Hv].
      * apply lc_app; apply erase_preserves_lc; [exact Hlu|apply semantic_type_lc with (T := T1) (rho := rho) (bound := bound); exact Hv].
      * exact HB.
  - destruct Hsem as [Hsn [Hlc Hfun]]. split.
    + rewrite <- Heq. exact Hsn.
    + split; [exact Hlu|]. intros P HP.
      pose proof (Hfun P HP) as HB.
      eapply IHT with (t := tm_tapp (erase_tm t) Ty_Nat)
                      (u := tm_tapp (erase_tm u) Ty_Nat).
      * simpl. rewrite Heq. reflexivity.
      * apply lc_tapp; [apply erase_preserves_lc; exact Hlt|apply lc_ty_nat].
      * apply lc_tapp; [apply erase_preserves_lc; exact Hlu|apply lc_ty_nat].
      * exact HB.
  - destruct Hsem as [Hsn Hlc]. split; [rewrite <- Heq; exact Hsn|exact Hlu].
Qed.

Lemma nth_app_lt : forall (A : Type) (l1 l2 : list A) n d,
  n < length l1 -> nth n (l1 ++ l2) d = nth n l1 d.
Proof.
  intros A l1. induction l1; intros l2 n d H; simpl in *; [lia|].
  destruct n; simpl; auto. apply IHl1. lia.
Qed.

Lemma nth_app_length_cons : forall (A : Type) (l : list A) a (r : list A) d,
  nth (length l) (l ++ a :: r) d = a.
Proof. induction l; intros; simpl; auto. Qed.

Lemma semantic_cons_agree : forall (P : tm -> Prop) bs1 bs2 k,
  (forall i, i < k -> nth i bs1 base_candidate = nth i bs2 base_candidate) ->
  forall i, i < S k ->
    nth i (P :: bs1) base_candidate = nth i (P :: bs2) base_candidate.
Proof.
  intros P bs1 bs2 k Hagree [|i] Hi; simpl; auto. apply Hagree. lia.
Qed.

Lemma semantic_bound_extensional : forall T rho bs1 bs2 k,
  (forall i, i < k -> nth i bs1 base_candidate = nth i bs2 base_candidate) ->
  lc_ty_at k T -> forall t,
  semantic_type rho bs1 T t <-> semantic_type rho bs2 T t.
Proof.
  induction T; intros rho bs1 bs2 k Hagree Hlc t; simpl in *.
  - inversion Hlc; subst. rewrite (Hagree n H1). tauto.
  - tauto.
  - inversion Hlc; subst. split.
    + intros [Hsn [Hlt Hfun]]. split; [exact Hsn|]. split; [exact Hlt|].
      intros v Hv.
      pose proof (proj2 (IHT1 rho bs1 bs2 k Hagree H2 v) Hv) as Hv1.
      pose proof (Hfun v Hv1) as Hv2.
      exact (proj1 (IHT2 rho bs1 bs2 k Hagree H3
        (tm_app (erase_tm t) (erase_tm v))) Hv2).
    + intros [Hsn [Hlt Hfun]]. split; [exact Hsn|]. split; [exact Hlt|].
      intros v Hv.
      pose proof (proj1 (IHT1 rho bs1 bs2 k Hagree H2 v) Hv) as Hv1.
      pose proof (Hfun v Hv1) as Hv2.
      exact (proj2 (IHT2 rho bs1 bs2 k Hagree H3
        (tm_app (erase_tm t) (erase_tm v))) Hv2).
  - inversion Hlc; subst. split.
    + intros [Hsn [Hlt Hfun]]. split; [exact Hsn|]. split; [exact Hlt|]. intros P HP.
      pose proof (Hfun P HP) as HB.
      exact (proj1 (IHT rho (P :: bs1) (P :: bs2) (S k)
        (semantic_cons_agree P bs1 bs2 k Hagree) ltac:(assumption)
        (tm_tapp (erase_tm t) Ty_Nat)) HB).
    + intros [Hsn [Hlt Hfun]]. split; [exact Hsn|]. split; [exact Hlt|]. intros P HP.
      pose proof (Hfun P HP) as HB.
      exact (proj2 (IHT rho (P :: bs1) (P :: bs2) (S k)
        (semantic_cons_agree P bs1 bs2 k Hagree) ltac:(assumption)
        (tm_tapp (erase_tm t) Ty_Nat)) HB).
  - tauto.
Qed.

Lemma semantic_closed_erasure_bound : forall U rho bs1 bs2 t,
  locally_closed_ty U -> locally_closed_tm t ->
  (semantic_type rho bs1 U t <-> semantic_type rho bs2 U (erase_tm t)).
Proof.
  intros U rho bs1 bs2 t HU Htlc. split; intros H.
  - pose proof (proj1 (semantic_bound_extensional U rho bs1 bs2 0
      (fun i Hi => False_rect _ (Nat.nlt_0_r i Hi)) HU t) H) as H'.
    eapply semantic_erasure_extensional with (t := t) (u := erase_tm t).
    + rewrite erase_tm_idempotent. reflexivity.
    + exact (semantic_type_lc _ _ _ _ H').
    + apply erase_preserves_lc. exact (semantic_type_lc _ _ _ _ H').
    + exact H'.
  - pose proof (proj2 (semantic_bound_extensional U rho bs1 bs2 0
      (fun i Hi => False_rect _ (Nat.nlt_0_r i Hi)) HU t)) as Hbound.
    assert (Hback : semantic_type rho bs2 U t).
    { eapply semantic_erasure_extensional with (t := erase_tm t) (u := t).
      - rewrite erase_tm_idempotent. reflexivity.
      - apply erase_preserves_lc. exact Htlc.
      - exact Htlc.
      - exact H. }
    exact (Hbound Hback).
Qed.

Lemma semantic_open_ty_rec : forall T rho inner outer k U t,
  length inner = k -> lc_ty_at (S k) T -> locally_closed_ty U ->
  locally_closed_tm t ->
  (semantic_type rho (inner ++ outer) (open_ty_rec k U T) t <->
   semantic_type rho (inner ++ semantic_type rho outer U :: outer) T t).
Proof.
  induction T; intros rho inner outer k U t Hlen Hlc HU Htlc; simpl in *.
  - inversion Hlc; subst. simpl.
    destruct (Nat.eqb (length inner) n) eqn:E.
    + apply Nat.eqb_eq in E. subst n.
      rewrite (nth_app_length_cons _ inner (semantic_type rho outer U) outer base_candidate).
      split; intros Hsem.
      * split.
        -- exact (semantic_type_lc _ _ _ _ Hsem).
        -- apply (proj1 (semantic_closed_erasure_bound U rho
             (inner ++ outer) outer t HU Htlc)). exact Hsem.
      * destruct Hsem as [Htargetlc HP].
        apply (proj2 (semantic_closed_erasure_bound U rho
          (inner ++ outer) outer t HU Htlc)). exact HP.
    + apply Nat.eqb_neq in E. assert (Hni : n < length inner) by lia.
      change (semantic_type rho (inner ++ outer) (Ty_BVar n) t <->
        semantic_type rho (inner ++ semantic_type rho outer U :: outer)
          (Ty_BVar n) t).
      eapply semantic_bound_extensional with (k := length inner).
      * intros i Hi.
        rewrite (nth_app_lt _ inner outer i base_candidate) by exact Hi.
        rewrite (nth_app_lt _ inner (semantic_type rho outer U :: outer) i base_candidate) by exact Hi.
        reflexivity.
      * constructor. exact Hni.
  - tauto.
  - inversion Hlc; subst. split.
    + intros [Hsn [Hlt Hfun]]. split; [exact Hsn|]. split; [exact Hlt|]. intros v Hv.
      apply (proj1 (IHT2 rho inner outer (length inner) U
        (tm_app (erase_tm t) (erase_tm v)) eq_refl H3 HU
        ltac:(apply lc_app; [apply erase_preserves_lc; exact Htlc|apply erase_preserves_lc; exact (semantic_type_lc _ _ _ _ Hv)]) )).
      apply Hfun. apply (proj2 (IHT1 rho inner outer (length inner) U v eq_refl H2 HU
        ltac:(eapply semantic_type_lc; eassumption))). exact Hv.
    + intros [Hsn [Hlt Hfun]]. split; [exact Hsn|]. split; [exact Hlt|]. intros v Hv.
      apply (proj2 (IHT2 rho inner outer (length inner) U
        (tm_app (erase_tm t) (erase_tm v)) eq_refl H3 HU
        ltac:(apply lc_app; [apply erase_preserves_lc; exact Htlc|apply erase_preserves_lc; exact (semantic_type_lc _ _ _ _ Hv)]) )).
      apply Hfun. apply (proj1 (IHT1 rho inner outer (length inner) U v eq_refl H2 HU
        ltac:(eapply semantic_type_lc; eassumption))). exact Hv.
  - inversion Hlc; subst. split.
    + intros [Hsn [Hlt Hfun]]. split; [exact Hsn|]. split; [exact Hlt|]. intros P HP.
      apply (proj1 (IHT rho (P :: inner) outer (S (length inner)) U
        (tm_tapp (erase_tm t) Ty_Nat) eq_refl ltac:(assumption) HU
        ltac:(apply lc_tapp; [apply erase_preserves_lc; exact Htlc|apply lc_ty_nat]))).
      apply Hfun. exact HP.
    + intros [Hsn [Hlt Hfun]]. split; [exact Hsn|]. split; [exact Hlt|]. intros P HP.
      apply (proj2 (IHT rho (P :: inner) outer (S (length inner)) U
        (tm_tapp (erase_tm t) Ty_Nat) eq_refl ltac:(assumption) HU
        ltac:(apply lc_tapp; [apply erase_preserves_lc; exact Htlc|apply lc_ty_nat]))).
      apply Hfun. exact HP.
  - tauto.
Qed.

Lemma wf_ty_locally_closed : forall Delta T,
  wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T Hwf. induction Hwf.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; assumption.
  - unfold locally_closed_ty. apply lc_ty_all.
    eapply lc_ty_at_open_inv with (X := fresh L).
    specialize (H0 (fresh L) (fresh_notin L)).
    exact H0.
  - apply lc_ty_nat.
Qed.

Lemma has_type_locally_closed : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T Hty. induction Hty.
  - apply lc_tm_fvar.
  - unfold locally_closed_tm. apply lc_tm_abs.
    + exact (wf_ty_locally_closed _ _ H).
    + eapply lc_tm_at_open_tm_inv with (x := fresh L).
      specialize (H1 (fresh L) (fresh_notin L)). exact H1.
  - unfold locally_closed_tm in *. apply lc_tm_app; assumption.
  - unfold locally_closed_tm. apply lc_tm_tabs.
    eapply lc_tm_at_open_ty_inv with (X := fresh L).
    specialize (H0 (fresh L) (fresh_notin L)). exact H0.
  - unfold locally_closed_tm in *. apply lc_tm_tapp.
    + assumption.
    + exact (wf_ty_locally_closed _ _ H).
  - unfold locally_closed_tm. apply lc_tm_zero.
  - unfold locally_closed_tm in *. apply lc_tm_succ. assumption.
  - unfold locally_closed_tm in *. apply lc_tm_rec; assumption.
Qed.

Lemma has_type_result_locally_closed : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_ty T.
Proof.
  intros Delta Gamma t T Hty. induction Hty.
  - exact (wf_ty_locally_closed _ _ H0).
  - unfold locally_closed_ty. apply lc_ty_arrow.
    + exact (wf_ty_locally_closed _ _ H).
    + specialize (H1 (fresh L) (fresh_notin L)). exact H1.
  - inversion IHHty1; assumption.
  - unfold locally_closed_ty. apply lc_ty_all.
    eapply lc_ty_at_open_inv with (X := fresh L).
    specialize (H0 (fresh L) (fresh_notin L)). exact H0.
  - inversion IHHty. unfold locally_closed_ty.
    apply lc_ty_at_open with (U := U); [assumption|exact (wf_ty_locally_closed _ _ H)].
  - apply lc_ty_nat.
  - exact IHHty.
  - exact IHHty2.
Qed.

Definition semantic_rho_update (rho : atom -> tm -> Prop) (X : atom)
    (P : tm -> Prop) : atom -> tm -> Prop :=
  fun Y => if Nat.eqb X Y then P else rho Y.

Lemma semantic_rho_extensional : forall T rho1 rho2 bound t,
  (forall X, In X (fv_ty T) -> rho1 X = rho2 X) ->
  semantic_type rho1 bound T t <-> semantic_type rho2 bound T t.
Proof.
  induction T; intros rho1 rho2 bound t Hagree; simpl.
  - tauto.
  - split.
    + intros [Hlc HP]. split; [exact Hlc|].
      rewrite <- (Hagree a (or_introl eq_refl)). exact HP.
    + intros [Hlc HP]. split; [exact Hlc|].
      rewrite (Hagree a (or_introl eq_refl)). exact HP.
  - split.
    + intros [Hsn [Hlc Hfun]]. split; [exact Hsn|]. split; [exact Hlc|]. intros v Hv.
      apply (proj1 (IHT2 rho1 rho2 bound
        (tm_app (erase_tm t) (erase_tm v)) ltac:(intros X HX; apply Hagree; apply in_or_app; right; exact HX))).
      apply Hfun. apply (proj2 (IHT1 rho1 rho2 bound v
        ltac:(intros X HX; apply Hagree; apply in_or_app; left; exact HX))). exact Hv.
    + intros [Hsn [Hlc Hfun]]. split; [exact Hsn|]. split; [exact Hlc|]. intros v Hv.
      apply (proj2 (IHT2 rho1 rho2 bound
        (tm_app (erase_tm t) (erase_tm v)) ltac:(intros X HX; apply Hagree; apply in_or_app; right; exact HX))).
      apply Hfun. apply (proj1 (IHT1 rho1 rho2 bound v
        ltac:(intros X HX; apply Hagree; apply in_or_app; left; exact HX))). exact Hv.
  - split.
    + intros [Hsn [Hlc Hfun]]. split; [exact Hsn|]. split; [exact Hlc|]. intros P HP.
      apply (proj1 (IHT rho1 rho2 (P :: bound)
        (tm_tapp (erase_tm t) Ty_Nat) Hagree)). apply Hfun. exact HP.
    + intros [Hsn [Hlc Hfun]]. split; [exact Hsn|]. split; [exact Hlc|]. intros P HP.
      apply (proj2 (IHT rho1 rho2 (P :: bound)
        (tm_tapp (erase_tm t) Ty_Nat) Hagree)). apply Hfun. exact HP.
  - tauto.
Qed.

Lemma semantic_rho_update_notin : forall T rho X P bound t,
  ~ In X (fv_ty T) ->
  semantic_type (semantic_rho_update rho X P) bound T t <->
  semantic_type rho bound T t.
Proof.
  intros T rho X P bound t HX.
  apply semantic_rho_extensional. intros Y HY. unfold semantic_rho_update.
  destruct (Nat.eqb X Y) eqn:E; auto. apply Nat.eqb_eq in E. subst. contradiction.
Qed.

Definition term_environment_ok (rho : atom -> tm -> Prop)
    (bound : list (tm -> Prop)) (Gamma : context) (gamma : term_substitution) : Prop :=
  forall x A, lookup_context x Gamma = Some A ->
    semantic_type rho bound A (gamma x).

Lemma lookup_fv_context : forall Gamma x A Y,
  lookup_context x Gamma = Some A -> In Y (fv_ty A) -> In Y (ftv_context Gamma).
Proof.
  induction Gamma as [|[z B] Gamma IH]; intros x A Y Hlookup HY; simpl in *; try discriminate.
  destruct (Nat.eqb x z) eqn:E.
  - inversion Hlookup; subst. apply in_or_app. left. exact HY.
  - apply in_or_app. right. eapply IH; eauto.
Qed.

Lemma term_environment_update : forall rho bound Gamma gamma x A v,
  term_environment_ok rho bound Gamma gamma ->
  semantic_type rho bound A v ->
  term_environment_ok rho bound (update Gamma x A)
    (term_subst_update gamma x v).
Proof.
  intros rho bound Gamma gamma x A v Henv Hv y B Hlookup.
  unfold update, term_subst_update in *. simpl in Hlookup.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y. inversion Hlookup; subst. rewrite Nat.eqb_refl. exact Hv.
  - rewrite Nat.eqb_sym, E. eapply Henv. exact Hlookup.
Qed.

Lemma instantiate_open_tm_rec : forall t k theta gamma x v,
  term_substitution_closed gamma ->
  ~ In x (fv_tm t) ->
  instantiate theta (term_subst_update gamma x v)
    (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k v (instantiate theta gamma t).
Proof.
  induction t; intros k theta gamma x v Hgamma Hfresh; simpl in *.
  - destruct (Nat.eqb k n).
    + unfold term_subst_update.
      change ((if Nat.eqb x x then v else gamma x) = v).
      rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply Hfresh. simpl. auto.
    + apply Nat.eqb_neq in E. assert (E' : Nat.eqb x a = false) by (apply Nat.eqb_neq; exact E).
      unfold term_subst_update. rewrite E'.
      rewrite (open_tm_rec_lc_at (gamma a) 0 k v
        (lc_tm_at_monotone 0 0 0 k (gamma a) (Hgamma a)
          (le_n 0) (Nat.le_0_l k))).
      reflexivity.
  - f_equal. apply IHt; assumption.
  - assert (H1 : ~ In x (fv_tm t1)) by (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (H2 : ~ In x (fv_tm t2)) by (intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
    rewrite (IHt1 k theta gamma x v Hgamma H1), (IHt2 k theta gamma x v Hgamma H2). reflexivity.
  - f_equal. apply IHt; assumption.
  - f_equal. apply IHt; assumption.
  - reflexivity.
  - f_equal. apply IHt; assumption.
  - assert (Hn : ~ In x (fv_tm t1)) by (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (Hbs : ~ In x (fv_tm t2 ++ fv_tm t3)) by (intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
    assert (Hb : ~ In x (fv_tm t2)) by (intro Hin; apply Hbs; apply in_or_app; left; exact Hin).
    assert (Hs : ~ In x (fv_tm t3)) by (intro Hin; apply Hbs; apply in_or_app; right; exact Hin).
    rewrite (IHt1 k theta gamma x v Hgamma Hn), (IHt2 k theta gamma x v Hgamma Hb), (IHt3 k theta gamma x v Hgamma Hs). reflexivity.
Qed.

Lemma instantiate_ty_identity : forall T,
  instantiate_ty identity_type_substitution T = T.
Proof. induction T; simpl; rewrite ?IHT, ?IHT1, ?IHT2; reflexivity. Qed.

Lemma instantiate_lc_at : forall t K k gamma,
  lc_tm_at K k t -> term_substitution_closed gamma ->
  lc_tm_at K k (instantiate identity_type_substitution gamma t).
Proof.
  intros t K k gamma Hlc. revert gamma.
  induction Hlc; intros gamma Hgamma; simpl.
  - apply lc_tm_bvar. exact H.
  - eapply lc_tm_at_monotone.
    + exact (Hgamma x).
    + lia.
    + lia.
  - rewrite instantiate_ty_identity. apply lc_tm_abs.
    + assumption.
    + apply IHHlc. exact Hgamma.
  - apply lc_tm_app; [apply IHHlc1|apply IHHlc2]; exact Hgamma.
  - apply lc_tm_tabs. apply IHHlc. exact Hgamma.
  - rewrite instantiate_ty_identity. apply lc_tm_tapp.
    + apply IHHlc. exact Hgamma.
    + assumption.
  - apply lc_tm_zero.
  - apply lc_tm_succ. apply IHHlc. exact Hgamma.
  - apply lc_tm_rec; [apply IHHlc1|apply IHHlc2|apply IHHlc3]; exact Hgamma.
Qed.

Lemma instantiate_locally_closed : forall t gamma,
  locally_closed_tm t -> term_substitution_closed gamma ->
  locally_closed_tm (instantiate identity_type_substitution gamma t).
Proof.
  intros t gamma Hlc Hgamma. unfold locally_closed_tm in *.
  eapply instantiate_lc_at; eauto.
Qed.

Lemma semantic_bound_erased_equiv : forall T rho bs1 bs2 k,
  (forall i, i < k -> forall e, locally_closed_tm e -> erase_tm e = e ->
     (nth i bs1 base_candidate e <-> nth i bs2 base_candidate e)) ->
  lc_ty_at k T -> forall t, locally_closed_tm t ->
  (semantic_type rho bs1 T t <-> semantic_type rho bs2 T t).
Proof.
  induction T; intros rho bs1 bs2 k Hagree Hty t Htlc; simpl in *.
  - inversion Hty; subst. split.
    + intros [Hlc HP]. split; [exact Htlc|].
      apply (proj1 (Hagree n H1 (erase_tm t)
        (erase_preserves_lc t Htlc) (erase_tm_idempotent t))). exact HP.
    + intros [Hlc HP]. split; [exact Htlc|].
      apply (proj2 (Hagree n H1 (erase_tm t)
        (erase_preserves_lc t Htlc) (erase_tm_idempotent t))). exact HP.
  - tauto.
  - inversion Hty; subst. split.
    + intros [Hsn [Hlc Hfun]]. split; [exact Hsn|]. split; [exact Htlc|]. intros v Hv.
      assert (Hvlc : locally_closed_tm v) by (eapply semantic_type_lc; eassumption).
      pose proof (proj2 (IHT1 rho bs1 bs2 k Hagree H2 v Hvlc) Hv) as Hv'.
      pose proof (Hfun v Hv') as HB.
      apply (proj1 (IHT2 rho bs1 bs2 k Hagree H3
        (tm_app (erase_tm t) (erase_tm v))
        (semantic_type_lc _ _ _ _ HB))).
      exact HB.
    + intros [Hsn [Hlc Hfun]]. split; [exact Hsn|]. split; [exact Htlc|]. intros v Hv.
      assert (Hvlc : locally_closed_tm v) by (eapply semantic_type_lc; eassumption).
      pose proof (proj1 (IHT1 rho bs1 bs2 k Hagree H2 v Hvlc) Hv) as Hv'.
      pose proof (Hfun v Hv') as HB.
      apply (proj2 (IHT2 rho bs1 bs2 k Hagree H3
        (tm_app (erase_tm t) (erase_tm v))
        (semantic_type_lc _ _ _ _ HB))). exact HB.
  - inversion Hty; subst. split.
    + intros [Hsn [Hlc Hfun]]. split; [exact Hsn|]. split; [exact Htlc|]. intros P HP.
      pose proof (Hfun P HP) as HB.
      apply (proj1 (IHT rho (P :: bs1) (P :: bs2) (S k)
        (fun i Hi e Hle Herase =>
          match i as j return j < S k ->
            forall e, locally_closed_tm e -> erase_tm e = e ->
              (nth j (P :: bs1) base_candidate e <-> nth j (P :: bs2) base_candidate e) with
          | 0 => fun _ e _ _ => iff_refl (P e)
          | S j => fun Hj e Hle Herase => Hagree j ltac:(lia) e Hle Herase
          end Hi e Hle Herase) H1 (tm_tapp (erase_tm t) Ty_Nat)
        (semantic_type_lc _ _ _ _ HB))). exact HB.
    + intros [Hsn [Hlc Hfun]]. split; [exact Hsn|]. split; [exact Htlc|]. intros P HP.
      pose proof (Hfun P HP) as HB.
      apply (proj2 (IHT rho (P :: bs1) (P :: bs2) (S k)
        (fun i Hi e Hle Herase =>
          match i as j return j < S k ->
            forall e, locally_closed_tm e -> erase_tm e = e ->
              (nth j (P :: bs1) base_candidate e <-> nth j (P :: bs2) base_candidate e) with
          | 0 => fun _ e _ _ => iff_refl (P e)
          | S j => fun Hj e Hle Herase => Hagree j ltac:(lia) e Hle Herase
          end Hi e Hle Herase) H1 (tm_tapp (erase_tm t) Ty_Nat)
        (semantic_type_lc _ _ _ _ HB))). exact HB.
  - tauto.
Qed.

Lemma semantic_candidate_insert_equiv : forall T rho bound P Q t,
  candidate_ok P ->
  (forall e, locally_closed_tm e -> erase_tm e = e -> (Q e <-> P e)) ->
  lc_ty_at 1 T -> locally_closed_tm t ->
  (semantic_type rho (Q :: bound) T t <->
   semantic_type rho (P :: bound) T t).
Proof.
  intros T rho bound P Q t HP Hagree Hty Hlc.
  eapply semantic_bound_erased_equiv with (k := 1); eauto.
  intros [|i] Hi e He Herase; simpl.
  - apply Hagree; assumption.
  - lia.
Qed.

Definition erased_term_substitution (gamma : term_substitution) : term_substitution :=
  fun x => erase_tm (gamma x).

Lemma erase_instantiate : forall t theta gamma,
  erase_tm (instantiate theta gamma t) =
  instantiate identity_type_substitution (erased_term_substitution gamma) (erase_tm t).
Proof.
  induction t; intros theta gamma; simpl; try rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3; reflexivity.
Qed.

Lemma term_environment_rho_update : forall rho bound Gamma gamma X P,
  term_environment_ok rho bound Gamma gamma ->
  ~ In X (ftv_context Gamma) ->
  term_environment_ok (semantic_rho_update rho X P) bound Gamma gamma.
Proof.
  intros rho bound Gamma gamma X P Henv HX x A Hlookup.
  assert (Hnotin : ~ In X (fv_ty A)).
  { intro Hfv. apply HX. eapply lookup_fv_context; eauto. }
  apply (proj2 (semantic_rho_update_notin A rho X P bound (gamma x) Hnotin)).
  apply Henv with (x := x). exact Hlookup.
Qed.

Lemma sn_succ : forall t, strongly_normalizing t ->
  strongly_normalizing (tm_succ t).
Proof.
  intros t Hsn.
  eapply sn_induction with (P := fun q => strongly_normalizing (tm_succ q)).
  - exact Hsn.
  - intros q IH. constructor. intros u Hstep. inversion Hstep; subst.
    eapply IH. eassumption.
Qed.

Lemma fresh_notin_app_left : forall (A B : list atom) (x : atom),
  ~ In x (A ++ B) -> ~ In x A.
Proof. intros A B x H Hin. apply H. apply in_or_app. left. exact Hin. Qed.

Lemma fresh_notin_app_right : forall (A B : list atom) (x : atom),
  ~ In x (A ++ B) -> ~ In x B.
Proof. intros A B x H Hin. apply H. apply in_or_app. right. exact Hin. Qed.

Definition semantic_environment_ok (rho : atom -> tm -> Prop)
    (Delta : ty_context) : Prop :=
  forall X, candidate_ok (rho X).

Lemma base_candidate_ok : candidate_ok base_candidate.
Proof.
  unfold candidate_ok, base_candidate.
  split.
  - intros t [Hsn Hlc]. exact Hsn.
  - split.
    + intros t [Hsn Hlc]. exact Hlc.
    + split.
      * intros t u [Hsn Hlc] Hs. split.
        -- eapply sn_step; eauto.
        -- eapply lc_step; eauto.
      * intros t Hlc Hnv Hall. split.
        -- constructor. intros u Hu. apply Hall in Hu. exact (proj1 Hu).
        -- exact Hlc.
Qed.

Lemma erased_candidate_ok : forall P,
  candidate_ok P -> candidate_ok (fun t => locally_closed_tm t /\ P (erase_tm t)).
Proof.
  intros P [Hsn [Hlc [Hstep Hcr3]]]. unfold candidate_ok. split.
  - intros t [Ht Hp]. eapply erase_sn_reflect. eapply Hsn. exact Hp.
  - split.
    + intros t [Ht Hp]. exact Ht.
    + split.
      * intros t u [Ht Hp] Htu. split.
        -- eapply lc_step; eauto.
        -- eapply Hstep; [exact Hp|apply erase_step; exact Htu].
      * intros t Ht Hnv Hall. split; [exact Ht|].
        apply Hcr3.
        -- apply erase_preserves_lc. exact Ht.
        -- intro Hv. apply Hnv. eapply erase_value_reflect; eauto.
        -- intros q Hq.
           destruct (erase_step_reflect t q Ht Hq) as [u [Htu Heq]].
           specialize (Hall u Htu) as [_ Hpu]. rewrite <- Heq. exact Hpu.
Qed.

Lemma tapp_nonvalue : forall t T, ~ value (tm_tapp t T).
Proof.
  intros t T H. inversion H; subst; try discriminate.
  match goal with Hn : numeric_value (tm_tapp _ _) |- _ => inversion Hn end.
Qed.

Lemma app_nonvalue : forall t u, ~ value (tm_app t u).
Proof.
  intros t u H. inversion H; subst; try discriminate.
  match goal with Hn : numeric_value (tm_app _ _) |- _ => inversion Hn end.
Qed.

Lemma rec_nonvalue : forall n b s, ~ value (tm_natrec n b s).
Proof.
  intros n b s H. inversion H; subst; try discriminate.
  match goal with Hnum : numeric_value (tm_natrec _ _ _) |- _ => inversion Hnum end.
Qed.

Lemma semantic_type_candidate : forall T rho bound Delta,
  semantic_environment_ok rho Delta -> Forall candidate_ok bound ->
  candidate_ok (semantic_type rho bound T).
Proof.
  induction T; intros rho bound Delta Henv Hbound; simpl.
  - destruct (Nat.lt_ge_cases n (length bound)) as [Hin|Hout].
    + apply erased_candidate_ok. rewrite Forall_forall in Hbound.
      apply Hbound. apply nth_In. lia.
    + rewrite nth_overflow by lia. apply erased_candidate_ok, base_candidate_ok.
  - apply erased_candidate_ok. apply Henv.
  - unfold candidate_ok. split.
    + intros t [Hsn [Hlc Hfun]]. eapply erase_sn_reflect. exact Hsn.
    + split.
      * intros t [Hsn [Hlc Hfun]]. exact Hlc.
      * split.
        -- intros t u [Hsn [Hlc Hfun]] Hstep. split.
           ++ eapply sn_step; [exact Hsn|apply erase_step; exact Hstep].
           ++ split; [eapply lc_step; eauto|]. intros v Hv.
              pose proof (Hfun v Hv) as HB.
              apply (proj1 (proj2 (proj2 (IHT2 rho bound Delta Henv Hbound))))
                with (t := tm_app (erase_tm t) (erase_tm v))
                     (u := tm_app (erase_tm u) (erase_tm v)); auto.
              apply ST_App1; [apply erase_step; exact Hstep|].
              apply erase_preserves_lc.
              exact (proj1 (proj2 (IHT1 rho bound Delta Henv Hbound)) v Hv).
        -- intros t Hlc Hnv Hall. split.
           ++ constructor. intros q Hq.
              destruct (erase_step_reflect t q Hlc Hq) as [t' [Hred Heq]].
              rewrite <- Heq. exact (proj1 (Hall t' Hred)).
           ++ split; [exact Hlc|]. intros v Hv.
              assert (Hne : ~ value (erase_tm t)).
              { intro Hv'. apply Hnv. eapply erase_value_reflect; eauto. }
              apply (proj2 (proj2 (proj2 (IHT2 rho bound Delta Henv Hbound)))).
              ** apply lc_app.
                 --- apply erase_preserves_lc; exact Hlc.
                 --- apply erase_preserves_lc.
                     exact (proj1 (proj2 (IHT1 rho bound Delta Henv Hbound)) v Hv).
              ** apply app_nonvalue.
              ** intros w Hw. inversion Hw; subst.
                 --- exfalso. apply Hne.
                     match goal with
                     | Heq : tm_abs ?A ?b = erase_tm t,
                       Habs : locally_closed_tm (tm_abs ?A ?b) |- _ =>
                         rewrite <- Heq; apply v_abs; exact Habs
                     end.
                 --- destruct (erase_step_reflect t t1' Hlc H1) as [t' [Hraw Heq]].
                     pose proof (Hall t' Hraw) as Hnext.
                     pose proof (proj2 (proj2 Hnext) v Hv) as Hout.
                     rewrite Heq in Hout. exact Hout.
                 --- exfalso. apply Hne. eassumption.
  - unfold candidate_ok. split.
    + intros t [Hsn [Hlc Hfun]]. eapply erase_sn_reflect. exact Hsn.
    + split.
      * intros t [Hsn [Hlc Hfun]]. exact Hlc.
      * split.
        -- intros t u [Hsn [Hlc Hfun]] Hstep. split.
           ++ eapply sn_step; [exact Hsn|apply erase_step; exact Hstep].
           ++ split; [eapply lc_step; eauto|]. intros P HP.
              pose proof (Hfun P HP) as HB.
              apply (proj1 (proj2 (proj2
                (IHT rho (P :: bound) Delta Henv (Forall_cons P HP Hbound)))))
                with (t := tm_tapp (erase_tm t) Ty_Nat)
                     (u := tm_tapp (erase_tm u) Ty_Nat); auto.
              apply ST_TApp; [apply erase_step; exact Hstep|apply lc_ty_nat].
        -- intros t Hlc Hnv Hall. split.
           ++ constructor. intros q Hq.
              destruct (erase_step_reflect t q Hlc Hq) as [t' [Hred Heq]].
              rewrite <- Heq. exact (proj1 (Hall t' Hred)).
           ++ split; [exact Hlc|]. intros P HP.
              assert (Hne : ~ value (erase_tm t)).
              { intro Hv'. apply Hnv. eapply erase_value_reflect; eauto. }
              pose proof (IHT rho (P :: bound) Delta Henv
                (Forall_cons P HP Hbound)) as Hbodyok.
              apply (proj2 (proj2 (proj2 Hbodyok))).
              ** apply lc_tapp; [apply erase_preserves_lc; exact Hlc|apply lc_ty_nat].
              ** apply tapp_nonvalue.
              ** intros w Hw. inversion Hw; subst.
                 --- exfalso. apply Hne.
                     match goal with
                     | Heq : tm_tabs ?b = erase_tm t,
                       Htabs : locally_closed_tm (tm_tabs ?b) |- _ =>
                         rewrite <- Heq; apply v_tabs; exact Htabs
                     end.
                 --- destruct (erase_step_reflect t t' Hlc H1) as [tnew [Hraw Heq]].
                     pose proof (Hall tnew Hraw) as Hnext.
                     pose proof (proj2 (proj2 Hnext) P HP) as Hout.
                     rewrite Heq in Hout. exact Hout.
  - unfold candidate_ok. split.
    + intros t [Hsn Hlc]. eapply erase_sn_reflect. exact Hsn.
    + split.
      * intros t [Hsn Hlc]. exact Hlc.
      * split.
        -- intros t u [Hsn Hlc] Hstep. split.
           ++ eapply sn_step; [exact Hsn|apply erase_step; exact Hstep].
           ++ eapply lc_step; eauto.
        -- intros t Hlc Hnv Hall. split.
           ++ constructor. intros q Hq.
              destruct (erase_step_reflect t q Hlc Hq) as [t' [Hred Heq]].
              rewrite <- Heq. exact (proj1 (Hall t' Hred)).
           ++ exact Hlc.
Qed.

Lemma numeric_semantic_nat : forall rho bound n,
  numeric_value n -> semantic_type rho bound Ty_Nat n.
Proof.
  intros rho bound n Hn. split.
  - apply numeric_strongly_normalizing. exact (erase_numeric_forward n Hn).
  - apply numeric_value_lc. exact Hn.
Qed.

Lemma semantic_natrec_numeric : forall T rho bound Delta n,
  semantic_environment_ok rho Delta -> Forall candidate_ok bound ->
  numeric_value n -> forall b s,
  semantic_type rho bound T b ->
  semantic_type rho bound (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  semantic_type rho bound T (tm_natrec n b s).
Proof.
  intros T rho bound Delta n Henv Hbnd Hnum.
  assert (HcandT : candidate_ok (semantic_type rho bound T)).
  { eapply semantic_type_candidate; eauto. }
  assert (HcandS : candidate_ok
    (semantic_type rho bound (Ty_Arrow Ty_Nat (Ty_Arrow T T)))).
  { eapply semantic_type_candidate; eauto. }
  destruct HcandT as [HsnT [HlcT [HstepT Hcr3T]]].
  destruct HcandS as [HsnS [HlcS [HstepS Hcr3S]]].
  induction Hnum as [|n Hn IHn]; intros b s Hb Hs.
  - pose proof (HsnT b Hb) as Hsn_b.
    revert s Hb Hs.
    apply (sn_induction
      (fun b0 => forall s0, semantic_type rho bound T b0 ->
        semantic_type rho bound (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s0 ->
        semantic_type rho bound T (tm_natrec tm_zero b0 s0)) b Hsn_b).
    intros b0 IHb sout Hb0 Hsout.
    pose proof (HsnS sout Hsout) as Hsn_s.
    revert Hsout.
    apply (sn_induction
      (fun s1 => semantic_type rho bound (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s1 ->
        semantic_type rho bound T (tm_natrec tm_zero b0 s1)) sout Hsn_s).
    intros s0 IHs Hs0.
        apply Hcr3T.
        -- apply lc_tm_rec; [apply numeric_value_lc; constructor|exact (HlcT b0 Hb0)|exact (HlcS s0 Hs0)].
        -- apply rec_nonvalue.
        -- intros u Hu. inversion Hu; subst.
           ++ exfalso. eapply numeric_no_step; eauto using nv_zero.
           ++ match goal with Hred : b0 --> ?b' |- _ =>
                exact (IHb b' Hred s0 (HstepT b0 b' Hb0 Hred) Hs0)
              end.
           ++ match goal with Hred : s0 --> ?s' |- _ =>
                exact (IHs s' Hred (HstepS s0 s' Hs0 Hred))
              end.
           ++ exact Hb0.
  - pose proof (HsnT b Hb) as Hsn_b.
    revert s Hb Hs.
    apply (sn_induction
      (fun b0 => forall s0, semantic_type rho bound T b0 ->
        semantic_type rho bound (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s0 ->
        semantic_type rho bound T (tm_natrec (tm_succ n) b0 s0)) b Hsn_b).
    intros b0 IHb sout Hb0 Hsout.
    pose proof (HsnS sout Hsout) as Hsn_s.
    revert Hsout.
    apply (sn_induction
      (fun s1 => semantic_type rho bound (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s1 ->
        semantic_type rho bound T (tm_natrec (tm_succ n) b0 s1)) sout Hsn_s).
    intros s0 IHs Hs0.
        apply Hcr3T.
        -- apply lc_tm_rec; [apply numeric_value_lc; constructor; exact Hn|exact (HlcT b0 Hb0)|exact (HlcS s0 Hs0)].
        -- apply rec_nonvalue.
        -- intros u Hu. inversion Hu; subst.
           ++ exfalso. match goal with Hred : tm_succ n --> ?q |- _ =>
                exact (numeric_no_step (tm_succ n) (nv_succ n Hn) q Hred)
              end.
           ++ match goal with Hred : b0 --> ?b' |- _ =>
                exact (IHb b' Hred s0 (HstepT b0 b' Hb0 Hred) Hs0)
              end.
           ++ match goal with Hred : s0 --> ?s' |- _ =>
                exact (IHs s' Hred (HstepS s0 s' Hs0 Hred))
              end.
           ++ pose proof (numeric_semantic_nat rho bound n Hn) as Hpred.
              pose proof (IHn b0 s0 Hb0 Hs0) as Htail.
              pose proof (HlcS s0 Hs0) as Hlc_s.
              destruct Hs0 as [_ [_ Happly]].
              specialize (Happly n Hpred) as Hfunction.
              destruct Hfunction as [_ [_ Happly2]].
              pose proof (Happly2 (tm_natrec n b0 s0) Htail) as Hrawout.
              eapply semantic_erasure_extensional with
                (t := tm_app
                  (erase_tm (tm_app (erase_tm s0) (erase_tm n)))
                  (erase_tm (tm_natrec n b0 s0)))
                (u := tm_app (tm_app s0 n) (tm_natrec n b0 s0)).
              * simpl. rewrite !erase_tm_idempotent. reflexivity.
              * apply semantic_type_lc with (T := T) (rho := rho) (bound := bound).
                exact Hrawout.
              * unfold locally_closed_tm. apply lc_tm_app.
                { eapply lc_tm_app.
                  - exact Hlc_s.
                  - apply numeric_value_lc. exact Hn. }
                { eapply lc_tm_rec.
                  - apply numeric_value_lc. exact Hn.
                  - exact (HlcT b0 Hb0).
                  - exact Hlc_s. }
              * exact Hrawout.
Qed.

Lemma semantic_natrec_succ_contract : forall T rho bound Delta n b s,
  semantic_environment_ok rho Delta -> Forall candidate_ok bound ->
  numeric_value n ->
  semantic_type rho bound T b ->
  semantic_type rho bound (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  semantic_type rho bound T (tm_natrec n b s) ->
  semantic_type rho bound T
    (tm_app (tm_app s n) (tm_natrec n b s)).
Proof.
  intros T rho bound Delta n b s Henv Hbound Hn Hb Hs Htail.
  pose proof (numeric_semantic_nat rho bound n Hn) as Hpred.
  pose proof (semantic_type_lc _ _ _ _ Hs) as Hlc_s.
  destruct Hs as [_ [_ Happly]].
  specialize (Happly n Hpred) as Hfunction.
  destruct Hfunction as [_ [_ Happly2]].
  pose proof (Happly2 (tm_natrec n b s) Htail) as Hrawout.
  eapply semantic_erasure_extensional with
    (t := tm_app (erase_tm (tm_app (erase_tm s) (erase_tm n)))
                 (erase_tm (tm_natrec n b s)))
    (u := tm_app (tm_app s n) (tm_natrec n b s)).
  - simpl. rewrite !erase_tm_idempotent. reflexivity.
  - eapply semantic_type_lc; eauto.
  - unfold locally_closed_tm. apply lc_tm_app.
    + apply lc_tm_app.
      * exact Hlc_s.
      * apply numeric_value_lc; exact Hn.
    + apply lc_tm_rec.
      * apply numeric_value_lc; exact Hn.
      * exact (semantic_type_lc _ _ _ _ Hb).
      * exact Hlc_s.
  - exact Hrawout.
Qed.

Lemma semantic_natrec : forall T rho bound Delta n b s,
  semantic_environment_ok rho Delta -> Forall candidate_ok bound ->
  semantic_type rho bound Ty_Nat n ->
  semantic_type rho bound T b ->
  semantic_type rho bound (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  semantic_type rho bound T (tm_natrec n b s).
Proof.
  intros T rho bound Delta n b s Henv Hbound Hn Hb Hs.
  assert (HcandN : candidate_ok (semantic_type rho bound Ty_Nat))
    by (eapply semantic_type_candidate; eauto).
  assert (HcandT : candidate_ok (semantic_type rho bound T))
    by (eapply semantic_type_candidate; eauto).
  assert (HcandS : candidate_ok
    (semantic_type rho bound (Ty_Arrow Ty_Nat (Ty_Arrow T T))))
    by (eapply semantic_type_candidate; eauto).
  destruct HcandN as [HsnN [HlcN [HstepN Hcr3N]]].
  destruct HcandT as [HsnT [HlcT [HstepT Hcr3T]]].
  destruct HcandS as [HsnS [HlcS [HstepS Hcr3S]]].
  pose proof (HsnN n Hn) as Hsn_n.
  revert b s Hb Hs Hn.
  apply (sn_induction
    (fun n0 => forall b0 s0,
      semantic_type rho bound T b0 ->
      semantic_type rho bound (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s0 ->
      semantic_type rho bound Ty_Nat n0 ->
      semantic_type rho bound T (tm_natrec n0 b0 s0)) n Hsn_n).
  intros n0 IHn b0 s0 Hb0 Hs0 Hn0.
  pose proof (HsnT b0 Hb0) as Hsn_b.
  revert s0 Hb0 Hs0 Hn0.
  apply (sn_induction
    (fun b1 => forall s1,
      semantic_type rho bound T b1 ->
      semantic_type rho bound (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s1 ->
      semantic_type rho bound Ty_Nat n0 ->
      semantic_type rho bound T (tm_natrec n0 b1 s1)) b0 Hsn_b).
  intros b1 IHb s1 Hb1 Hs1 Hn1.
  pose proof (HsnS s1 Hs1) as Hsn_s.
  revert Hs1 Hn1.
  apply (sn_induction
    (fun s2 => semantic_type rho bound (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s2 ->
      semantic_type rho bound Ty_Nat n0 ->
      semantic_type rho bound T (tm_natrec n0 b1 s2)) s1 Hsn_s).
  intros s2 IHs Hs2 Hn2.
  apply Hcr3T.
  - apply lc_tm_rec; [exact (HlcN n0 Hn2)|exact (HlcT b1 Hb1)|exact (HlcS s2 Hs2)].
  - apply rec_nonvalue.
  - intros u Hu. inversion Hu; subst.
    + match goal with Hred : n0 --> ?n' |- _ =>
        exact (IHn n' Hred b1 s2 Hb1 Hs2 (HstepN n0 n' Hn2 Hred))
      end.
    + match goal with Hred : b1 --> ?b' |- _ =>
        exact (IHb b' Hred s2 (HstepT b1 b' Hb1 Hred) Hs2 Hn2)
      end.
    + match goal with Hred : s2 --> ?s' |- _ =>
        exact (IHs s' Hred (HstepS s2 s' Hs2 Hred) Hn2)
      end.
    + exact Hb1.
    + match goal with
      | Hnv : numeric_value ?p |- _ =>
          let Htail := fresh "Htail" in
          pose proof (semantic_natrec_numeric T rho bound Delta p Henv Hbound Hnv b1 s2 Hb1 Hs2) as Htail;
          exact (semantic_natrec_succ_contract T rho bound Delta p b1 s2 Henv Hbound Hnv Hb1 Hs2 Htail)
      end.
Qed.

Theorem fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall rho bound gamma,
    semantic_environment_ok rho Delta ->
    Forall candidate_ok bound ->
    term_environment_ok rho bound Gamma gamma ->
    term_substitution_closed gamma ->
    semantic_type rho bound T (instantiate identity_type_substitution gamma t).
Proof.
  intros Delta Gamma t T Hty. induction Hty;
    intros rho bound gamma Henv Hbound Hterm Hgamma.
  - apply Hterm with (x := x). exact H.
  - simpl. split.
    + constructor. intros q Hq. inversion Hq.
    + split.
      * eapply (instantiate_locally_closed (tm_abs T1 t2) gamma).
        -- eapply has_type_locally_closed. econstructor; eauto.
        -- exact Hgamma.
      * intros v Hv. set (x := fresh (L ++ fv_tm t2)).
        assert (Hx : ~ In x (L ++ fv_tm t2)) by (unfold x; apply fresh_notin).
        assert (HxL : ~ In x L) by (eapply fresh_notin_app_left; exact Hx).
        assert (Hxbody : ~ In x (fv_tm t2)) by (eapply fresh_notin_app_right; exact Hx).
        assert (Hdepth : lc_tm_at 0 1 t2).
        { eapply lc_tm_at_open_tm_inv with (x := x).
          exact (has_type_locally_closed _ _ _ _ (H0 x HxL)). }
        assert (Hdepthinst : lc_tm_at 0 1 (instantiate identity_type_substitution gamma t2)).
        { eapply instantiate_lc_at; eauto. }
        assert (Hbody : forall w, semantic_type rho bound T1 w ->
          semantic_type rho bound T2
            (open_tm (instantiate identity_type_substitution gamma t2) w)).
        { intros w Hw.
          set (gammaw := term_subst_update gamma x w).
          assert (Htermw : term_environment_ok rho bound (update Gamma x T1) gammaw).
          { unfold gammaw. eapply term_environment_update; eauto. }
          assert (Hgammaw : term_substitution_closed gammaw).
          { unfold gammaw. eapply term_subst_update_closed; eauto.
            exact (semantic_type_lc _ _ _ _ Hw). }
          specialize (H1 x HxL rho bound gammaw Henv Hbound Htermw Hgammaw) as HB.
          assert (Eopen : instantiate identity_type_substitution gammaw
              (open_tm t2 (tm_fvar x)) =
            open_tm (instantiate identity_type_substitution gamma t2) w).
          { unfold gammaw, open_tm. apply instantiate_open_tm_rec; assumption. }
          assert (HtargetLC : locally_closed_tm
            (open_tm (instantiate identity_type_substitution gamma t2) w)).
          { unfold locally_closed_tm. eapply open_tm_preserves_lc_at.
            - exact Hdepthinst.
            - exact (semantic_type_lc _ _ _ _ Hw). }
          eapply semantic_erasure_extensional with
            (t := instantiate identity_type_substitution gammaw
              (open_tm t2 (tm_fvar x)))
            (u := open_tm (instantiate identity_type_substitution gamma t2) w).
          - rewrite Eopen, erase_open_tm. reflexivity.
          - exact (semantic_type_lc _ _ _ _ HB).
          - exact HtargetLC.
          - exact HB. }
        pose proof (semantic_type_candidate T1 rho bound Delta Henv Hbound) as HcandA.
        destruct HcandA as [HsnA [HlcA [HstepA _]]].
        assert (Hsnv : strongly_normalizing v) by (apply HsnA; exact Hv).
        assert (Happlication : semantic_type rho bound T1 v ->
          semantic_type rho bound T2
            (tm_app (erase_tm (instantiate identity_type_substitution gamma
              (tm_abs T1 t2))) (erase_tm v))).
        { apply (sn_induction
          (fun a => semantic_type rho bound T1 a ->
             semantic_type rho bound T2
               (tm_app (erase_tm (instantiate identity_type_substitution gamma
                    (tm_abs T1 t2))) (erase_tm a))) v Hsnv).
        intros a IH Ha.
        pose proof (semantic_type_candidate T2 rho bound Delta Henv Hbound) as HcandB.
        destruct HcandB as [_ [_ [_ Hcr3B]]].
        assert (HappLC : locally_closed_tm
          (tm_app (erase_tm (instantiate identity_type_substitution gamma
              (tm_abs T1 t2))) (erase_tm a))).
        { apply lc_app.
          - apply erase_preserves_lc. eapply (instantiate_locally_closed (tm_abs T1 t2) gamma).
            + eapply has_type_locally_closed. econstructor; eauto.
            + exact Hgamma.
          - apply erase_preserves_lc. exact (semantic_type_lc _ _ _ _ Ha). }
        apply Hcr3B; [exact HappLC|apply app_nonvalue|].
        intros q Hstep. inversion Hstep; subst.
        -- assert (HargErase : semantic_type rho bound T1 (erase_tm a)).
           { eapply semantic_erasure_extensional with (t := a) (u := erase_tm a).
             - symmetry. apply erase_tm_idempotent.
             - exact (semantic_type_lc _ _ _ _ Ha).
             - apply erase_preserves_lc. exact (semantic_type_lc _ _ _ _ Ha).
             - exact Ha. }
           pose proof (Hbody (erase_tm a) HargErase) as HBeta.
           eapply semantic_erasure_extensional with
             (t := open_tm (instantiate identity_type_substitution gamma t2) (erase_tm a))
             (u := open_tm (erase_tm (instantiate identity_type_substitution gamma t2)) (erase_tm a)).
           ++ rewrite !erase_open_tm. rewrite !erase_tm_idempotent. reflexivity.
           ++ exact (semantic_type_lc _ _ _ _ HBeta).
           ++ eapply lc_step with
                (t := tm_app (erase_tm (instantiate identity_type_substitution gamma
                    (tm_abs T1 t2))) (erase_tm a)); eauto.
           ++ exact HBeta.
        -- match goal with Hinner : step (tm_abs _ _) _ |- _ => inversion Hinner end.
        -- destruct (erase_step_reflect a t2'
             (semantic_type_lc _ _ _ _ Ha) H6) as [araw [Hraw Herase]].
           assert (Hrawsem : semantic_type rho bound T1 araw)
             by (eapply HstepA; eauto).
           pose proof (IH araw Hraw Hrawsem) as Hrecursive.
           rewrite Herase in Hrecursive. exact Hrecursive. }
        exact (Happlication Hv).
  - simpl. pose proof (IHHty1 rho bound gamma Henv Hbound Hterm Hgamma) as Hf.
    pose proof (IHHty2 rho bound gamma Henv Hbound Hterm Hgamma) as Ha.
    destruct Hf as [_ [_ Happly]].
    pose proof (Happly (instantiate identity_type_substitution gamma t2) Ha) as Hout.
    eapply semantic_erasure_extensional with
      (t := tm_app (erase_tm (instantiate identity_type_substitution gamma t1))
                   (erase_tm (instantiate identity_type_substitution gamma t2)))
      (u := instantiate identity_type_substitution gamma (tm_app t1 t2)).
    + simpl. rewrite !erase_tm_idempotent. reflexivity.
    + exact (semantic_type_lc _ _ _ _ Hout).
    + eapply (instantiate_locally_closed (tm_app t1 t2) gamma).
      * eapply has_type_locally_closed. econstructor; eauto.
      * exact Hgamma.
    + exact Hout.
  - simpl. split.
    + constructor. intros q Hq. inversion Hq.
    + split.
      * eapply (instantiate_locally_closed (tm_tabs t) gamma).
        -- eapply has_type_locally_closed. econstructor; eauto.
        -- exact Hgamma.
      * intros P HP.
        set (X := fresh (L ++ ftv_context Gamma ++ fv_ty T)).
        assert (HX : ~ In X (L ++ ftv_context Gamma ++ fv_ty T))
          by (unfold X; apply fresh_notin).
        assert (HXL : ~ In X L).
        { intro Hin. apply HX. apply in_or_app. left. exact Hin. }
        assert (HXctx : ~ In X (ftv_context Gamma)).
        { intro Hin. apply HX. apply in_or_app. right. apply in_or_app. left. exact Hin. }
        assert (HXty : ~ In X (fv_ty T)).
        { intro Hin. apply HX. apply in_or_app. right. apply in_or_app. right. exact Hin. }
        set (rho' := semantic_rho_update rho X P).
        assert (Henv' : semantic_environment_ok rho' (X :: Delta)).
        { intros Y. unfold rho'. unfold semantic_rho_update.
          destruct (Nat.eqb X Y) eqn:E.
          - apply Nat.eqb_eq in E. subst. exact HP.
          - apply Henv. }
        assert (Hterm' : term_environment_ok rho' bound Gamma gamma).
        { unfold rho'. eapply term_environment_rho_update; eauto. }
        specialize (H0 X HXL rho' bound gamma Henv' Hbound Hterm' Hgamma) as HB.
        pose proof (has_type_result_locally_closed _ _ _ _ (T_TAbs L Delta Gamma t T H)) as Hresult.
        inversion Hresult; subst.
        assert (HErased : erase_tm
            (instantiate identity_type_substitution gamma
              (open_tm_ty t (Ty_FVar X))) =
          erase_tm (instantiate identity_type_substitution gamma t)).
        { rewrite !erase_instantiate, erase_open_tm_ty. reflexivity. }
        set (tabsapp := tm_tapp
          (erase_tm (instantiate identity_type_substitution gamma (tm_tabs t))) Ty_Nat).
        assert (HtabsappLC : locally_closed_tm tabsapp).
        { unfold tabsapp. apply lc_tapp.
          - apply erase_preserves_lc. eapply (instantiate_locally_closed (tm_tabs t) gamma).
            + eapply has_type_locally_closed. econstructor; eauto.
            + exact Hgamma.
          - apply lc_ty_nat. }
        assert (Hbodyapp : semantic_type rho' bound (open_ty T (Ty_FVar X)) tabsapp).
        { pose proof (semantic_type_candidate (open_ty T (Ty_FVar X)) rho' bound
              (X :: Delta) Henv' Hbound) as HcandOpen.
          destruct HcandOpen as [_ [_ [_ Hcr3Open]]].
          apply Hcr3Open; [exact HtabsappLC|apply tapp_nonvalue|].
          intros q Hstep. inversion Hstep; subst.
          + eapply semantic_erasure_extensional with
              (t := instantiate identity_type_substitution gamma
                (open_tm_ty t (Ty_FVar X)))
              (u := open_tm_ty (erase_tm (instantiate identity_type_substitution gamma t)) Ty_Nat).
            - rewrite HErased, erase_open_tm_ty, erase_tm_idempotent. reflexivity.
            - exact (semantic_type_lc _ _ _ _ HB).
            - eapply lc_step with (t := tabsapp). exact HtabsappLC. assumption.
            - exact HB.
          + match goal with Hinner : step (tm_tabs _) _ |- _ => inversion Hinner end. }
        assert (HQcand : candidate_ok
          (semantic_type rho' bound (Ty_FVar X))).
        { eapply semantic_type_candidate; eauto. }
        assert (Hinsert : semantic_type rho' (semantic_type rho' bound (Ty_FVar X) :: bound)
            T tabsapp).
        { apply (proj1 (semantic_open_ty_rec T rho' [] bound 0
            (Ty_FVar X) tabsapp eq_refl H3 (@lc_ty_fvar 0 X) HtabsappLC)).
          exact Hbodyapp. }
        assert (HinsertP : semantic_type rho' (P :: bound) T tabsapp).
        { eapply (proj1 (semantic_candidate_insert_equiv T rho' bound P
            (semantic_type rho' bound (Ty_FVar X)) tabsapp HP)).
          - intros e Hle Herase. simpl. unfold rho', semantic_rho_update.
            rewrite Nat.eqb_refl. rewrite Herase. tauto.
          - exact H3.
          - exact HtabsappLC.
          - exact Hinsert. }
        apply (proj2 (semantic_rho_update_notin T rho X P (P :: bound)
          tabsapp HXty)). exact HinsertP.
  - simpl. pose proof (H0 rho bound gamma Henv Hbound Hterm Hgamma) as Hpoly.
    pose proof (semantic_type_candidate U rho bound Delta Henv Hbound) as HcandU.
    set (P := semantic_type rho bound U).
    specialize (Hpoly P HcandU) as Hopened.
    pose proof (has_type_result_locally_closed _ _ _ _ (T_TApp Delta Gamma t T U H0 H)) as Hresult.
    inversion Hresult; subst.
    assert (HtermLC : locally_closed_tm
      (instantiate identity_type_substitution gamma (tm_tapp t U))).
    { eapply (instantiate_locally_closed (tm_tapp t U) gamma).
      - eapply has_type_locally_closed. econstructor; eauto.
      - exact Hgamma. }
    assert (Hbody : semantic_type rho (P :: bound) T
      (instantiate identity_type_substitution gamma (tm_tapp t U))).
    { eapply semantic_erasure_extensional with
        (t := tm_tapp (erase_tm (instantiate identity_type_substitution gamma t)) Ty_Nat)
        (u := instantiate identity_type_substitution gamma (tm_tapp t U)).
      - simpl. rewrite !erase_tm_idempotent. reflexivity.
      - exact (semantic_type_lc _ _ _ _ Hopened).
      - exact HtermLC.
      - exact Hopened. }
    apply (proj2 (semantic_open_ty_rec T rho [] bound 0 U
      (instantiate identity_type_substitution gamma (tm_tapp t U))
      eq_refl H1 (wf_ty_locally_closed _ _ H) HtermLC)).
    exact Hbody.
  - simpl. split.
    + constructor. intros q Hq. inversion Hq.
    + split; [apply lc_tm_zero|].
      eapply numeric_semantic_nat. constructor.
  - simpl. pose proof (H0 rho bound gamma Henv Hbound Hterm Hgamma) as Hn.
    split.
    + destruct Hn as [Hsn _]. simpl. apply sn_succ. exact Hsn.
    + eapply (instantiate_locally_closed (tm_succ n) gamma).
      * eapply has_type_locally_closed. econstructor; eauto.
      * exact Hgamma.
  - simpl. pose proof (H0 rho bound gamma Henv Hbound Hterm Hgamma) as Hn.
    pose proof (H1 rho bound gamma Henv Hbound Hterm Hgamma) as Hb.
    pose proof (H2 rho bound gamma Henv Hbound Hterm Hgamma) as Hs.
    eapply semantic_natrec; eauto.
Qed.


Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  intros t T Hty. induction Hty.
  all: try (constructor; intros u Hstep; inversion Hstep).
Qed.

End SystemFNormalizationRecursionEasyTask.
