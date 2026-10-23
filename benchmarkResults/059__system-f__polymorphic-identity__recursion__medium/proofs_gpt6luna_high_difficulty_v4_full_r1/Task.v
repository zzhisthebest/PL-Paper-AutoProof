(** System F parametricity benchmark, Easy variant.
    Features: recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFParametricityRecursionEasyTask.

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
      evaluates (tm_natrec n b s) result.

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

(* The value relation is indexed by the (possibly open) type.  Universal
   types quantify over an arbitrary relation on values; this is the clause
   that will force the two sides of an identity instantiation to agree. *)
Definition value_relation := tm -> tm -> Prop.

Definition related_eval (R : value_relation) (t u : tm) : Prop :=
  exists v w, t -->* v /\ u -->* w /\ value v /\ value w /\ R v w.

Fixpoint logical_value_relation
    (rho : list value_relation) (phi : atom -> value_relation)
    (T : ty) : value_relation :=
  match T with
  | Ty_BVar i =>
      fun v w => value v /\ value w /\ nth i rho (fun _ _ => False) v w
  | Ty_FVar X => fun v w => value v /\ value w /\ phi X v w
  | Ty_Arrow T1 T2 =>
      fun f g => value f /\ value g /\
        forall a b, logical_value_relation rho phi T1 a b ->
          related_eval (logical_value_relation rho phi T2)
            (tm_app f a) (tm_app g b)
  | Ty_All T1 =>
      fun f g => value f /\ value g /\
        exists fbody gbody,
          f = tm_tabs fbody /\ g = tm_tabs gbody /\
          forall U1 U2 R, locally_closed_ty U1 -> locally_closed_ty U2 ->
            related_eval (logical_value_relation (R :: rho) phi T1)
              (open_tm_ty fbody U1) (open_tm_ty gbody U2)
  | Ty_Nat =>
      fun n m => numeric_value n /\ numeric_value m /\ n = m
  end.

Definition logical_term_relation
    (rho : list value_relation) (phi : atom -> value_relation)
    (T : ty) (t u : tm) : Prop :=
  related_eval (logical_value_relation rho phi T) t u.

Lemma logical_value_relation_values : forall T rho phi v w,
  logical_value_relation rho phi T v w -> value v /\ value w.
Proof.
  induction T; intros rho phi v w H; simpl in H.
  - tauto.
  - tauto.
  - tauto.
  - tauto.
  - destruct H as [Hn [Hm Heq]]. split; apply v_nat; assumption.
Qed.

Definition phi_update (phi : atom -> value_relation) (X : atom)
    (R : value_relation) : atom -> value_relation :=
  fun Y => if Nat.eqb X Y then R else phi Y.

Lemma related_eval_mor : forall R S t u,
  (forall v w, R v w <-> S v w) ->
  (related_eval R t u <-> related_eval S t u).
Proof.
  unfold related_eval. intros R S t u H. split;
    intros [v [w [Htv [Huw [Hv [Hw HR]]]]]];
    exists v, w; repeat split; try assumption; apply H; assumption.
Qed.

Lemma nth_app_left' : forall (A : Type) (xs ys : list A) n d,
  n < length xs -> nth n (xs ++ ys) d = nth n xs d.
Proof.
  intros A xs. induction xs; intros ys n d H; simpl in *; [lia|].
  destruct n; simpl; [reflexivity|]. apply IHxs. lia.
Qed.

Lemma nth_app_right' : forall (A : Type) (xs ys : list A) n d,
  nth (length xs + n) (xs ++ ys) d = nth n ys d.
Proof.
  intros A xs. induction xs; intros ys n d; simpl; [reflexivity|].
  replace (S (length xs) + n) with (S (length xs + n)) by lia.
  simpl. apply IHxs.
Qed.

Lemma logical_value_relation_tail_irrelevant : forall T k prefix rho1 rho2 phi,
  length prefix = k -> lc_ty_at k T -> forall v w,
  logical_value_relation (prefix ++ rho1) phi T v w <->
  logical_value_relation (prefix ++ rho2) phi T v w.
Proof.
  induction T; intros k prefix rho1 rho2 phi Hlen Hlc v w; simpl in *.
  - inversion Hlc; subst.
    rewrite (nth_app_left' _ prefix rho1 n (fun _ _ => False) H1).
    rewrite (nth_app_left' _ prefix rho2 n (fun _ _ => False) H1). tauto.
  - tauto.
  - inversion Hlc; subst. simpl. split.
    + intros [Hf [Hg Hrel]]. repeat split; try assumption. intros a b Hab.
      apply (proj2 (IHT1 (length prefix) prefix rho1 rho2 phi eq_refl H2 a b)) in Hab.
      specialize (Hrel a b Hab). eapply related_eval_mor; [|exact Hrel].
      intros x y. symmetry. apply (IHT2 (length prefix) prefix rho1 rho2 phi eq_refl H3 x y).
    + intros [Hf [Hg Hrel]]. repeat split; try assumption. intros a b Hab.
      apply (proj1 (IHT1 (length prefix) prefix rho1 rho2 phi eq_refl H2 a b)) in Hab.
      specialize (Hrel a b Hab). eapply related_eval_mor; [|exact Hrel].
      intros x y. apply (IHT2 (length prefix) prefix rho1 rho2 phi eq_refl H3 x y).
  - inversion Hlc; subst. simpl. split.
    + intros [Hf [Hg [fb [gb [Hfb [Hgb Hbody]]]]]].
      split; [exact Hf|]. split; [exact Hg|]. exists fb, gb.
      repeat split; try assumption.
      intros U1 U2 R HLU1 HLU2.
      assert (Hiff : forall a b,
        logical_value_relation ((R :: prefix) ++ rho1) phi T a b <->
        logical_value_relation ((R :: prefix) ++ rho2) phi T a b).
      { intros a b. apply (IHT (S (length prefix)) (R :: prefix) rho1 rho2 phi).
        - simpl. reflexivity.
        - assumption. }
      exact (proj1 (related_eval_mor _ _ _ _ Hiff) (Hbody U1 U2 R HLU1 HLU2)).
    + intros [Hf [Hg [fb [gb [Hfb [Hgb Hbody]]]]]].
      split; [exact Hf|]. split; [exact Hg|]. exists fb, gb.
      repeat split; try assumption.
      intros U1 U2 R HLU1 HLU2.
      assert (Hiff : forall a b,
        logical_value_relation ((R :: prefix) ++ rho1) phi T a b <->
        logical_value_relation ((R :: prefix) ++ rho2) phi T a b).
      { intros a b. apply (IHT (S (length prefix)) (R :: prefix) rho1 rho2 phi).
        - simpl. reflexivity.
        - assumption. }
      exact (proj2 (related_eval_mor _ _ _ _ Hiff) (Hbody U1 U2 R HLU1 HLU2)).
  - tauto.
Qed.

Lemma logical_value_relation_closed_env : forall T rho1 rho2 phi,
  locally_closed_ty T -> forall v w,
  logical_value_relation rho1 phi T v w <->
  logical_value_relation rho2 phi T v w.
Proof.
  intros T rho1 rho2 phi Hlc v w.
  eapply logical_value_relation_tail_irrelevant with (prefix := []) (k := 0);
    simpl; eauto.
Qed.

Definition relation_equiv (R S : value_relation) : Prop :=
  forall v w, R v w <-> S v w.

Definition relation_env_equiv (rho1 rho2 : list value_relation) : Prop :=
  forall n, relation_equiv (nth n rho1 (fun _ _ => False))
                           (nth n rho2 (fun _ _ => False)).

Lemma relation_env_equiv_cons : forall R1 R2 rho1 rho2,
  relation_equiv R1 R2 -> relation_env_equiv rho1 rho2 ->
  relation_env_equiv (R1 :: rho1) (R2 :: rho2).
Proof.
  intros R1 R2 rho1 rho2 Hhead Htail n. destruct n; simpl.
  - exact Hhead.
  - apply Htail.
Qed.

Lemma relation_env_equiv_insert : forall prefix rho R1 R2,
  relation_equiv R1 R2 ->
  relation_env_equiv (prefix ++ R1 :: rho) (prefix ++ R2 :: rho).
Proof.
  induction prefix; intros rho R1 R2 Hrel n; simpl.
  - destruct n; simpl.
    + exact Hrel.
    + unfold relation_equiv. intros v w. tauto.
  - apply relation_env_equiv_cons.
    + unfold relation_equiv. intros v w. tauto.
    + apply IHprefix. exact Hrel.
Qed.

Lemma logical_value_relation_env_mor : forall T rho1 rho2 phi,
  relation_env_equiv rho1 rho2 -> forall v w,
  logical_value_relation rho1 phi T v w <->
  logical_value_relation rho2 phi T v w.
Proof.
  induction T; intros rho1 rho2 phi Henv v w; simpl.
  - destruct (Henv n v w); tauto.
  - tauto.
  - split.
    + intros [Hf [Hg Hfun]]. repeat split; try assumption. intros a b Hab.
      apply (proj2 (IHT1 rho1 rho2 phi Henv a b)) in Hab.
      specialize (Hfun a b Hab).
      assert (Hiff : forall x y,
        logical_value_relation rho1 phi T2 x y <->
        logical_value_relation rho2 phi T2 x y).
      { intros x y. apply IHT2. exact Henv. }
      exact (proj1 (related_eval_mor _ _ _ _ Hiff) Hfun).
    + intros [Hf [Hg Hfun]]. repeat split; try assumption. intros a b Hab.
      apply (proj1 (IHT1 rho1 rho2 phi Henv a b)) in Hab.
      specialize (Hfun a b Hab).
      assert (Hiff : forall x y,
        logical_value_relation rho1 phi T2 x y <->
        logical_value_relation rho2 phi T2 x y).
      { intros x y. apply IHT2. exact Henv. }
      exact (proj2 (related_eval_mor _ _ _ _ Hiff) Hfun).
  - split.
    + intros [Hf [Hg [fb [gb [Hfb [Hgb Hbody]]]]]].
      split; [exact Hf|]. split; [exact Hg|]. exists fb, gb.
      repeat split; try assumption. intros U1 U2 R HLU1 HLU2.
      assert (Hiff : relation_env_equiv (R :: rho1) (R :: rho2)).
      { apply relation_env_equiv_cons; [unfold relation_equiv; tauto|exact Henv]. }
      assert (Hrel : forall a b,
        logical_value_relation (R :: rho1) phi T a b <->
        logical_value_relation (R :: rho2) phi T a b).
      { intros a b. apply IHT. exact Hiff. }
      exact (proj1 (related_eval_mor _ _ _ _ Hrel)
        (Hbody U1 U2 R HLU1 HLU2)).
    + intros [Hf [Hg [fb [gb [Hfb [Hgb Hbody]]]]]].
      split; [exact Hf|]. split; [exact Hg|]. exists fb, gb.
      repeat split; try assumption. intros U1 U2 R HLU1 HLU2.
      assert (Hiff : relation_env_equiv (R :: rho1) (R :: rho2)).
      { apply relation_env_equiv_cons; [unfold relation_equiv; tauto|exact Henv]. }
      assert (Hrel : forall a b,
        logical_value_relation (R :: rho1) phi T a b <->
        logical_value_relation (R :: rho2) phi T a b).
      { intros a b. apply IHT. exact Hiff. }
      exact (proj2 (related_eval_mor _ _ _ _ Hrel)
        (Hbody U1 U2 R HLU1 HLU2)).
  - tauto.
Qed.

Lemma logical_value_relation_open_ty_closed : forall T k prefix rho phi U,
  length prefix = k ->
  lc_ty_at (S k) T ->
  locally_closed_ty U ->
  forall v w,
  logical_value_relation
      (prefix ++ logical_value_relation (prefix ++ rho) phi U :: rho)
      phi T v w <->
  logical_value_relation (prefix ++ rho) phi
      (open_ty_rec k U T) v w.
Proof.
  induction T; intros k prefix rho phi U Hlen Hlc HU v w; simpl in *.
  - inversion Hlc; subst. destruct (Nat.eqb (length prefix) n) eqn:E.
    + apply Nat.eqb_eq in E. subst n.
      replace (length prefix) with (length prefix + 0) by lia.
      rewrite nth_app_right'. simpl. split.
      * tauto.
      * intro Hrel. pose proof (logical_value_relation_values U (prefix ++ rho) phi v w Hrel).
        tauto.
    + apply Nat.eqb_neq in E. assert (Hnk : n < length prefix) by lia.
      rewrite (nth_app_left' _ prefix
        (logical_value_relation (prefix ++ rho) phi U :: rho)
        n (fun _ _ => False) Hnk).
      change (value v /\ value w /\ nth n prefix (fun _ _ => False) v w <->
        value v /\ value w /\ nth n (prefix ++ rho) (fun _ _ => False) v w).
      rewrite (nth_app_left' _ prefix rho n (fun _ _ => False) Hnk). tauto.
  - tauto.
  - inversion Hlc; subst. simpl. split.
    + intros [Hfv [Hgv Hfun]]. repeat split; try assumption. intros a b Hab.
      apply (proj2 (IHT1 (length prefix) prefix rho phi U eq_refl H2 HU a b)) in Hab.
      specialize (Hfun a b Hab).
      assert (Hiff : forall x y,
        logical_value_relation
          (prefix ++ logical_value_relation (prefix ++ rho) phi U :: rho) phi T2 x y <->
        logical_value_relation (prefix ++ rho) phi
          (open_ty_rec (length prefix) U T2) x y).
      { intros x y. apply (IHT2 (length prefix) prefix rho phi U eq_refl H3 HU x y). }
      exact (proj1 (related_eval_mor _ _ _ _ Hiff) Hfun).
    + intros [Hfv [Hgv Hfun]]. repeat split; try assumption. intros a b Hab.
      apply (proj1 (IHT1 (length prefix) prefix rho phi U eq_refl H2 HU a b)) in Hab.
      specialize (Hfun a b Hab).
      assert (Hiff : forall x y,
        logical_value_relation
          (prefix ++ logical_value_relation (prefix ++ rho) phi U :: rho) phi T2 x y <->
        logical_value_relation (prefix ++ rho) phi
          (open_ty_rec (length prefix) U T2) x y).
      { intros x y. apply (IHT2 (length prefix) prefix rho phi U eq_refl H3 HU x y). }
      exact (proj2 (related_eval_mor _ _ _ _ Hiff) Hfun).
  - inversion Hlc; subst. simpl. split.
    + intros [Hfv [Hgv [fb [gb [Hfb [Hgb Hbody]]]]]].
      split; [exact Hfv|]. split; [exact Hgv|]. exists fb, gb.
      repeat split; try assumption. intros U1 U2 Q HLU1 HLU2.
      set (R0 := logical_value_relation (prefix ++ rho) phi U).
      set (R1 := logical_value_relation ((Q :: prefix) ++ rho) phi U).
      assert (HR : relation_equiv R0 R1).
      { unfold relation_equiv, R0, R1. intros a0 b0.
        eapply logical_value_relation_closed_env; eauto. }
      assert (Henv : relation_env_equiv
        (((Q :: prefix) ++ R0 :: rho)) (((Q :: prefix) ++ R1 :: rho))).
      { apply relation_env_equiv_insert. exact HR. }
      assert (Htail : forall a0 b0,
        logical_value_relation (((Q :: prefix) ++ R0 :: rho)) phi T a0 b0 <->
        logical_value_relation (((Q :: prefix) ++ R1 :: rho)) phi T a0 b0).
      { intros a0 b0. apply logical_value_relation_env_mor. exact Henv. }
      assert (Hopen : forall a0 b0,
        logical_value_relation (((Q :: prefix) ++ R1 :: rho)) phi T a0 b0 <->
        logical_value_relation ((Q :: prefix) ++ rho) phi
          (open_ty_rec (S (length prefix)) U T) a0 b0).
      { intros a0 b0. apply IHT with (k := S (length prefix)).
        - simpl. reflexivity.
        - exact H1.
        - exact HU. }
      assert (Hiff : forall a0 b0,
        logical_value_relation (((Q :: prefix) ++ R0 :: rho)) phi T a0 b0 <->
        logical_value_relation ((Q :: prefix) ++ rho) phi
          (open_ty_rec (S (length prefix)) U T) a0 b0).
      { intros a0 b0. transitivity
          (logical_value_relation (((Q :: prefix) ++ R1 :: rho)) phi T a0 b0).
        - apply Htail.
        - apply Hopen. }
      exact (proj1 (related_eval_mor _ _ _ _ Hiff)
        (Hbody U1 U2 Q HLU1 HLU2)).
    + intros [Hfv [Hgv [fb [gb [Hfb [Hgb Hbody]]]]]].
      split; [exact Hfv|]. split; [exact Hgv|]. exists fb, gb.
      repeat split; try assumption. intros U1 U2 Q HLU1 HLU2.
      set (R0 := logical_value_relation (prefix ++ rho) phi U).
      set (R1 := logical_value_relation ((Q :: prefix) ++ rho) phi U).
      assert (HR : relation_equiv R0 R1).
      { unfold relation_equiv, R0, R1. intros a0 b0.
        eapply logical_value_relation_closed_env; eauto. }
      assert (Henv : relation_env_equiv
        (((Q :: prefix) ++ R0 :: rho)) (((Q :: prefix) ++ R1 :: rho))).
      { apply relation_env_equiv_insert. exact HR. }
      assert (Htail : forall a0 b0,
        logical_value_relation (((Q :: prefix) ++ R0 :: rho)) phi T a0 b0 <->
        logical_value_relation (((Q :: prefix) ++ R1 :: rho)) phi T a0 b0).
      { intros a0 b0. apply logical_value_relation_env_mor. exact Henv. }
      assert (Hopen : forall a0 b0,
        logical_value_relation (((Q :: prefix) ++ R1 :: rho)) phi T a0 b0 <->
        logical_value_relation ((Q :: prefix) ++ rho) phi
          (open_ty_rec (S (length prefix)) U T) a0 b0).
      { intros a0 b0. apply IHT with (k := S (length prefix)).
        - simpl. reflexivity.
        - exact H1.
        - exact HU. }
      assert (Hiff : forall a0 b0,
        logical_value_relation (((Q :: prefix) ++ R0 :: rho)) phi T a0 b0 <->
        logical_value_relation ((Q :: prefix) ++ rho) phi
          (open_ty_rec (S (length prefix)) U T) a0 b0).
      { intros a0 b0. transitivity
          (logical_value_relation (((Q :: prefix) ++ R1 :: rho)) phi T a0 b0).
        - apply Htail.
        - apply Hopen. }
      exact (proj2 (related_eval_mor _ _ _ _ Hiff)
        (Hbody U1 U2 Q HLU1 HLU2)).
  - inversion Hlc. tauto.
Qed.

Lemma logical_value_relation_open_ty_rec : forall T k prefix rho phi X R,
  length prefix = k -> lc_ty_at (S k) T -> ~ In X (fv_ty T) -> forall v w,
  logical_value_relation (prefix ++ R :: rho) phi T v w <->
  logical_value_relation (prefix ++ rho) (phi_update phi X R)
    (open_ty_rec k (Ty_FVar X) T) v w.
Proof.
  induction T; intros k prefix rho phi X R Hlen Hlc Hfresh v w; simpl in *.
  - inversion Hlc; subst. destruct (Nat.eqb (length prefix) n) eqn:E.
    + apply Nat.eqb_eq in E. subst n.
      replace (length prefix) with (length prefix + 0) by lia.
      rewrite nth_app_right'. simpl. unfold phi_update. rewrite Nat.eqb_refl. tauto.
    + apply Nat.eqb_neq in E. assert (Hnk : n < length prefix) by lia.
      rewrite (nth_app_left' _ prefix (R :: rho) n (fun _ _ => False) Hnk).
      change (value v /\ value w /\ nth n prefix (fun _ _ => False) v w <->
        value v /\ value w /\ nth n (prefix ++ rho) (fun _ _ => False) v w).
      rewrite (nth_app_left' _ prefix rho n (fun _ _ => False) Hnk). tauto.
  - unfold phi_update. destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E. subst a. exfalso. apply Hfresh. simpl. auto.
    + tauto.
  - inversion Hlc; subst. simpl. split.
    + intros [Hf [Hg Hrel]]. repeat split; try assumption. intros a0 b0 Hab.
      assert (Hf1 : ~ In X (fv_ty T1)).
      { intro Hin. apply Hfresh. simpl. apply in_or_app. left; exact Hin. }
      assert (Hf2 : ~ In X (fv_ty T2)).
      { intro Hin. apply Hfresh. simpl. apply in_or_app. right; exact Hin. }
      apply (proj2 (IHT1 (length prefix) prefix rho phi X R eq_refl H2 Hf1 a0 b0)) in Hab.
      specialize (Hrel a0 b0 Hab).
      assert (Hiff : forall x y,
        logical_value_relation (prefix ++ R :: rho) phi T2 x y <->
        logical_value_relation (prefix ++ rho) (phi_update phi X R)
          (open_ty_rec (length prefix) (Ty_FVar X) T2) x y).
      { intros x y.
        apply (IHT2 (length prefix) prefix rho phi X R eq_refl H3 Hf2 x y). }
      exact (proj1 (related_eval_mor _ _ _ _ Hiff) Hrel).
    + intros [Hf [Hg Hrel]]. repeat split; try assumption. intros a0 b0 Hab.
      assert (Hf1 : ~ In X (fv_ty T1)).
      { intro Hin. apply Hfresh. simpl. apply in_or_app. left; exact Hin. }
      assert (Hf2 : ~ In X (fv_ty T2)).
      { intro Hin. apply Hfresh. simpl. apply in_or_app. right; exact Hin. }
      apply (proj1 (IHT1 (length prefix) prefix rho phi X R eq_refl H2 Hf1 a0 b0)) in Hab.
      specialize (Hrel a0 b0 Hab).
      assert (Hiff : forall x y,
        logical_value_relation (prefix ++ R :: rho) phi T2 x y <->
        logical_value_relation (prefix ++ rho) (phi_update phi X R)
          (open_ty_rec (length prefix) (Ty_FVar X) T2) x y).
      { intros x y.
        apply (IHT2 (length prefix) prefix rho phi X R eq_refl H3 Hf2 x y). }
      exact (proj2 (related_eval_mor _ _ _ _ Hiff) Hrel).
  - inversion Hlc; subst. simpl. split.
    + intros [Hf [Hg [fb [gb [Hfb [Hgb Hbody]]]]]].
      split; [exact Hf|]. split; [exact Hg|]. exists fb, gb.
      repeat split; try assumption.
      intros U1 U2 Q HLU1 HLU2.
      assert (Hf1 : ~ In X (fv_ty T)).
      { exact Hfresh. }
      assert (Hiff : forall a0 b0,
        logical_value_relation (Q :: prefix ++ R :: rho) phi T a0 b0 <->
        logical_value_relation (Q :: prefix ++ rho) (phi_update phi X R)
          (open_ty_rec (S (length prefix)) (Ty_FVar X) T) a0 b0).
      { intros a0 b0. apply (IHT (S (length prefix)) (Q :: prefix) rho phi X R).
        - simpl. reflexivity.
        - assumption.
        - exact Hf1. }
      exact (proj1 (related_eval_mor _ _ _ _ Hiff) (Hbody U1 U2 Q HLU1 HLU2)).
    + intros [Hf [Hg [fb [gb [Hfb [Hgb Hbody]]]]]].
      split; [exact Hf|]. split; [exact Hg|]. exists fb, gb.
      repeat split; try assumption.
      intros U1 U2 Q HLU1 HLU2.
      assert (Hiff : forall a0 b0,
        logical_value_relation (Q :: prefix ++ R :: rho) phi T a0 b0 <->
        logical_value_relation (Q :: prefix ++ rho) (phi_update phi X R)
          (open_ty_rec (S (length prefix)) (Ty_FVar X) T) a0 b0).
      { intros a0 b0.
        apply (IHT (S (length prefix)) (Q :: prefix) rho phi X R).
        - simpl. reflexivity.
        - assumption.
        - exact Hfresh. }
      exact (proj2 (related_eval_mor _ _ _ _ Hiff) (Hbody U1 U2 Q HLU1 HLU2)).
  - inversion Hlc. tauto.
Qed.

Lemma ty_subst_preserves_lc_at : forall T k,
  lc_ty_at k T -> forall X U, locally_closed_ty U ->
  lc_ty_at k (ty_subst X U T).
Proof.
  intros T k Hlc. induction Hlc; intros Z U HU; simpl.
  - apply lc_ty_bvar. assumption.
  - destruct (Nat.eqb Z X) eqn:E.
    + eapply lc_ty_at_monotone; [exact HU|lia].
    + apply lc_ty_fvar.
  - apply lc_ty_arrow; eauto.
  - apply lc_ty_all. eauto.
  - apply lc_ty_nat.
Qed.

Lemma ty_subst_open_ty_rec : forall T k X U V,
  locally_closed_ty U ->
  ty_subst X U (open_ty_rec k V T) =
  open_ty_rec k (ty_subst X U V) (ty_subst X U T).
Proof.
  induction T; intros k X U V HU; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - destruct (Nat.eqb X a) eqn:E.
    + assert (HUk : lc_ty_at k U).
      { eapply lc_ty_at_monotone; [exact HU|lia]. }
      rewrite (open_ty_rec_lc_at U k (ty_subst X U V) HUk). reflexivity.
    + reflexivity.
  - rewrite IHT1, IHT2; auto.
  - rewrite IHT; auto.
  - reflexivity.
Qed.

Lemma tm_ty_subst_open_tm_rec : forall t k X U s,
  tm_ty_subst X U (open_tm_rec k s t) =
  open_tm_rec k (tm_ty_subst X U s) (tm_ty_subst X U t).
Proof.
  induction t; intros k X U s; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - reflexivity.
  - f_equal. apply IHt.
  - f_equal; [apply IHt1|apply IHt2].
  - f_equal. apply IHt.
  - f_equal. apply IHt.
  - reflexivity.
  - f_equal. apply IHt.
  - f_equal; [apply IHt1|apply IHt2|apply IHt3].
Qed.

Lemma tm_ty_subst_open_tm_ty_rec : forall t k X U V,
  locally_closed_ty U ->
  tm_ty_subst X U (open_tm_ty_rec k V t) =
  open_tm_ty_rec k (ty_subst X U V) (tm_ty_subst X U t).
Proof.
  induction t; intros k X U V HU; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite ty_subst_open_ty_rec, IHt; auto.
  - rewrite IHt1, IHt2; auto.
  - f_equal. apply IHt with (k := S k); assumption.
  - rewrite IHt, ty_subst_open_ty_rec; auto.
  - reflexivity.
  - rewrite IHt; auto.
  - rewrite IHt1, IHt2, IHt3; auto.
Qed.

Lemma tm_ty_subst_preserves_lc_at : forall t K k,
  lc_tm_at K k t -> forall X U, locally_closed_ty U ->
  lc_tm_at K k (tm_ty_subst X U t).
Proof.
  intros t K k Hlc. induction Hlc; intros X U HU; simpl.
  - apply lc_tm_bvar. assumption.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + eapply ty_subst_preserves_lc_at; eauto.
    + eauto.
  - apply lc_tm_app; eauto.
  - apply lc_tm_tabs. eauto.
  - apply lc_tm_tapp.
    + eauto.
    + eapply ty_subst_preserves_lc_at; eauto.
  - apply lc_tm_zero.
  - apply lc_tm_succ. eauto.
  - apply lc_tm_rec; eauto.
Qed.

Lemma ty_subst_preserves_lc : forall T,
  locally_closed_ty T -> forall X U, locally_closed_ty U ->
  locally_closed_ty (ty_subst X U T).
Proof.
  intros T HT X U HU. unfold locally_closed_ty in *.
  eapply ty_subst_preserves_lc_at; eauto.
Qed.

Lemma tm_ty_subst_preserves_lc : forall t,
  locally_closed_tm t -> forall X U, locally_closed_ty U ->
  locally_closed_tm (tm_ty_subst X U t).
Proof.
  intros t Ht X U HU. unfold locally_closed_tm in *.
  eapply tm_ty_subst_preserves_lc_at; eauto.
Qed.

Lemma tm_ty_subst_preserves_value : forall v,
  value v -> forall X U, locally_closed_ty U -> value (tm_ty_subst X U v).
Proof.
  intros v Hv. induction Hv; intros X U HU.
  - apply v_abs. unfold locally_closed_tm in *.
    exact (tm_ty_subst_preserves_lc_at (tm_abs T t) 0 0 H X U HU).
  - apply v_tabs. unfold locally_closed_tm in *.
    exact (tm_ty_subst_preserves_lc_at (tm_tabs t) 0 0 H X U HU).
  - apply v_nat. induction H; simpl; constructor; assumption.
Qed.

Lemma tm_ty_subst_preserves_numeric : forall n,
  numeric_value n -> forall X U, numeric_value (tm_ty_subst X U n).
Proof.
  intros n Hn. induction Hn; intros X U; simpl; constructor; auto.
Qed.

Lemma tm_ty_subst_preserves_step : forall t t',
  t --> t' -> forall X U, locally_closed_ty U ->
  tm_ty_subst X U t --> tm_ty_subst X U t'.
Proof.
  intros t t' Hstep. induction Hstep; intros X U HU; simpl.
  - unfold open_tm. rewrite tm_ty_subst_open_tm_rec.
    apply ST_AppAbs.
    + change (lc_tm_at 0 0 (tm_ty_subst X U (tm_abs T t))).
      unfold locally_closed_tm in H.
      exact (tm_ty_subst_preserves_lc_at (tm_abs T t) 0 0 H X U HU).
    + eapply tm_ty_subst_preserves_value; eauto.
  - apply ST_App1.
    + apply IHHstep. exact HU.
    + eapply tm_ty_subst_preserves_lc; eauto.
  - apply ST_App2.
    + eapply tm_ty_subst_preserves_value; eauto.
    + apply IHHstep. exact HU.
  - unfold open_tm_ty. rewrite tm_ty_subst_open_tm_ty_rec; [|exact HU].
    apply ST_TAppTabs.
    + change (lc_tm_at 0 0 (tm_ty_subst X U (tm_tabs t))).
      unfold locally_closed_tm in H.
      exact (tm_ty_subst_preserves_lc_at (tm_tabs t) 0 0 H X U HU).
    + unfold locally_closed_ty in H0.
      exact (ty_subst_preserves_lc_at T 0 H0 X U HU).
  - apply ST_TApp.
    + apply IHHstep. exact HU.
    + unfold locally_closed_ty in H |- *.
      exact (ty_subst_preserves_lc_at T 0 H X U HU).
  - apply ST_Succ. apply IHHstep. exact HU.
  - apply ST_RecArg.
    + apply IHHstep. exact HU.
    + eapply tm_ty_subst_preserves_lc; eauto.
    + eapply tm_ty_subst_preserves_lc; eauto.
  - apply ST_RecBase.
    + eapply tm_ty_subst_preserves_numeric; eauto.
    + apply IHHstep. exact HU.
    + eapply tm_ty_subst_preserves_lc; eauto.
  - apply ST_RecStep.
    + eapply tm_ty_subst_preserves_numeric; eauto.
    + eapply tm_ty_subst_preserves_value; eauto.
    + apply IHHstep. exact HU.
  - apply ST_RecZero.
    + eapply tm_ty_subst_preserves_value; eauto.
    + eapply tm_ty_subst_preserves_value; eauto.
  - apply ST_RecSucc.
    + eapply tm_ty_subst_preserves_numeric; eauto.
    + eapply tm_ty_subst_preserves_value; eauto.
    + eapply tm_ty_subst_preserves_value; eauto.
Qed.

Lemma tm_ty_subst_preserves_multi : forall t u,
  t -->* u -> forall X U, locally_closed_ty U ->
  tm_ty_subst X U t -->* tm_ty_subst X U u.
Proof.
  intros t u H. induction H; intros X U HU.
  - constructor.
  - eapply multi_step.
    + eapply tm_ty_subst_preserves_step; eauto.
    + eapply IHmulti; eauto.
Qed.

Lemma instantiate_open_tm_rec : forall t theta gamma k x,
  term_substitution_closed gamma ->
  instantiate theta gamma (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k (gamma x) (instantiate theta gamma t).
Proof.
  induction t; intros theta gamma k x Hgamma; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - assert (Hlc : lc_tm_at 0 k (gamma a)).
    { eapply lc_tm_at_monotone; [apply Hgamma|lia|lia]. }
    rewrite (open_tm_rec_lc_at (gamma a) 0 k (gamma x) Hlc).
    reflexivity.
  - f_equal. apply IHt. exact Hgamma.
  - f_equal; [apply IHt1|apply IHt2]; exact Hgamma.
  - f_equal. apply IHt. exact Hgamma.
  - f_equal. apply IHt. exact Hgamma.
  - reflexivity.
  - f_equal. apply IHt. exact Hgamma.
  - f_equal; [apply IHt1|apply IHt2|apply IHt3]; exact Hgamma.
Qed.

Lemma instantiate_open_tm : forall t theta gamma x,
  term_substitution_closed gamma ->
  instantiate theta gamma (open_tm t (tm_fvar x)) =
  open_tm (instantiate theta gamma t) (gamma x).
Proof. intros; apply instantiate_open_tm_rec; assumption. Qed.

Lemma not_in_app_left : forall (A : Type) (x : A) xs ys,
  ~ In x (xs ++ ys) -> ~ In x xs.
Proof. intros A x xs ys H Hin. apply H. apply in_or_app. left. exact Hin. Qed.

Lemma not_in_app_right : forall (A : Type) (x : A) xs ys,
  ~ In x (xs ++ ys) -> ~ In x ys.
Proof. intros A x xs ys H Hin. apply H. apply in_or_app. right. exact Hin. Qed.

Lemma instantiate_term_update_fresh : forall t theta gamma x u,
  ~ In x (fv_tm t) ->
  instantiate theta (term_subst_update gamma x u) t =
  instantiate theta gamma t.
Proof.
  induction t; intros theta gamma x u Hfresh; simpl in *.
  - reflexivity.
  - destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E. subst a. exfalso. apply Hfresh. simpl. auto.
    + unfold term_subst_update. rewrite E. reflexivity.
  - rewrite IHt by exact Hfresh. reflexivity.
  - assert (H1 : ~ In x (fv_tm t1)) by (eapply not_in_app_left; exact Hfresh).
    assert (H2 : ~ In x (fv_tm t2)) by (eapply not_in_app_right; exact Hfresh).
    rewrite IHt1 by exact H1. rewrite IHt2 by exact H2. reflexivity.
  - f_equal. apply IHt. exact Hfresh.
  - rewrite IHt by exact Hfresh. reflexivity.
  - reflexivity.
  - f_equal. apply IHt. exact Hfresh.
  - assert (H1 : ~ In x (fv_tm t1)) by (eapply not_in_app_left; exact Hfresh).
    assert (H23 : ~ In x (fv_tm t2 ++ fv_tm t3)) by (eapply not_in_app_right; exact Hfresh).
    assert (H2 : ~ In x (fv_tm t2)) by (eapply not_in_app_left; exact H23).
    assert (H3 : ~ In x (fv_tm t3)) by (eapply not_in_app_right; exact H23).
    rewrite IHt1 by exact H1. rewrite IHt2 by exact H2.
    rewrite IHt3 by exact H3. reflexivity.
Qed.

Lemma logical_term_relation_of_values : forall rho phi T v w,
  value v -> value w ->
  logical_value_relation rho phi T v w ->
  logical_term_relation rho phi T v w.
Proof.
  intros rho phi T v w Hv Hw Hrel. unfold logical_term_relation, related_eval.
  exists v, w. repeat split; try assumption; constructor.
Qed.

Lemma logical_identity_extract : forall t U v,
  locally_closed_ty U -> value v ->
  logical_term_relation [] (fun _ => fun _ _ => False)
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) t t ->
  tm_app (tm_tapp t U) v -->* v.
Proof.
  intros t U v HLU Hv Hrel.
  unfold logical_term_relation, related_eval in Hrel.
  destruct Hrel as [f [g [Htf [Htg [Hf [Hg Hfg]]]]]].
  simpl in Hfg.
  destruct Hfg as [_ [_ [fb [gb [Hf' [Hg' Hbody]]]]]].
  subst f g.
  specialize (Hbody U U (fun a b => a = v /\ b = v) HLU HLU).
  unfold related_eval in Hbody.
  destruct Hbody as [uf [ug [Huf [Hug [Hvuf [Hvug Hfun]]]]]].
  simpl in Hfun.
  destruct Hfun as [_ [_ Hfun]].
  specialize (Hfun v v (conj Hv (conj Hv (conj eq_refl eq_refl)))).
  unfold related_eval in Hfun.
  destruct Hfun as [a [b [Hleft [Hright [Hva [Hvb [Hra [Hrb [HeqA HeqB]]]]]]]]].
  assert (Hav : a = v) by exact HeqA.
  subst a.
  assert (Htabs : locally_closed_tm (tm_tabs fb)).
  { eapply value_regular. exact Hf. }
  assert (Htap : tm_tapp (tm_tabs fb) U -->* open_tm_ty fb U).
  { eapply multi_step.
    - apply ST_TAppTabs; assumption.
    - apply multi_refl. }
  assert (Hprefix : tm_app (tm_tapp t U) v -->*
                    tm_app uf v).
  { eapply multi_trans.
    - apply multi_app_left.
      + apply multi_trans with (u := tm_tapp (tm_tabs fb) U).
        * apply multi_tapp; [exact Htf|exact HLU].
        * exact Htap.
      + apply value_regular; exact Hv.
    - apply multi_app_left; [exact Huf|apply value_regular; exact Hv]. }
  eapply multi_trans; [exact Hprefix|].
  exact Hleft.
Qed.

Lemma wf_ty_locally_closed : forall Delta T,
  wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T Hwf. induction Hwf.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; assumption.
  - apply lc_ty_all.
    pose (X := fresh L).
    pose proof (H0 X (fresh_notin L)) as Hlc.
    unfold locally_closed_ty in Hlc.
    eapply lc_ty_at_open_inv; exact Hlc.
  - apply lc_ty_nat.
Qed.

Lemma has_type_locally_closed : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T Hty. induction Hty.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + eapply wf_ty_locally_closed; eauto.
    + pose (x := fresh L).
      pose proof (H1 x (fresh_notin L)) as Hlc.
      unfold locally_closed_tm in Hlc.
      eapply lc_tm_at_open_tm_inv; exact Hlc.
  - apply lc_tm_app; assumption.
  - apply lc_tm_tabs.
    pose (X := fresh L).
    pose proof (H0 X (fresh_notin L)) as Hlc.
    unfold locally_closed_tm in Hlc.
    eapply lc_tm_at_open_ty_inv; exact Hlc.
  - apply lc_tm_tapp.
    + assumption.
    + eapply wf_ty_locally_closed; eauto.
  - apply lc_tm_zero.
  - apply lc_tm_succ. assumption.
  - apply lc_tm_rec; assumption.
Qed.

Lemma has_type_result_locally_closed : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_ty T.
Proof.
  intros Delta Gamma t T Hty. induction Hty.
  - eapply wf_ty_locally_closed; eauto.
  - apply lc_ty_arrow.
    + eapply wf_ty_locally_closed; eauto.
    + pose (x := fresh L).
      pose proof (H1 x (fresh_notin L)) as Hbody.
      exact Hbody.
  - inversion IHHty1; subst. assumption.
  - apply lc_ty_all.
    pose (X := fresh L).
    pose proof (H0 X (fresh_notin L)) as Hbody.
    pose proof (H0 X (fresh_notin L)) as Hlc.
    unfold locally_closed_ty in Hlc.
    eapply lc_ty_at_open_inv; exact Hlc.
  - inversion IHHty; subst.
    unfold locally_closed_ty in *.
    eapply lc_ty_at_open.
    + exact H2.
    + eapply wf_ty_locally_closed; eauto.
  - apply lc_ty_nat.
  - apply lc_ty_nat.
  - assumption.
Qed.

Definition related_context
    (rho : list value_relation) (phi : atom -> value_relation)
    (Gamma : context) (gamma1 gamma2 : term_substitution) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    logical_term_relation rho phi T (gamma1 x) (gamma2 x).

Lemma related_context_rho_mor : forall rho1 rho2 phi Gamma gamma1 gamma2,
  (forall x T, lookup_context x Gamma = Some T -> locally_closed_ty T) ->
  related_context rho1 phi Gamma gamma1 gamma2 ->
  related_context rho2 phi Gamma gamma1 gamma2.
Proof.
  intros rho1 rho2 phi Gamma gamma1 gamma2 Hlc Hctx x T Hlook.
  specialize (Hctx x T Hlook).
  unfold logical_term_relation in *.
  assert (Hiff : forall v w,
    logical_value_relation rho1 phi T v w <->
    logical_value_relation rho2 phi T v w).
  { intros v w. apply logical_value_relation_closed_env.
    apply Hlc with (x:=x). exact Hlook. }
  exact (proj1 (related_eval_mor _ _ _ _ Hiff) Hctx).
Qed.

Lemma logical_value_relation_phi_fresh : forall T rho phi X R,
  ~ In X (fv_ty T) -> forall v w,
  logical_value_relation rho phi T v w <->
  logical_value_relation rho (phi_update phi X R) T v w.
Proof.
  induction T; intros rho phi X R Hfresh v w; simpl in *.
  - tauto.
  - destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E. subst a. exfalso. apply Hfresh. simpl. auto.
    + unfold phi_update. rewrite E. tauto.
  - assert (Hparts : ~ In X (fv_ty T1) /\ ~ In X (fv_ty T2)).
    { rewrite in_app_iff in Hfresh. tauto. }
    destruct Hparts as [Hf1 Hf2]. simpl. split.
    + intros [Hval1 [Hval2 Hfun]]. repeat split; try assumption.
      intros a b Hab. apply (proj2 (IHT1 rho phi X R Hf1 a b)) in Hab.
      specialize (Hfun a b Hab).
      assert (Hiff : forall x y,
        logical_value_relation rho phi T2 x y <->
        logical_value_relation rho (phi_update phi X R) T2 x y).
      { intros x y. apply IHT2; assumption. }
      exact (proj1 (related_eval_mor _ _ _ _ Hiff) Hfun).
    + intros [Hval1 [Hval2 Hfun]]. repeat split; try assumption.
      intros a b Hab. apply (proj1 (IHT1 rho phi X R Hf1 a b)) in Hab.
      specialize (Hfun a b Hab).
      assert (Hiff : forall x y,
        logical_value_relation rho phi T2 x y <->
        logical_value_relation rho (phi_update phi X R) T2 x y).
      { intros x y. apply IHT2; assumption. }
      exact (proj2 (related_eval_mor _ _ _ _ Hiff) Hfun).
  - assert (Hf : ~ In X (fv_ty T)).
    { exact Hfresh. }
    simpl. split.
    + intros [Hval1 [Hval2 [fb [gb [Hfb [Hgb Hbody]]]]]].
      split; [exact Hval1|]. split; [exact Hval2|]. exists fb, gb.
      repeat split; try assumption.
      intros U1 U2 Q HLU1 HLU2.
      assert (Hiff : forall a b,
        logical_value_relation (Q :: rho) phi T a b <->
        logical_value_relation (Q :: rho) (phi_update phi X R) T a b).
      { intros a b. apply IHT; assumption. }
      exact (proj1 (related_eval_mor _ _ _ _ Hiff) (Hbody U1 U2 Q HLU1 HLU2)).
    + intros [Hval1 [Hval2 [fb [gb [Hfb [Hgb Hbody]]]]]].
      split; [exact Hval1|]. split; [exact Hval2|]. exists fb, gb.
      repeat split; try assumption.
      intros U1 U2 Q HLU1 HLU2.
      assert (Hiff : forall a b,
        logical_value_relation (Q :: rho) phi T a b <->
        logical_value_relation (Q :: rho) (phi_update phi X R) T a b).
      { intros a b. apply IHT; assumption. }
      exact (proj2 (related_eval_mor _ _ _ _ Hiff) (Hbody U1 U2 Q HLU1 HLU2)).
  - tauto.
Qed.

Lemma lookup_context_ftv : forall Gamma x T X,
  lookup_context x Gamma = Some T ->
  In X (fv_ty T) -> In X (ftv_context Gamma).
Proof.
  induction Gamma as [|[y S] Gamma IH]; intros x T X Hlook Hin; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + inversion Hlook; subst. apply in_or_app. left. exact Hin.
    + apply in_or_app. right. eapply IH; eauto.
Qed.

Lemma related_context_update : forall rho phi Gamma gamma1 gamma2
    x T a b,
  related_context rho phi Gamma gamma1 gamma2 ->
  logical_term_relation rho phi T a b ->
  related_context rho phi (update Gamma x T)
    (term_subst_update gamma1 x a) (term_subst_update gamma2 x b).
Proof.
  intros rho phi Gamma gamma1 gamma2 x T a b Hctx Hxy y S Hlook.
  unfold update in Hlook. simpl in Hlook.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y.
    inversion Hlook; subst S. unfold term_subst_update.
    rewrite !Nat.eqb_refl. exact Hxy.
  - apply Nat.eqb_neq in E.
    assert (E' : Nat.eqb x y = false) by (apply Nat.eqb_neq; congruence).
    unfold term_subst_update. rewrite !E'.
    eapply Hctx. exact Hlook.
Qed.

Lemma related_context_phi_fresh : forall rho phi Gamma gamma1 gamma2 X R,
  ~ In X (ftv_context Gamma) ->
  related_context rho phi Gamma gamma1 gamma2 ->
  related_context rho (phi_update phi X R) Gamma gamma1 gamma2.
Proof.
  intros rho phi Gamma gamma1 gamma2 X R Hfresh Hctx x T Hlook.
  specialize (Hctx x T Hlook).
  assert (Hty : ~ In X (fv_ty T)).
  { intro Hin. apply Hfresh. eapply lookup_context_ftv; eauto. }
  unfold logical_term_relation in *.
  assert (Hiff : forall v w,
    logical_value_relation rho phi T v w <->
    logical_value_relation rho (phi_update phi X R) T v w).
  { intros v w. apply (logical_value_relation_phi_fresh T rho phi X R Hty v w). }
  exact (proj1 (related_eval_mor _ _ _ _ Hiff) Hctx).
Qed.

Lemma logical_term_relation_app : forall rho phi A B f g a b,
  logical_term_relation rho phi (Ty_Arrow A B) f g ->
  logical_term_relation rho phi A a b ->
  locally_closed_tm a -> locally_closed_tm b ->
  logical_term_relation rho phi B (tm_app f a) (tm_app g b).
Proof.
  intros rho phi A B f g a b Hf Ha HLa HLb.
  unfold logical_term_relation, related_eval in *.
  destruct Hf as [fv [gv [Hf [Hg [Hfv [Hgv Hfr]]]]]].
  destruct Ha as [av [bv [Ha [Hb [Hav [Hbv Har]]]]]].
  simpl in Hfr. destruct Hfr as [_ [_ Happly]].
  specialize (Happly av bv Har).
  assert (Hpath1 : tm_app f a -->* tm_app fv av).
  { eapply multi_trans.
    - apply multi_app_left.
      + exact Hf.
      + exact HLa.
    - apply multi_app_right; [exact Hfv|exact Ha]. }
  assert (Hpath2 : tm_app g b -->* tm_app gv bv).
  { eapply multi_trans.
    - apply multi_app_left.
      + exact Hg.
      + exact HLb.
    - apply multi_app_right; [exact Hgv|exact Hb]. }
  unfold related_eval in Happly.
  destruct Happly as [v [w [Hv [Hw [Hvv [Hww Hrel]]]]]].
  exists v, w. repeat split; try assumption.
  - eapply multi_trans; eassumption.
  - eapply multi_trans; eassumption.
Qed.

Lemma logical_term_relation_succ : forall rho phi n m,
  logical_term_relation rho phi Ty_Nat n m ->
  logical_term_relation rho phi Ty_Nat (tm_succ n) (tm_succ m).
Proof.
  intros rho phi n m H. unfold logical_term_relation, related_eval in *.
  destruct H as [nv [mv [Hn [Hm [Hnv [Hmv Hrel]]]]]].
  simpl in Hrel. destruct Hrel as [Hnn [Hmm Heq]]. subst mv.
  exists (tm_succ nv), (tm_succ nv).
  split; [apply multi_succ; exact Hn|].
  split; [apply multi_succ; exact Hm|].
  split.
  - apply v_nat. constructor. exact Hnn.
  - split.
    + apply v_nat. constructor. exact Hnn.
    + simpl. repeat split; try assumption; constructor; assumption.
Qed.

Lemma logical_term_relation_natrec : forall rho phi T n m b c s r,
  logical_term_relation rho phi Ty_Nat n m ->
  logical_term_relation rho phi T b c ->
  logical_term_relation rho phi (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s r ->
  locally_closed_tm b -> locally_closed_tm c ->
  locally_closed_tm s -> locally_closed_tm r ->
  logical_term_relation rho phi T (tm_natrec n b s) (tm_natrec m c r).
Proof.
  intros rho phi T n m b c s r Hn Hb Hs Hlb Hlc Hls Hlr.
  unfold logical_term_relation, related_eval in *.
  destruct Hn as [nv [mv [Hn [Hm [Hnv [Hmv Hnum]]]]]].
  destruct Hb as [bv [cv [Hb [Hc [Hbv [Hcv Hbrel]]]]]].
  destruct Hs as [sv [tv [Hs [Ht [Hsv [Htv Hsrel]]]]]].
  simpl in Hnum. destruct Hnum as [Hnvnum [Hmnum Hnum]].
  subst mv.
  simpl in Hsrel. destruct Hsrel as [_ [_ Hsfun]].
  assert (HsvalueRel : logical_value_relation rho phi
    (Ty_Arrow Ty_Nat (Ty_Arrow T T)) sv tv).
  { simpl. split; [exact Hsv|]. split; [exact Htv|exact Hsfun]. }
  assert (Hrec : forall k, numeric_value k ->
    related_eval (logical_value_relation rho phi T)
      (tm_natrec k bv sv) (tm_natrec k cv tv)).
  { intros k Hk. induction Hk.
    - unfold related_eval. exists bv, cv. repeat split.
      + eapply multi_step. apply ST_RecZero; assumption. apply multi_refl.
      + eapply multi_step. apply ST_RecZero; assumption. apply multi_refl.
      + exact Hbv.
      + exact Hcv.
      + exact Hbrel.
    - pose proof IHHk as Hrecursive.
      unfold related_eval in Hrecursive.
      destruct Hrecursive as [rv [rw [Hrv [Hrw [HrvV [HrwV Hrrel]]]]]].
      assert (Hnrel : logical_value_relation rho phi Ty_Nat n0 n0).
      { simpl. split; [exact Hk|]. split; [exact Hk|reflexivity]. }
      specialize (Hsfun n0 n0 Hnrel) as Hfirst.
      unfold related_eval in Hfirst.
      destruct Hfirst as [f1 [f2 [Hf1 [Hf2 [Hf1V [Hf2V Hfrel]]]]]].
      pose proof (logical_term_relation_of_values rho phi T rv rw HrvV HrwV Hrrel) as Hrr.
      assert (HrecLC1 : locally_closed_tm (tm_natrec n0 bv sv)).
      { apply lc_tm_rec; [|apply value_regular; exact Hbv|apply value_regular; exact Hsv].
        apply value_regular. apply v_nat. exact Hk. }
      assert (HrecLC2 : locally_closed_tm (tm_natrec n0 cv tv)).
      { apply lc_tm_rec; [|apply value_regular; exact Hcv|apply value_regular; exact Htv].
        apply value_regular. apply v_nat. exact Hk. }
      pose proof (logical_term_relation_app rho phi Ty_Nat (Ty_Arrow T T)
        sv tv n0 n0
        (@logical_term_relation_of_values rho phi
          (Ty_Arrow Ty_Nat (Ty_Arrow T T)) sv tv Hsv Htv HsvalueRel)
        (@logical_term_relation_of_values rho phi Ty_Nat n0 n0
          (v_nat n0 Hk) (v_nat n0 Hk) Hnrel)
        (@value_regular n0 (v_nat n0 Hk)) (@value_regular n0 (v_nat n0 Hk)) ) as HfirstTerm.
      pose proof (logical_term_relation_app rho phi T T
        (tm_app sv n0) (tm_app tv n0) (tm_natrec n0 bv sv) (tm_natrec n0 cv tv)
        HfirstTerm IHHk HrecLC1 HrecLC2) as Happ.
      unfold logical_term_relation, related_eval in Happ.
      destruct Happ as [z [zz [Hz [Hzz [HzV [HzzV Hzrel]]]]]].
      unfold related_eval. exists z, zz. repeat split.
      + eapply multi_trans.
        * eapply multi_step. apply ST_RecSucc; assumption. apply multi_refl.
        * exact Hz.
      + eapply multi_trans.
        * eapply multi_step. apply ST_RecSucc; assumption. apply multi_refl.
        * exact Hzz.
      + exact HzV.
      + exact HzzV.
      + exact Hzrel. }
  pose proof (Hrec nv Hnvnum) as Hterminal.
  unfold related_eval in Hterminal.
  destruct Hterminal as [z [zz [Hz [Hzz [HzV [HzzV Hzrel]]]]]].
  unfold related_eval. exists z, zz. repeat split.
  - eapply multi_trans.
    + eapply multi_trans.
      * apply multi_rec_arg; [exact Hn|exact Hlb|exact Hls].
      * apply multi_rec_base; [exact Hnvnum|exact Hb|exact Hls].
    + eapply multi_trans.
      * apply multi_rec_step; [exact Hnvnum|exact Hbv|exact Hs].
      * exact Hz.
  - eapply multi_trans.
    + eapply multi_trans.
      * apply multi_rec_arg; [exact Hm|exact Hlc|exact Hlr].
      * apply multi_rec_base; [exact Hnvnum|exact Hc|exact Hlr].
    + eapply multi_trans.
      * apply multi_rec_step; [exact Hnvnum|exact Hcv|exact Ht].
      * exact Hzz.
  - exact HzV.
  - exact HzzV.
  - exact Hzrel.
Qed.

Lemma instantiate_ty_preserves_lc_at : forall T K,
  lc_ty_at K T -> forall theta,
  type_substitution_closed theta ->
  lc_ty_at K (instantiate_ty theta T).
Proof.
  intros T K Hlc. induction Hlc; intros theta Htheta; simpl.
  - apply lc_ty_bvar. assumption.
  - eapply lc_ty_at_monotone.
    + apply Htheta.
    + lia.
  - apply lc_ty_arrow; eauto.
  - apply lc_ty_all. eauto.
  - apply lc_ty_nat.
Qed.

Lemma instantiate_preserves_lc_at : forall t K k,
  lc_tm_at K k t -> forall theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  lc_tm_at K k (instantiate theta gamma t).
Proof.
  intros t K k Hlc. induction Hlc; intros theta gamma Htheta Hgamma; simpl.
  - apply lc_tm_bvar. assumption.
  - eapply lc_tm_at_monotone; [apply Hgamma|lia|lia].
  - apply lc_tm_abs.
    + eapply instantiate_ty_preserves_lc_at; eauto.
    + eauto.
  - apply lc_tm_app; eauto.
  - apply lc_tm_tabs. eauto.
  - apply lc_tm_tapp.
    + eauto.
    + eapply instantiate_ty_preserves_lc_at; eauto.
  - apply lc_tm_zero.
  - apply lc_tm_succ. eauto.
  - apply lc_tm_rec; eauto.
Qed.

Lemma instantiate_preserves_lc : forall t theta gamma,
  locally_closed_tm t ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm (instantiate theta gamma t).
Proof.
  intros. unfold locally_closed_tm in *.
  eapply instantiate_preserves_lc_at; eauto.
Qed.

Lemma instantiate_ty_update_fresh : forall T theta X U,
  ~ In X (fv_ty T) ->
  instantiate_ty (type_subst_update theta X U) T = instantiate_ty theta T.
Proof.
  induction T; intros theta X U Hfresh; simpl in *.
  - reflexivity.
  - simpl in Hfresh. unfold type_subst_update.
    destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E. subst a. exfalso. apply Hfresh. simpl. auto.
    + reflexivity.
  - assert (Hparts : ~ In X (fv_ty T1) /\ ~ In X (fv_ty T2)).
    { rewrite in_app_iff in Hfresh. tauto. }
    destruct Hparts as [H1 H2].
    rewrite IHT1 by exact H1. rewrite IHT2 by exact H2. reflexivity.
  - rewrite IHT by exact Hfresh. reflexivity.
  - reflexivity.
Qed.

Lemma instantiate_ty_open_update : forall T k theta X U,
  type_substitution_closed theta ->
  locally_closed_ty U ->
  lc_ty_at (S k) T ->
  ~ In X (fv_ty T) ->
  instantiate_ty (type_subst_update theta X U)
      (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k U (instantiate_ty theta T).
Proof.
  induction T; intros k theta X U Htheta HU Hlc Hfresh; simpl in *.
  - inversion Hlc; subst.
    destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. simpl. unfold type_subst_update.
      rewrite Nat.eqb_refl. reflexivity.
    + apply Nat.eqb_neq in E. assert (Hnk : n < k) by lia.
      reflexivity.
  - simpl in Hfresh. unfold type_subst_update.
    destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E. subst a. exfalso. apply Hfresh. simpl. auto.
    + simpl.
      assert (HUlc : lc_ty_at k (theta a)).
      { eapply lc_ty_at_monotone; [apply Htheta|lia]. }
      symmetry. apply open_ty_rec_lc_at. exact HUlc.
  - inversion Hlc; subst. simpl.
    assert (Hparts : ~ In X (fv_ty T1) /\ ~ In X (fv_ty T2)).
    { rewrite in_app_iff in Hfresh. tauto. }
    destruct Hparts as [Hf1 Hf2].
    rewrite (IHT1 k theta X U Htheta HU H2 Hf1).
    rewrite (IHT2 k theta X U Htheta HU H3 Hf2). reflexivity.
  - inversion Hlc; subst. simpl.
    rewrite (IHT (S k) theta X U Htheta HU H1 Hfresh). reflexivity.
  - reflexivity.
Qed.

Lemma instantiate_open_tm_ty_update_rec : forall t K k theta gamma X U,
  lc_tm_at (S K) k t ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_ty U ->
  ~ In X (ftv_tm t) ->
  instantiate (type_subst_update theta X U) gamma
      (open_tm_ty_rec K (Ty_FVar X) t) =
  open_tm_ty_rec K U (instantiate theta gamma t).
Proof.
  induction t; intros K k theta gamma X U Hlc Htheta Hgamma HU Hfresh; simpl in *.
  - reflexivity.
  - assert (Hlcg : lc_tm_at K k (gamma a)).
    { eapply lc_tm_at_monotone; [apply Hgamma|lia|lia]. }
    rewrite (open_tm_ty_rec_lc_at (gamma a) K k U Hlcg). reflexivity.
  - inversion Hlc; subst.
    assert (HfT : ~ In X (fv_ty t)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. left; exact Hin. }
    assert (Hft : ~ In X (ftv_tm t0)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. right; exact Hin. }
    rewrite (instantiate_ty_open_update t K theta X U Htheta HU H3 HfT).
    rewrite (IHt K (S k) theta gamma X U H4 Htheta Hgamma HU Hft).
    reflexivity.
  - inversion Hlc; subst.
    assert (Hf1 : ~ In X (ftv_tm t1)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. left; exact Hin. }
    assert (Hf2 : ~ In X (ftv_tm t2)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. right; exact Hin. }
    rewrite (IHt1 K k theta gamma X U H3 Htheta Hgamma HU Hf1).
    rewrite (IHt2 K k theta gamma X U H4 Htheta Hgamma HU Hf2). reflexivity.
  - inversion Hlc; subst.
    rewrite (IHt (S K) k theta gamma X U H2 Htheta Hgamma HU Hfresh).
    reflexivity.
  - inversion Hlc; subst.
    assert (Hft : ~ In X (ftv_tm t)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. left; exact Hin. }
    assert (HfT : ~ In X (fv_ty t0)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. right; exact Hin. }
    rewrite (IHt K k theta gamma X U H3 Htheta Hgamma HU Hft).
    rewrite (instantiate_ty_open_update t0 K theta X U Htheta HU H4 HfT).
    reflexivity.
  - reflexivity.
  - inversion Hlc; subst.
    rewrite (IHt K k theta gamma X U H2 Htheta Hgamma HU Hfresh). reflexivity.
  - inversion Hlc; subst.
    assert (Hfn : ~ In X (ftv_tm t1)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. left. exact Hin. }
    assert (Hfb : ~ In X (ftv_tm t2)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. right. apply in_or_app. left. exact Hin. }
    assert (Hfs : ~ In X (ftv_tm t3)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. right. apply in_or_app. right. exact Hin. }
    rewrite (IHt1 K k theta gamma X U H4 Htheta Hgamma HU Hfn).
    rewrite (IHt2 K k theta gamma X U H5 Htheta Hgamma HU Hfb).
    rewrite (IHt3 K k theta gamma X U H6 Htheta Hgamma HU Hfs). reflexivity.
Qed.

Lemma instantiate_open_tm_ty_update : forall t theta gamma X U,
  lc_tm_at 1 0 t ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_ty U ->
  ~ In X (ftv_tm t) ->
  instantiate (type_subst_update theta X U) gamma
      (open_tm_ty t (Ty_FVar X)) =
  open_tm_ty (instantiate theta gamma t) U.
Proof.
  intros. unfold open_tm_ty.
  eapply instantiate_open_tm_ty_update_rec; eauto.
Qed.

Theorem fundamental_theorem : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall rho phi theta1 theta2 gamma1 gamma2,
    type_substitution_closed theta1 -> type_substitution_closed theta2 ->
    term_substitution_closed gamma1 -> term_substitution_closed gamma2 ->
    (forall x S, lookup_context x Gamma = Some S -> locally_closed_ty S) ->
    related_context rho phi Gamma gamma1 gamma2 ->
    logical_term_relation rho phi T
      (instantiate theta1 gamma1 t) (instantiate theta2 gamma2 t).
Proof.
  intros Delta Gamma t T Hty. induction Hty;
    intros rho phi theta1 theta2 gamma1 gamma2 Hth1 Hth2 Hga1 Hga2 Hctxlc Hctx.
  - specialize (Hctx x T H). exact Hctx.
  - assert (Hsrc : has_type Delta Gamma (tm_abs T1 t2) (Ty_Arrow T1 T2)).
    { econstructor; eauto. }
    assert (Hlcsrc : locally_closed_tm (tm_abs T1 t2)).
    { eapply has_type_locally_closed; exact Hsrc. }
    assert (Hlc1 : locally_closed_tm (instantiate theta1 gamma1 (tm_abs T1 t2))).
    { eapply instantiate_preserves_lc; [exact Hlcsrc|exact Hth1|exact Hga1]. }
    assert (Hlc2 : locally_closed_tm (instantiate theta2 gamma2 (tm_abs T1 t2))).
    { eapply instantiate_preserves_lc; [exact Hlcsrc|exact Hth2|exact Hga2]. }
    simpl. unfold logical_term_relation, related_eval. simpl.
    exists (instantiate theta1 gamma1 (tm_abs T1 t2)),
           (instantiate theta2 gamma2 (tm_abs T1 t2)).
    split; [constructor|]. split; [constructor|].
    split.
    + apply v_abs. exact Hlc1.
    + split.
      * apply v_abs. exact Hlc2.
      * simpl. split.
        -- apply v_abs. exact Hlc1.
        -- split.
           ++ apply v_abs. exact Hlc2.
           ++ intros a b Hab.
              destruct (logical_value_relation_values T1 rho phi a b Hab) as [Hav Hbv].
              pose (x := fresh (L ++ fv_tm t2)).
              assert (HxL : ~ In x L).
              { unfold x. eapply not_in_app_left. apply fresh_notin. }
              assert (HxF : ~ In x (fv_tm t2)).
              { unfold x. eapply not_in_app_right. apply fresh_notin. }
              assert (Hctx' : related_context rho phi (update Gamma x T1)
                (term_subst_update gamma1 x a) (term_subst_update gamma2 x b)).
              { eapply related_context_update.
                - exact Hctx.
                - eapply logical_term_relation_of_values; eauto. }
              assert (Hctxlc' : forall y S,
                lookup_context y (update Gamma x T1) = Some S -> locally_closed_ty S).
              { intros y S Hlook. unfold update in Hlook. simpl in Hlook.
                destruct (Nat.eqb y x) eqn:E.
                - inversion Hlook; subst. eapply wf_ty_locally_closed; exact H.
                - eapply Hctxlc. exact Hlook. }
              assert (Hga1' : term_substitution_closed (term_subst_update gamma1 x a)).
              { apply term_subst_update_closed.
                - exact Hga1.
                - eapply value_regular; exact Hav. }
              assert (Hga2' : term_substitution_closed (term_subst_update gamma2 x b)).
              { apply term_subst_update_closed.
                - exact Hga2.
                - eapply value_regular; exact Hbv. }
              pose proof (H1 x HxL rho phi theta1 theta2
                (term_subst_update gamma1 x a) (term_subst_update gamma2 x b)
                Hth1 Hth2 Hga1' Hga2' Hctxlc' Hctx') as Hopen.
              rewrite (instantiate_open_tm t2 theta1
                (term_subst_update gamma1 x a) x Hga1') in Hopen.
              rewrite (instantiate_open_tm t2 theta2
                (term_subst_update gamma2 x b) x Hga2') in Hopen.
              rewrite (instantiate_term_update_fresh t2 theta1 gamma1 x a HxF) in Hopen.
              rewrite (instantiate_term_update_fresh t2 theta2 gamma2 x b HxF) in Hopen.
              unfold term_subst_update in Hopen. rewrite !Nat.eqb_refl in Hopen.
              unfold logical_term_relation in Hopen.
              destruct Hopen as [va [vb [Hva [Hvb [HvalA [HvalB Hrel]]]]]].
              exists va, vb. repeat split.
              ** eapply multi_trans.
                 --- eapply multi_step.
                     +++ apply ST_AppAbs.
                         *** exact Hlc1.
                         *** exact Hav.
                     +++ apply multi_refl.
                 --- exact Hva.
              ** eapply multi_trans.
                 --- eapply multi_step.
                     +++ apply ST_AppAbs.
                         *** exact Hlc2.
                         *** exact Hbv.
                     +++ apply multi_refl.
                 --- exact Hvb.
              ** exact HvalA.
              ** exact HvalB.
              ** exact Hrel.
  - eapply logical_term_relation_app.
    + exact (IHHty1 rho phi theta1 theta2 gamma1 gamma2 Hth1 Hth2 Hga1 Hga2 Hctxlc Hctx).
    + exact (IHHty2 rho phi theta1 theta2 gamma1 gamma2 Hth1 Hth2 Hga1 Hga2 Hctxlc Hctx).
    + eapply instantiate_preserves_lc.
      * eapply has_type_locally_closed; exact Hty2.
      * exact Hth1.
      * exact Hga1.
    + eapply instantiate_preserves_lc.
      * eapply has_type_locally_closed; exact Hty2.
      * exact Hth2.
      * exact Hga2.
  - (* type abstraction *)
    pose (X := fresh (L ++ ftv_context Gamma ++ ftv_tm t ++ fv_ty T)).
    assert (Hx : ~ In X L).
    { unfold X. intro Hin. apply (fresh_notin (L ++ ftv_context Gamma ++ ftv_tm t ++ fv_ty T)).
      repeat rewrite in_app_iff. tauto. }
    assert (Hxctx : ~ In X (ftv_context Gamma)).
    { unfold X. intro Hin. apply (fresh_notin (L ++ ftv_context Gamma ++ ftv_tm t ++ fv_ty T)).
      repeat rewrite in_app_iff. tauto. }
    assert (Hxtm : ~ In X (ftv_tm t)).
    { unfold X. intro Hin. apply (fresh_notin (L ++ ftv_context Gamma ++ ftv_tm t ++ fv_ty T)).
      repeat rewrite in_app_iff. tauto. }
    assert (HxT : ~ In X (fv_ty T)).
    { unfold X. intro Hin. apply (fresh_notin (L ++ ftv_context Gamma ++ ftv_tm t ++ fv_ty T)).
      repeat rewrite in_app_iff. tauto. }
    pose proof (H X Hx) as Htyped.
    pose proof (has_type_locally_closed _ _ _ _ Htyped) as Hlcopened.
    pose proof (lc_tm_at_open_ty_inv t 0 0 X Hlcopened) as Hlcbody.
    pose proof (has_type_result_locally_closed _ _ _ _ Htyped) as Hlctypeopen.
    pose proof (lc_ty_at_open_inv T 0 X Hlctypeopen) as Hlctypebody.
    assert (Hlcabs : locally_closed_tm (tm_tabs t)).
    { apply lc_tm_tabs. exact Hlcbody. }
    assert (Hlc1 : locally_closed_tm (instantiate theta1 gamma1 (tm_tabs t))).
    { eapply instantiate_preserves_lc; [exact Hlcabs|exact Hth1|exact Hga1]. }
    assert (Hlc2 : locally_closed_tm (instantiate theta2 gamma2 (tm_tabs t))).
    { eapply instantiate_preserves_lc; [exact Hlcabs|exact Hth2|exact Hga2]. }
    unfold logical_term_relation, related_eval. simpl.
    exists (instantiate theta1 gamma1 (tm_tabs t)),
           (instantiate theta2 gamma2 (tm_tabs t)).
    split; [constructor|]. split; [constructor|].
    split; [apply v_tabs; exact Hlc1|].
    split; [apply v_tabs; exact Hlc2|].
    simpl. split; [apply v_tabs; exact Hlc1|].
    split; [apply v_tabs; exact Hlc2|].
    exists (instantiate theta1 gamma1 t), (instantiate theta2 gamma2 t).
    split; [reflexivity|]. split; [reflexivity|].
    intros U1 U2 R HLU1 HLU2.
      pose proof (related_context_phi_fresh rho phi Gamma gamma1 gamma2 X R
        Hxctx Hctx) as HctxRphi.
      assert (Hth1' : type_substitution_closed (type_subst_update theta1 X U1)).
      { apply type_subst_update_closed; assumption. }
      assert (Hth2' : type_substitution_closed (type_subst_update theta2 X U2)).
      { apply type_subst_update_closed; assumption. }
      pose proof (H0 X Hx rho (phi_update phi X R)
        (type_subst_update theta1 X U1) (type_subst_update theta2 X U2)
        gamma1 gamma2 Hth1' Hth2' Hga1 Hga2 Hctxlc HctxRphi) as Hopened.
      rewrite (instantiate_open_tm_ty_update t theta1 gamma1 X U1
        Hlcbody Hth1 Hga1 HLU1 Hxtm) in Hopened.
      rewrite (instantiate_open_tm_ty_update t theta2 gamma2 X U2
        Hlcbody Hth2 Hga2 HLU2 Hxtm) in Hopened.
      unfold logical_term_relation in Hopened.
      assert (Hiff : forall a b,
        logical_value_relation (R :: rho) phi T a b <->
        logical_value_relation rho (phi_update phi X R) (open_ty T (Ty_FVar X)) a b).
      { intros a b. apply (logical_value_relation_open_ty_rec T 0 [] rho phi X R).
        - reflexivity.
        - exact Hlctypebody.
        - exact HxT. }
      exact (proj2 (related_eval_mor _ _ _ _ Hiff) Hopened).
  - (* type application *)
    pose proof (IHHty rho phi theta1 theta2 gamma1 gamma2
      Hth1 Hth2 Hga1 Hga2 Hctxlc Hctx) as Hfunterm.
    pose proof (has_type_result_locally_closed _ _ _ _ Hty) as HlcAll.
    assert (HlcT : lc_ty_at 1 T).
    { inversion HlcAll; assumption. }
    pose proof (wf_ty_locally_closed _ _ H) as HlcU.
    pose proof (instantiate_ty_preserves_lc_at U 0 HlcU theta1 Hth1) as HlcU1.
    pose proof (instantiate_ty_preserves_lc_at U 0 HlcU theta2 Hth2) as HlcU2.
    unfold logical_term_relation, related_eval in Hfunterm.
    destruct Hfunterm as [f [g [Hf [Hg [Hfv [Hgv Hfg]]]]]].
    simpl in Hfg.
    destruct Hfg as [Hfv' [Hgv' [fb [gb [Hfb [Hgb Hbody]]]]]].
    subst f g.
    set (Q := logical_value_relation rho phi U).
    specialize (Hbody (instantiate_ty theta1 U) (instantiate_ty theta2 U) Q
      HlcU1 HlcU2).
    assert (Hiff : forall a b,
      logical_value_relation (Q :: rho) phi T a b <->
      logical_value_relation rho phi (open_ty T U) a b).
    { intros a b. unfold Q. apply (logical_value_relation_open_ty_closed T 0 [] rho phi U).
      - reflexivity.
      - exact HlcT.
      - exact HlcU. }
    pose proof (proj1 (related_eval_mor _ _ _ _ Hiff) Hbody) as Hresult.
    unfold logical_term_relation, related_eval.
    destruct Hresult as [va [vb [Hva [Hvb [HvaV [HvbV Hrel]]]]]].
    exists va, vb. repeat split; try assumption.
    + eapply multi_trans.
      * eapply multi_trans.
        -- apply multi_tapp; [exact Hf|exact HlcU1].
        -- eapply multi_step.
           ++ apply ST_TAppTabs; [eapply value_regular; exact Hfv|exact HlcU1].
           ++ apply multi_refl.
      * exact Hva.
    + eapply multi_trans.
      * eapply multi_trans.
        -- apply multi_tapp; [exact Hg|exact HlcU2].
        -- eapply multi_step.
           ++ apply ST_TAppTabs; [eapply value_regular; exact Hgv|exact HlcU2].
           ++ apply multi_refl.
      * exact Hvb.
  - unfold logical_term_relation, related_eval. simpl.
    exists tm_zero, tm_zero.
    split; [apply multi_refl|].
    split; [apply multi_refl|].
    split; [apply v_nat; constructor|].
    split; [apply v_nat; constructor|].
    simpl. split; [constructor|]. split; [constructor|reflexivity].
  - apply logical_term_relation_succ.
    exact (IHHty rho phi theta1 theta2 gamma1 gamma2 Hth1 Hth2 Hga1 Hga2 Hctxlc Hctx).
  - eapply logical_term_relation_natrec.
    + exact (IHHty1 rho phi theta1 theta2 gamma1 gamma2
        Hth1 Hth2 Hga1 Hga2 Hctxlc Hctx).
    + exact (IHHty2 rho phi theta1 theta2 gamma1 gamma2
        Hth1 Hth2 Hga1 Hga2 Hctxlc Hctx).
    + exact (IHHty3 rho phi theta1 theta2 gamma1 gamma2
        Hth1 Hth2 Hga1 Hga2 Hctxlc Hctx).
    + eapply instantiate_preserves_lc.
      * eapply has_type_locally_closed; exact Hty2.
      * exact Hth1.
      * exact Hga1.
    + eapply instantiate_preserves_lc.
      * eapply has_type_locally_closed; exact Hty2.
      * exact Hth2.
      * exact Hga2.
    + eapply instantiate_preserves_lc.
      * eapply has_type_locally_closed; exact Hty3.
      * exact Hth1.
      * exact Hga1.
    + eapply instantiate_preserves_lc.
      * eapply has_type_locally_closed; exact Hty3.
      * exact Hth2.
      * exact Hga2.
Qed.

Lemma instantiate_ty_identity : forall T,
  instantiate_ty identity_type_substitution T = T.
Proof. induction T; simpl; try rewrite IHT; try rewrite IHT1; try rewrite IHT2; reflexivity. Qed.

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
  intros t Hty U v HwfU Hv Htyv.
  assert (Hlu : locally_closed_ty U) by (eapply wf_ty_locally_closed; exact HwfU).
  assert (Hctxlc : forall x S, lookup_context x empty = Some S -> locally_closed_ty S).
  { intros x S Hlook. discriminate. }
  assert (Hctx : related_context [] (fun _ => fun _ _ => False)
    empty identity_term_substitution identity_term_substitution).
  { intros x S Hlook. discriminate. }
  pose proof (@fundamental_theorem [] empty t
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) Hty
    [] (fun _ => fun _ _ => False)
    identity_type_substitution identity_type_substitution
    identity_term_substitution identity_term_substitution
    identity_type_substitution_closed identity_type_substitution_closed
    identity_term_substitution_closed identity_term_substitution_closed
    Hctxlc Hctx) as Hfund.
  rewrite instantiate_identity in Hfund.
  eapply logical_identity_extract; eauto.
Qed.

End SystemFParametricityRecursionEasyTask.
