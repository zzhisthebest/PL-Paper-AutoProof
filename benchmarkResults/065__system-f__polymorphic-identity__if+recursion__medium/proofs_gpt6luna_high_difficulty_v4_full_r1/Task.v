(** System F parametricity benchmark, Easy variant.
    Features: if-recursion. *)

From Stdlib Require Import Arith.PeanoNat Arith.Wf_nat Lists.List Lia.
Import ListNotations.

Module SystemFParametricityIfRecursionEasyTask.

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
  | Ty_Bool : ty
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
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm
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

Notation "'Bool'" := Ty_Bool (in custom systemf_ty at level 0) : systemf_scope.
Notation "'true'" := tm_true (in custom systemf_tm at level 0) : systemf_scope.
Notation "'false'" := tm_false (in custom systemf_tm at level 0) : systemf_scope.
Notation "'if' t1 'then' t2 'else' t3" := (tm_if t1 t2 t3)
  (in custom systemf_tm at level 200, t1 custom systemf_tm, t2 custom systemf_tm, t3 custom systemf_tm at level 200) : systemf_scope.
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
  | Ty_Bool => Ty_Bool
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
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (open_tm_rec k u t1) (open_tm_rec k u t2) (open_tm_rec k u t3)
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
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (open_tm_ty_rec k U t1) (open_tm_ty_rec k U t2) (open_tm_ty_rec k U t3)
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
  | Ty_Bool => Ty_Bool
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
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (tm_ty_subst X U t1) (tm_ty_subst X U t2) (tm_ty_subst X U t3)
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
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (tm_subst x s t1) (tm_subst x s t2) (tm_subst x s t3)
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
  | lc_ty_bool : forall k, lc_ty_at k Ty_Bool
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
  | lc_tm_true : forall K k, lc_tm_at K k tm_true
  | lc_tm_false : forall K k, lc_tm_at K k tm_false
  | lc_tm_if : forall K k t1 t2 t3,
      lc_tm_at K k t1 -> lc_tm_at K k t2 -> lc_tm_at K k t3 -> lc_tm_at K k (tm_if t1 t2 t3)
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
  | v_true : value tm_true
  | v_false : value tm_false
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
  | WF_Bool : forall Delta, wf_ty Delta Ty_Bool
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
  | T_True : forall Delta Gamma, has_type Delta Gamma tm_true Ty_Bool
  | T_False : forall Delta Gamma, has_type Delta Gamma tm_false Ty_Bool
  | T_If : forall Delta Gamma t1 t2 t3 T,
      has_type Delta Gamma t1 Ty_Bool ->
      has_type Delta Gamma t2 T -> has_type Delta Gamma t3 T ->
      has_type Delta Gamma (tm_if t1 t2 t3) T
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
  | Ty_Bool => []
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
  | tm_true => []
  | tm_false => []
  | tm_if t1 t2 t3 => fv_tm t1 ++ fv_tm t2 ++ fv_tm t3
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
  | tm_true => []
  | tm_false => []
  | tm_if t1 t2 t3 => ftv_tm t1 ++ ftv_tm t2 ++ ftv_tm t3
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
  - apply lc_ty_bool.
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
  - apply lc_tm_true.
  - apply lc_tm_false.
  - eauto using lc_tm_at.
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
  - apply lc_ty_bool.
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
  - apply lc_ty_bool.
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
  - apply lc_tm_true.
  - apply lc_tm_false.
  - inversion Hlc; subst; eauto using lc_tm_at.
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
  - apply lc_tm_true.
  - apply lc_tm_false.
  - inversion Hlc; subst; eauto using lc_tm_at.
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
  | Ty_Bool => Ty_Bool
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
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (instantiate theta gamma t1) (instantiate theta gamma t2) (instantiate theta gamma t3)
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
  | EvalIfTrue : forall c t u v,
      evaluates c tm_true -> evaluates t v -> locally_closed_tm u ->
      evaluates (tm_if c t u) v
  | EvalIfFalse : forall c t u v,
      evaluates c tm_false -> locally_closed_tm t -> evaluates u v ->
      evaluates (tm_if c t u) v
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

Definition rel_env := list (tm -> tm -> Prop).
Definition rel_substitution := atom -> tm -> tm -> Prop.

Definition rel_subst_update
    (rho : rel_substitution) (X : atom) (R : tm -> tm -> Prop) : rel_substitution :=
  fun Y => if Nat.eqb X Y then R else rho Y.

Fixpoint rel_env_lookup (rs : rel_env) (i : nat) : tm -> tm -> Prop :=
  match rs, i with
  | [], _ => fun _ _ => False
  | R :: _, 0 => R
  | _ :: rs', S i' => rel_env_lookup rs' i'
  end.

Definition empty_rel : tm -> tm -> Prop := fun _ _ => False.

Fixpoint rel_env_insert (k : nat) (R : tm -> tm -> Prop) (rs : rel_env) : rel_env :=
  match k, rs with
  | 0, _ => R :: rs
  | S k', [] => empty_rel :: rel_env_insert k' R []
  | S k', r :: rs' => r :: rel_env_insert k' R rs'
  end.

Lemma rel_env_insert_lookup_lt : forall k R rs i,
  i < k -> rel_env_lookup (rel_env_insert k R rs) i = rel_env_lookup rs i.
Proof.
  induction k; intros R rs i Hlt; [lia|].
  destruct rs as [|r rs']; destruct i as [|i']; simpl in *.
  - reflexivity.
  - apply IHk. lia.
  - reflexivity.
  - apply IHk. lia.
Qed.

Lemma rel_env_insert_lookup_eq : forall k R rs,
  rel_env_lookup (rel_env_insert k R rs) k = R.
Proof.
  induction k; intros R rs; destruct rs as [|r rs']; simpl; auto.
Qed.

Lemma rel_env_insert_lookup_gt : forall k R rs i a b,
  k < i ->
  rel_env_lookup (rel_env_insert k R rs) i a b <->
  rel_env_lookup rs (i - 1) a b.
Proof.
  induction k; intros R rs i a b Hlt.
  - destruct i; [lia|]. simpl. rewrite Nat.sub_0_r. reflexivity.
  - destruct rs as [|r rs']; destruct i as [|i']; simpl in *.
    + lia.
    + apply IHk. lia.
    + lia.
    + replace (S i' - 1) with i' by lia.
      destruct i' as [|j]; [lia|]. simpl.
      replace (S j - 1) with j by lia.
      pose proof (IHk R rs' (S j) a b ltac:(lia)) as Hrec.
      simpl in Hrec. rewrite Nat.sub_0_r in Hrec. exact Hrec.
Qed.

Lemma rel_env_insert_cons_agree : forall k R R' rs Q i a b,
  (forall x y, R x y <-> R' x y) ->
  rel_env_lookup (Q :: rel_env_insert k R rs) i a b <->
  rel_env_lookup (rel_env_insert (S k) R' (Q :: rs)) i a b.
Proof.
  intros k R R' rs Q i a b Hrel.
  destruct i as [|i]; simpl; [tauto|].
  destruct (Nat.lt_trichotomy i k) as [Hlt|[Heq|Hgt]].
  - rewrite rel_env_insert_lookup_lt by exact Hlt.
    rewrite rel_env_insert_lookup_lt by lia. tauto.
  - subst i. rewrite rel_env_insert_lookup_eq, rel_env_insert_lookup_eq. apply Hrel.
  - rewrite rel_env_insert_lookup_gt by exact Hgt.
    rewrite rel_env_insert_lookup_gt by lia.
    replace (S i - S k) with (i - k) by lia. tauto.
Qed.

Fixpoint value_rel (rs : rel_env) (rho : rel_substitution) (T : ty)
    (v1 v2 : tm) {struct T} : Prop :=
  match T with
  | Ty_BVar i => rel_env_lookup rs i v1 v2
  | Ty_FVar X => rho X v1 v2
  | Ty_Arrow A B =>
      match v1, v2 with
      | tm_abs _ b1, tm_abs _ b2 =>
          value v1 /\ value v2 /\
          (forall a1 a2, value a1 -> value a2 ->
             value_rel rs rho A a1 a2 ->
             exists w1 w2,
               evaluates (open_tm b1 a1) w1 /\
               evaluates (open_tm b2 a2) w2 /\
               value_rel rs rho B w1 w2)
      | _, _ => False
      end
  | Ty_All T0 =>
      match v1, v2 with
      | tm_tabs b1, tm_tabs b2 =>
          value v1 /\ value v2 /\
          (forall U1 U2 R,
             locally_closed_ty U1 -> locally_closed_ty U2 ->
             exists w1 w2,
               evaluates (open_tm_ty b1 U1) w1 /\
               evaluates (open_tm_ty b2 U2) w2 /\
               value_rel (R :: rs) rho T0 w1 w2)
      | _, _ => False
      end
  | Ty_Bool => (v1 = tm_true /\ v2 = tm_true) \/
               (v1 = tm_false /\ v2 = tm_false)
  | Ty_Nat => v1 = v2 /\ numeric_value v1
  end.

Definition term_rel (rs : rel_env) (rho : rel_substitution) (T : ty)
    (t1 t2 : tm) : Prop :=
  exists v1 v2,
    evaluates t1 v1 /\ evaluates t2 v2 /\ value_rel rs rho T v1 v2.

Lemma value_rel_env_agree : forall T,
  forall k rs1 rs2 rho v1 v2,
    lc_ty_at k T ->
    (forall i a b, i < k -> rel_env_lookup rs1 i a b <-> rel_env_lookup rs2 i a b) ->
    (value_rel rs1 rho T v1 v2 <-> value_rel rs2 rho T v1 v2).
Proof.
  induction T; intros k rs1 rs2 rho v1 v2 HT Hagree; simpl in *.
  - inversion HT; subst. apply Hagree. assumption.
  - tauto.
  - inversion HT; subst. simpl.
    destruct v1 as [|x|A1 b1|f1 a1|b1|f1 A1| | | | | |];
    destruct v2 as [|y|A2 b2|f2 a2|b2|f2 A2| | | | | |]; simpl; try tauto.
    split.
    + intros [Hv1 [Hv2 Hfun]]. split; [exact Hv1|]. split; [exact Hv2|].
      intros a1 a2 Ha1 Ha2 Hra.
      apply (proj2 (IHT1 k rs1 rs2 rho a1 a2 H2 Hagree)) in Hra.
      destruct (Hfun a1 a2 Ha1 Ha2 Hra) as [w1 [w2 [E1 [E2 Hrb]]]].
      exists w1, w2. repeat split; try assumption.
      apply (proj1 (IHT2 k rs1 rs2 rho w1 w2 H3 Hagree)); assumption.
    + intros [Hv1 [Hv2 Hfun]]. split; [exact Hv1|]. split; [exact Hv2|].
      intros a1 a2 Ha1 Ha2 Hra.
      apply (proj1 (IHT1 k rs1 rs2 rho a1 a2 H2 Hagree)) in Hra.
      destruct (Hfun a1 a2 Ha1 Ha2 Hra) as [w1 [w2 [E1 [E2 Hrb]]]].
      exists w1, w2. repeat split; try assumption.
      apply (proj2 (IHT2 k rs1 rs2 rho w1 w2 H3 Hagree)); assumption.
  - inversion HT; subst. simpl.
    destruct v1 as [|x|A1 b1|f1 a1|b1|f1 A1| | | | | |];
    destruct v2 as [|y|A2 b2|f2 a2|b2|f2 A2| | | | | |]; simpl; try tauto.
    split.
    + intros [Hv1 [Hv2 Hpoly]]. split; [exact Hv1|]. split; [exact Hv2|].
      intros U1 U2 R HU1 HU2.
      destruct (Hpoly U1 U2 R HU1 HU2) as [w1 [w2 [E1 [E2 Hrel]]]].
      exists w1, w2. repeat split; try assumption.
      assert (Hagr : forall i a b, i < S k ->
        rel_env_lookup (R :: rs1) i a b <-> rel_env_lookup (R :: rs2) i a b).
      { intros [|i] a b Hlt; simpl; [tauto|]. apply Hagree. lia. }
      pose proof (IHT (S k) (R :: rs1) (R :: rs2) rho w1 w2 H1 Hagr) as Heq.
      apply (proj1 Heq). exact Hrel.
    + intros [Hv1 [Hv2 Hpoly]]. split; [exact Hv1|]. split; [exact Hv2|].
      intros U1 U2 R HU1 HU2.
      destruct (Hpoly U1 U2 R HU1 HU2) as [w1 [w2 [E1 [E2 Hrel]]]].
      exists w1, w2. repeat split; try assumption.
      assert (Hagr : forall i a b, i < S k ->
        rel_env_lookup (R :: rs1) i a b <-> rel_env_lookup (R :: rs2) i a b).
      { intros [|i] a b Hlt; simpl; [tauto|]. apply Hagree. lia. }
      pose proof (IHT (S k) (R :: rs1) (R :: rs2) rho w1 w2 H1 Hagr) as Heq.
      apply (proj2 Heq). exact Hrel.
  - tauto.
  - tauto.
Qed.

Lemma value_rel_rho_update_absent : forall T,
  forall rs rho X R v1 v2,
    ~ In X (fv_ty T) ->
    (value_rel rs (rel_subst_update rho X R) T v1 v2 <->
     value_rel rs rho T v1 v2).
Proof.
  induction T; intros rs rho X R v1 v2 Hfresh; simpl in *.
  - tauto.
  - assert (X <> a) as Hne by (intro Heq; apply Hfresh; simpl; left; symmetry; exact Heq).
    unfold rel_subst_update. destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E. contradiction.
    + tauto.
  - assert (~ In X (fv_ty T1)) as Hf1.
    { intro Hin. apply Hfresh. simpl. apply in_or_app. left. exact Hin. }
    assert (~ In X (fv_ty T2)) as Hf2.
    { intro Hin. apply Hfresh. simpl. apply in_or_app. right. exact Hin. }
    destruct v1 as [|x|A1 b1|f1 a1|b1|f1 A1| | | | | |];
    destruct v2 as [|y|A2 b2|f2 c2|b2|f2 A2| | | | | |]; simpl; try tauto.
    split.
    + intros [Hv1 [Hv2 Hfun]]. split; [exact Hv1|]. split; [exact Hv2|].
      intros a1 a2 Ha1 Ha2 Hra.
      apply (proj2 (IHT1 rs rho X R a1 a2 Hf1)) in Hra.
      destruct (Hfun a1 a2 Ha1 Ha2 Hra) as [w1 [w2 [E1 [E2 Hrb]]]].
      exists w1, w2. repeat split; try assumption.
      apply (proj1 (IHT2 rs rho X R w1 w2 Hf2)); assumption.
    + intros [Hv1 [Hv2 Hfun]]. split; [exact Hv1|]. split; [exact Hv2|].
      intros a1 a2 Ha1 Ha2 Hra.
      apply (proj1 (IHT1 rs rho X R a1 a2 Hf1)) in Hra.
      destruct (Hfun a1 a2 Ha1 Ha2 Hra) as [w1 [w2 [E1 [E2 Hrb]]]].
      exists w1, w2. repeat split; try assumption.
      apply (proj2 (IHT2 rs rho X R w1 w2 Hf2)); assumption.
  - destruct v1 as [|x|A1 b1|f1 c1|b1|f1 A1| | | | | |];
    destruct v2 as [|y|A2 b2|f2 c2|b2|f2 A2| | | | | |]; simpl; try tauto.
    simpl in Hfresh.
    split.
    + intros [Hv1 [Hv2 Hpoly]]. split; [exact Hv1|]. split; [exact Hv2|].
      intros U1 U2 Q HU1 HU2.
      destruct (Hpoly U1 U2 Q HU1 HU2) as [w1 [w2 [E1 [E2 Hr]]]].
      exists w1, w2. repeat split; try assumption.
      apply (proj1 (IHT (Q :: rs) rho X R w1 w2 Hfresh)); exact Hr.
    + intros [Hv1 [Hv2 Hpoly]]. split; [exact Hv1|]. split; [exact Hv2|].
      intros U1 U2 Q HU1 HU2.
      destruct (Hpoly U1 U2 Q HU1 HU2) as [w1 [w2 [E1 [E2 Hr]]]].
      exists w1, w2. repeat split; try assumption.
      apply (proj2 (IHT (Q :: rs) rho X R w1 w2 Hfresh)); exact Hr.
  - tauto.
  - tauto.
Qed.

Lemma value_rel_open_ty_rec : forall T,
  forall k rs rho U v1 v2,
    lc_ty_at (S k) T -> locally_closed_ty U ->
    value_rel (rel_env_insert k (value_rel rs rho U) rs) rho T v1 v2 <->
    value_rel rs rho (open_ty_rec k U T) v1 v2.
Proof.
  induction T; intros k rs rho U v1 v2 HT HU; simpl in *.
  - inversion HT; subst.
    destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst.
      rewrite rel_env_insert_lookup_eq. reflexivity.
    + apply Nat.eqb_neq in E. rewrite rel_env_insert_lookup_lt by lia.
      reflexivity.
  - tauto.
  - inversion HT; subst. simpl.
    destruct v1 as [|x|A1 b1|f1 a1|b1|f1 A1| | | | | |];
    destruct v2 as [|y|A2 b2|f2 a2|b2|f2 A2| | | | | |]; simpl; try tauto.
    split.
    + intros [Hv1 [Hv2 Hfun]]. split; [exact Hv1|]. split; [exact Hv2|].
      intros a1 a2 Ha1 Ha2 Hra.
      apply (proj2 (IHT1 k rs rho U a1 a2 H2 HU)) in Hra.
      destruct (Hfun a1 a2 Ha1 Ha2 Hra) as [w1 [w2 [E1 [E2 Hrb]]]].
      exists w1, w2. repeat split; try assumption.
      apply (proj1 (IHT2 k rs rho U w1 w2 H3 HU)); assumption.
    + intros [Hv1 [Hv2 Hfun]]. split; [exact Hv1|]. split; [exact Hv2|].
      intros a1 a2 Ha1 Ha2 Hra.
      apply (proj1 (IHT1 k rs rho U a1 a2 H2 HU)) in Hra.
      destruct (Hfun a1 a2 Ha1 Ha2 Hra) as [w1 [w2 [E1 [E2 Hrb]]]].
      exists w1, w2. repeat split; try assumption.
      apply (proj2 (IHT2 k rs rho U w1 w2 H3 HU)); assumption.
  - inversion HT; subst. simpl.
    destruct v1 as [|x|A1 b1|f1 a1|b1|f1 A1| | | | | |];
    destruct v2 as [|y|A2 b2|f2 a2|b2|f2 A2| | | | | |]; simpl; try tauto.
    split.
    + intros [Hv1 [Hv2 Hpoly]]. split; [exact Hv1|]. split; [exact Hv2|].
      intros U1 U2 R HU1 HU2.
      destruct (Hpoly U1 U2 R HU1 HU2) as [w1 [w2 [E1 [E2 Hrel]]]].
      exists w1, w2. repeat split; try assumption.
      assert (HUrel : forall a b, value_rel rs rho U a b <-> value_rel (R :: rs) rho U a b).
      { intros a b. eapply value_rel_env_agree.
        - exact HU.
        - intros i x y Hlt. lia. }
      assert (Hagr : forall i a b, i < S (S k) ->
        rel_env_lookup (R :: rel_env_insert k (value_rel rs rho U) rs) i a b <->
        rel_env_lookup (rel_env_insert (S k) (value_rel (R :: rs) rho U) (R :: rs)) i a b).
      { intros i a b Hi. apply rel_env_insert_cons_agree. exact HUrel. }
      pose proof (value_rel_env_agree T (S (S k))
        (R :: rel_env_insert k (value_rel rs rho U) rs)
        (rel_env_insert (S k) (value_rel (R :: rs) rho U) (R :: rs))
        rho w1 w2 H1 Hagr) as Henv.
      pose proof (IHT (S k) (R :: rs) rho U w1 w2 H1
        HU) as Hopen.
      apply (proj1 Hopen). apply (proj1 Henv). exact Hrel.
    + intros [Hv1 [Hv2 Hpoly]]. split; [exact Hv1|]. split; [exact Hv2|].
      intros U1 U2 R HU1 HU2.
      destruct (Hpoly U1 U2 R HU1 HU2) as [w1 [w2 [E1 [E2 Hrel]]]].
      exists w1, w2. repeat split; try assumption.
      assert (HUrel : forall a b, value_rel rs rho U a b <-> value_rel (R :: rs) rho U a b).
      { intros a b. eapply value_rel_env_agree.
        - exact HU.
        - intros i x y Hlt. lia. }
      assert (Hagr : forall i a b, i < S (S k) ->
        rel_env_lookup (R :: rel_env_insert k (value_rel rs rho U) rs) i a b <->
        rel_env_lookup (rel_env_insert (S k) (value_rel (R :: rs) rho U) (R :: rs)) i a b).
      { intros i a b Hi. apply rel_env_insert_cons_agree. exact HUrel. }
      pose proof (value_rel_env_agree T (S (S k))
        (R :: rel_env_insert k (value_rel rs rho U) rs)
        (rel_env_insert (S k) (value_rel (R :: rs) rho U) (R :: rs))
        rho w1 w2 H1 Hagr) as Henv.
      pose proof (IHT (S k) (R :: rs) rho U w1 w2 H1
        HU) as Hopen.
      apply (proj2 Henv). apply (proj2 Hopen). exact Hrel.
  - tauto.
  - tauto.
Qed.

Fixpoint ty_size (T : ty) : nat :=
  match T with
  | Ty_BVar _ | Ty_FVar _ | Ty_Bool | Ty_Nat => 1
  | Ty_Arrow A B => S (ty_size A + ty_size B)
  | Ty_All A => S (ty_size A)
  end.

Lemma open_ty_fvar_size : forall T k X,
  ty_size (open_ty_rec k (Ty_FVar X) T) = ty_size T.
Proof.
  induction T; intros k X; simpl; try rewrite ?IHT1, ?IHT2, ?IHT; try reflexivity.
  destruct (Nat.eqb k n); reflexivity.
Qed.

Lemma wf_ty_lc_at : forall T Delta, wf_ty Delta T -> lc_ty_at 0 T.
Proof.
  intros T Delta Hwf.
  refine (well_founded_induction lt_wf
    (fun n => forall T' Delta, ty_size T' = n -> wf_ty Delta T' -> lc_ty_at 0 T')
    _ (ty_size T) T Delta eq_refl Hwf).
  intros n IH T' Delta' Hsize Hwf'.
  destruct T'; simpl in Hsize; inversion Hwf'; subst.
  - constructor.
  - apply lc_ty_arrow.
    + eapply IH with (y := ty_size T'1); [simpl; lia|reflexivity|exact H2].
    + eapply IH with (y := ty_size T'2); [simpl; lia|reflexivity|exact H3].
  - apply lc_ty_all.
    specialize (H1 (fresh L)).
    assert (~ In (fresh L) L) as Hfresh by apply fresh_notin.
    specialize (H1 Hfresh).
    assert (ty_size (open_ty T' (Ty_FVar (fresh L))) < ty_size (Ty_All T')) as Hlt.
    { unfold open_ty. rewrite open_ty_fvar_size. simpl. lia. }
    pose proof (IH _ Hlt _ _ eq_refl H1) as Hopen.
    eapply lc_ty_at_open_inv; eauto.
  - constructor.
  - constructor.
Qed.

Lemma has_type_lc_at : forall Delta Gamma t T,
  has_type Delta Gamma t T -> lc_tm_at 0 0 t.
Proof.
  intros Delta Gamma t T Hty. induction Hty; eauto using lc_tm_at.
  - apply lc_tm_abs.
    + eapply wf_ty_lc_at; eauto.
    + assert (~ In (fresh L) L) as Hfresh by apply fresh_notin.
      specialize (H1 (fresh L) Hfresh).
      eapply lc_tm_at_open_tm_inv; eauto.
  - apply lc_tm_tabs.
    assert (~ In (fresh L) L) as Hfresh by apply fresh_notin.
    specialize (H0 (fresh L) Hfresh).
    eapply lc_tm_at_open_ty_inv; eauto.
  - apply lc_tm_tapp.
    + assumption.
    + eapply wf_ty_lc_at; eauto.
Qed.

Lemma instantiate_ty_lc_at : forall T k theta,
  lc_ty_at k T -> type_substitution_closed theta ->
  lc_ty_at k (instantiate_ty theta T).
Proof.
  induction T; intros k theta Hlc Htheta; simpl in *.
  - inversion Hlc; subst. constructor; assumption.
  - eapply lc_ty_at_monotone; [apply Htheta|lia].
  - inversion Hlc; subst. constructor; eauto.
  - inversion Hlc; subst. constructor. eauto.
  - constructor.
  - constructor.
Qed.

Lemma instantiate_lc_at : forall t K k theta gamma,
  lc_tm_at K k t -> type_substitution_closed theta ->
  term_substitution_closed gamma ->
  lc_tm_at K k (instantiate theta gamma t).
Proof.
  induction t; intros K k theta gamma Hlc Htheta Hgamma; simpl in *.
  - inversion Hlc; subst. constructor; assumption.
  - eapply lc_tm_at_monotone; [apply Hgamma|lia|lia].
  - inversion Hlc; subst. apply lc_tm_abs.
    + eapply instantiate_ty_lc_at; eauto.
    + eapply IHt; eauto.
  - inversion Hlc; subst. apply lc_tm_app; eauto.
  - inversion Hlc; subst. apply lc_tm_tabs. eapply IHt; eauto.
  - inversion Hlc; subst. apply lc_tm_tapp.
    + eapply IHt; eauto.
    + eapply instantiate_ty_lc_at; eauto.
  - constructor.
  - constructor.
  - inversion Hlc; subst. eauto using lc_tm_at.
  - constructor.
  - inversion Hlc; subst. eauto using lc_tm_at.
  - inversion Hlc; subst. eauto using lc_tm_at.
Qed.

Lemma instantiate_ty_open_rec : forall T theta X U k,
  type_substitution_closed theta -> locally_closed_ty U ->
  ~ In X (fv_ty T) ->
  instantiate_ty (type_subst_update theta X U)
    (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k U (instantiate_ty theta T).
Proof.
  induction T; intros theta X U k Htheta HU Hfresh; simpl in *.
  - destruct (Nat.eqb k n).
    + unfold type_subst_update. cbn [instantiate_ty].
      rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - unfold type_subst_update.
    destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply Hfresh. left. reflexivity.
    + rewrite open_ty_rec_lc_at; [reflexivity|].
      eapply lc_ty_at_monotone; [apply Htheta|lia].
  - assert (~ In X (fv_ty T1)) as Hf1.
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (~ In X (fv_ty T2)) as Hf2.
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    rewrite (IHT1 theta X U k Htheta HU Hf1).
    rewrite (IHT2 theta X U k Htheta HU Hf2). reflexivity.
  - rewrite (IHT theta X U (S k) Htheta HU Hfresh). reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma instantiate_ty_open : forall T theta X U,
  type_substitution_closed theta -> locally_closed_ty U ->
  ~ In X (fv_ty T) ->
  instantiate_ty (type_subst_update theta X U)
    (open_ty T (Ty_FVar X)) =
  open_ty (instantiate_ty theta T) U.
Proof. intros. unfold open_ty. eapply instantiate_ty_open_rec; eauto. Qed.

Lemma instantiate_tm_open_rec : forall t theta gamma X U k,
  type_substitution_closed theta -> locally_closed_ty U ->
  term_substitution_closed gamma ->
  ~ In X (ftv_tm t) ->
  instantiate (type_subst_update theta X U) gamma
    (open_tm_ty_rec k (Ty_FVar X) t) =
  open_tm_ty_rec k U (instantiate theta gamma t).
Proof.
  induction t; intros theta gamma X U k Htheta HU Hgamma Hfresh; simpl in *.
  - reflexivity.
  - pose proof (Hgamma a) as Hlc.
    eapply lc_tm_at_monotone in Hlc; [|lia|lia].
    rewrite (open_tm_ty_rec_lc_at (gamma a) k 0 U Hlc). reflexivity.
  - assert (~ In X (fv_ty t)) as HfT.
    { intro Hin. apply Hfresh. simpl. apply in_or_app. left. exact Hin. }
    assert (~ In X (ftv_tm t0)) as Hft.
    { intro Hin. apply Hfresh. simpl. apply in_or_app. right. exact Hin. }
    rewrite (instantiate_ty_open_rec t theta X U k Htheta HU HfT).
    rewrite (IHt theta gamma X U k Htheta HU Hgamma Hft). reflexivity.
  - assert (~ In X (ftv_tm t1)) as Hf1.
    { intro Hin. apply Hfresh. simpl. apply in_or_app. left. exact Hin. }
    assert (~ In X (ftv_tm t2)) as Hf2.
    { intro Hin. apply Hfresh. simpl. apply in_or_app. right. exact Hin. }
    rewrite (IHt1 theta gamma X U k Htheta HU Hgamma Hf1).
    rewrite (IHt2 theta gamma X U k Htheta HU Hgamma Hf2). reflexivity.
  - rewrite IHt; try assumption. reflexivity.
  - assert (~ In X (ftv_tm t)) as Hft.
    { intro Hin. apply Hfresh. simpl. apply in_or_app. left. exact Hin. }
    assert (~ In X (fv_ty t0)) as HfT.
    { intro Hin. apply Hfresh. simpl. apply in_or_app. right. exact Hin. }
    rewrite (IHt theta gamma X U k Htheta HU Hgamma Hft).
    rewrite (instantiate_ty_open_rec t0 theta X U k Htheta HU HfT). reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2, IHt3; try (simpl in Hfresh; repeat rewrite in_app_iff in Hfresh; tauto).
  - reflexivity.
  - rewrite IHt; try assumption. reflexivity.
  - rewrite IHt1, IHt2, IHt3; try (simpl in Hfresh; repeat rewrite in_app_iff in Hfresh; tauto).
Qed.

Lemma instantiate_tm_open_ty : forall t theta gamma X U,
  type_substitution_closed theta -> locally_closed_ty U ->
  term_substitution_closed gamma ->
  ~ In X (ftv_tm t) ->
  instantiate (type_subst_update theta X U) gamma
    (open_tm_ty t (Ty_FVar X)) =
  open_tm_ty (instantiate theta gamma t) U.
Proof. intros. unfold open_tm_ty. eapply instantiate_tm_open_rec; eauto. Qed.

Lemma instantiate_open_tm_rec : forall t theta gamma k u,
  term_substitution_closed gamma ->
  instantiate theta gamma (open_tm_rec k u t) =
  open_tm_rec k (instantiate theta gamma u) (instantiate theta gamma t).
Proof.
  induction t; intros theta gamma k u Hgamma; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - pose proof (Hgamma a) as Hlc.
    eapply lc_tm_at_monotone in Hlc; [|lia|lia].
    rewrite (open_tm_rec_lc_at (gamma a) 0 k (instantiate theta gamma u) Hlc).
    reflexivity.
  - f_equal. exact (IHt theta gamma (S k) u Hgamma).
  - rewrite (IHt1 theta gamma k u Hgamma), (IHt2 theta gamma k u Hgamma). reflexivity.
  - f_equal. exact (IHt theta gamma k u Hgamma).
  - f_equal. exact (IHt theta gamma k u Hgamma).
  - reflexivity.
  - reflexivity.
  - rewrite (IHt1 theta gamma k u Hgamma), (IHt2 theta gamma k u Hgamma),
      (IHt3 theta gamma k u Hgamma). reflexivity.
  - reflexivity.
  - f_equal. exact (IHt theta gamma k u Hgamma).
  - rewrite (IHt1 theta gamma k u Hgamma), (IHt2 theta gamma k u Hgamma),
      (IHt3 theta gamma k u Hgamma). reflexivity.
Qed.

Lemma instantiate_open_tm : forall t theta gamma u,
  term_substitution_closed gamma ->
  instantiate theta gamma (open_tm t u) =
  open_tm (instantiate theta gamma t) (instantiate theta gamma u).
Proof. intros. unfold open_tm. eapply instantiate_open_tm_rec; eauto. Qed.

Lemma instantiate_term_update_absent : forall t theta gamma x u,
  ~ In x (fv_tm t) ->
  instantiate theta (term_subst_update gamma x u) t =
  instantiate theta gamma t.
Proof.
  induction t; intros theta gamma x u Hfresh; simpl in *.
  - reflexivity.
  - assert (x <> a) as Hne by (intro Heq; apply Hfresh; left; symmetry; exact Heq).
    unfold term_subst_update. destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E. contradiction.
    + reflexivity.
  - rewrite (IHt theta gamma x u Hfresh). reflexivity.
  - assert (~ In x (fv_tm t1)) as Hf1.
    { intro Hin. apply Hfresh. simpl. apply in_or_app. left. exact Hin. }
    assert (~ In x (fv_tm t2)) as Hf2.
    { intro Hin. apply Hfresh. simpl. apply in_or_app. right. exact Hin. }
    rewrite (IHt1 theta gamma x u Hf1), (IHt2 theta gamma x u Hf2). reflexivity.
  - rewrite (IHt theta gamma x u Hfresh). reflexivity.
  - rewrite (IHt theta gamma x u Hfresh). reflexivity.
  - reflexivity.
  - reflexivity.
  - assert (~ In x (fv_tm t1)) as Hf1.
    { intro Hin. apply Hfresh. simpl. apply in_or_app. left. exact Hin. }
    assert (~ In x (fv_tm t2)) as Hf2.
    { intro Hin. apply Hfresh. simpl. repeat rewrite in_app_iff. right. left. exact Hin. }
    assert (~ In x (fv_tm t3)) as Hf3.
    { intro Hin. apply Hfresh. simpl. repeat rewrite in_app_iff. right. right. exact Hin. }
    rewrite (IHt1 theta gamma x u Hf1), (IHt2 theta gamma x u Hf2),
      (IHt3 theta gamma x u Hf3). reflexivity.
  - reflexivity.
  - rewrite (IHt theta gamma x u Hfresh). reflexivity.
  - assert (~ In x (fv_tm t1)) as Hf1.
    { intro Hin. apply Hfresh. simpl. apply in_or_app. left. exact Hin. }
    assert (~ In x (fv_tm t2)) as Hf2.
    { intro Hin. apply Hfresh. simpl. repeat rewrite in_app_iff. right. left. exact Hin. }
    assert (~ In x (fv_tm t3)) as Hf3.
    { intro Hin. apply Hfresh. simpl. repeat rewrite in_app_iff. right. right. exact Hin. }
    rewrite (IHt1 theta gamma x u Hf1), (IHt2 theta gamma x u Hf2),
      (IHt3 theta gamma x u Hf3). reflexivity.
Qed.

Lemma evaluates_value : forall t v, evaluates t v -> value v.
Proof.
  intros t v He. induction He; eauto using value.
  - apply v_nat. constructor; assumption.
Qed.

Lemma eval_app_rel : forall rs rho A B f1 f2 a1 a2,
  term_rel rs rho (Ty_Arrow A B) f1 f2 ->
  term_rel rs rho A a1 a2 ->
  exists w1 w2,
    evaluates (tm_app f1 a1) w1 /\ evaluates (tm_app f2 a2) w2 /\
    value_rel rs rho B w1 w2.
Proof.
  intros rs rho A B f1 f2 a1 a2
    [vf1 [vf2 [Ef1 [Ef2 Hf]]]] [va1 [va2 [Ea1 [Ea2 Ha]]]].
  destruct vf1 as [|x|U1 b1|f a|b|f U3| | | | | |];
  destruct vf2 as [|y|U2 b2|g c|d|g U4| | | | | |]; simpl in Hf; try contradiction.
  destruct Hf as [_ [_ Hfun]].
  pose proof (Hfun va1 va2 (evaluates_value _ _ Ea1) (evaluates_value _ _ Ea2) Ha)
    as [w1 [w2 [Eb1 [Eb2 Hrel]]]].
  exists w1, w2. split.
  - eapply EvalApp; eauto.
  - split.
    + eapply EvalApp; eauto.
    + exact Hrel.
Qed.

Definition value_env_rel (Gamma : context) (rs : rel_env) (rho : rel_substitution)
    (gamma1 gamma2 : term_substitution) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    value (gamma1 x) /\ value (gamma2 x) /\ value_rel rs rho T (gamma1 x) (gamma2 x).

Lemma lookup_context_in_dom : forall Gamma x T,
  lookup_context x Gamma = Some T -> In x (dom_context Gamma).
Proof.
  induction Gamma as [|[y U] Gamma IH]; intros x T H; simpl in *; try discriminate.
  destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. subst. simpl. auto.
  - right. apply (IH x T). exact H.
Qed.

Lemma lookup_context_in_ftv : forall Gamma x T X,
  lookup_context x Gamma = Some T -> In X (fv_ty T) -> In X (ftv_context Gamma).
Proof.
  induction Gamma as [|[y U] Gamma IH]; intros x T X Hlookup Hin; simpl in *; try discriminate.
  destruct (Nat.eqb x y) eqn:E.
  - inversion Hlookup; subst. apply in_or_app. left. exact Hin.
  - apply in_or_app. right. eapply IH; eauto.
Qed.

Lemma eval_natrec_related : forall n,
  numeric_value n ->
  forall rs rho T n1 n2 b1 b2 s1 s2,
    evaluates n1 n -> evaluates n2 n ->
    term_rel rs rho T b1 b2 ->
    term_rel rs rho (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s1 s2 ->
    exists r1 r2,
      evaluates (tm_natrec n1 b1 s1) r1 /\
      evaluates (tm_natrec n2 b2 s2) r2 /\
      value_rel rs rho T r1 r2.
Proof.
  intros n Hnum. induction Hnum; intros rs rho T n1 n2 b1 b2 s1 s2 En1 En2 Hb Hs.
  - destruct Hb as [vb1 [vb2 [Eb1 [Eb2 Hvb]]]].
    destruct Hs as [vs1 [vs2 [Es1 [Es2 Hvs]]]].
    exists vb1, vb2. split; [eapply EvalRecZero; eauto|].
    split; [eapply EvalRecZero; eauto|exact Hvb].
  - destruct Hb as [vb1 [vb2 [Eb1 [Eb2 Hvb]]]].
    destruct Hs as [vs1 [vs2 [Es1 [Es2 Hvs]]]].
    assert (Hkn : term_rel rs rho Ty_Nat n n).
    { unfold term_rel. exists n, n. split; [apply EvalValue; apply v_nat; exact Hnum|].
      split; [apply EvalValue; apply v_nat; exact Hnum|]. split; [reflexivity|exact Hnum]. }
    assert (Hb' : term_rel rs rho T b1 b2).
    { exists vb1, vb2. repeat split; assumption. }
    assert (Hs' : term_rel rs rho (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s1 s2).
    { exists vs1, vs2. repeat split; assumption. }
    assert (Hbval : term_rel rs rho T vb1 vb2).
    { unfold term_rel. exists vb1, vb2. split; [apply EvalValue; eapply evaluates_value; eauto|].
      split; [apply EvalValue; eapply evaluates_value; eauto|exact Hvb]. }
    assert (Hsval : term_rel rs rho (Ty_Arrow Ty_Nat (Ty_Arrow T T)) vs1 vs2).
    { unfold term_rel. exists vs1, vs2. split; [apply EvalValue; eapply evaluates_value; eauto|].
      split; [apply EvalValue; eapply evaluates_value; eauto|exact Hvs]. }
    destruct (IHHnum rs rho T n n vb1 vb2 vs1 vs2
      (EvalValue n (v_nat n Hnum)) (EvalValue n (v_nat n Hnum)) Hbval Hsval)
      as [r1 [r2 [Er1 [Er2 Hrec]]]].
    assert (Hvsval : term_rel rs rho (Ty_Arrow Ty_Nat (Ty_Arrow T T)) vs1 vs2).
    { unfold term_rel. exists vs1, vs2. split; [apply EvalValue; eapply evaluates_value; eauto|].
      split; [apply EvalValue; eapply evaluates_value; eauto|exact Hvs]. }
    destruct (eval_app_rel rs rho Ty_Nat (Ty_Arrow T T) vs1 vs2 n n Hvsval Hkn)
      as [g1 [g2 [Eg1 [Eg2 Hg]]]].
    assert (Hstepterm : term_rel rs rho (Ty_Arrow T T)
      (tm_app vs1 n) (tm_app vs2 n)).
    { exists g1, g2. repeat split; assumption. }
    assert (Hrecterm : term_rel rs rho T
      (tm_natrec n vb1 vs1) (tm_natrec n vb2 vs2)).
    { exists r1, r2. repeat split; assumption. }
    destruct (eval_app_rel rs rho T T (tm_app vs1 n) (tm_app vs2 n)
      (tm_natrec n vb1 vs1) (tm_natrec n vb2 vs2) Hstepterm Hrecterm)
      as [q1 [q2 [Eq1 [Eq2 Hq]]]].
    exists q1, q2. split.
    + eapply EvalRecSucc with (k := n); eauto using evaluates_value.
    + split.
      * eapply EvalRecSucc with (k := n); eauto using evaluates_value.
      * exact Hq.
Qed.

Lemma value_env_rel_update : forall Gamma rs rho gamma1 gamma2 x T a1 a2,
  ~ In x (dom_context Gamma) ->
  value a1 -> value a2 -> value_rel rs rho T a1 a2 ->
  value_env_rel Gamma rs rho gamma1 gamma2 ->
  value_env_rel (update Gamma x T) rs rho
    (term_subst_update gamma1 x a1) (term_subst_update gamma2 x a2).
Proof.
  intros Gamma rs rho gamma1 gamma2 x T a1 a2 Hfresh Ha1 Ha2 Hrel Henv.
  intros y S Hlookup.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y.
    rewrite lookup_context_update_eq in Hlookup. inversion Hlookup; subst S.
    unfold term_subst_update. rewrite Nat.eqb_refl. repeat split; assumption.
  - apply Nat.eqb_neq in E.
    rewrite lookup_context_update_neq in Hlookup by congruence.
    specialize (Henv y S Hlookup) as [Hy1 [Hy2 Hyr]].
    unfold term_subst_update. destruct (Nat.eqb x y) eqn:E2.
    + apply Nat.eqb_eq in E2. congruence.
    +
    repeat split; assumption.
Qed.

Lemma has_type_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> lc_ty_at 0 T.
Proof.
  intros Delta Gamma t T Hty. induction Hty; eauto using lc_ty_at.
  - eapply wf_ty_lc_at; eauto.
  - apply lc_ty_arrow.
    + eapply wf_ty_lc_at; eauto.
    + specialize (H1 (fresh L)).
      assert (~ In (fresh L) L) as Hfresh by apply fresh_notin.
      specialize (H1 Hfresh). exact H1.
  - inversion IHHty1; subst. assumption.
  - apply lc_ty_all.
    specialize (H0 (fresh L)).
    assert (~ In (fresh L) L) as Hfresh by apply fresh_notin.
    specialize (H0 Hfresh).
    eapply lc_ty_at_open_inv; eauto.
  - inversion IHHty; subst.
    eapply lc_ty_at_open; [eassumption|].
    eapply wf_ty_lc_at; eauto.
Qed.

Lemma fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  locally_closed_tm t ->
  forall theta1 theta2 rho rs gamma1 gamma2,
    type_substitution_closed theta1 -> type_substitution_closed theta2 ->
    term_substitution_closed gamma1 -> term_substitution_closed gamma2 ->
    value_env_rel Gamma rs rho gamma1 gamma2 ->
    term_rel rs rho T (instantiate theta1 gamma1 t) (instantiate theta2 gamma2 t).
Proof.
  intros Delta Gamma t T Hty Hlc. induction Hty;
    intros theta1 theta2 rho rs gamma1 gamma2 Htheta1 Htheta2 Hgamma1 Hgamma2 Henv.
  - simpl. destruct (Henv x T H) as [Hv1 [Hv2 Hrel]].
    unfold term_rel. simpl. exists (gamma1 x), (gamma2 x).
    repeat split; try assumption; constructor; assumption.
  - set (x := fresh (L ++ dom_context Gamma ++ fv_tm t2)).
    assert (Hnotall : ~ In x (L ++ dom_context Gamma ++ fv_tm t2)).
    { unfold x. apply fresh_notin. }
    assert (HxL : ~ In x L).
    { intro Hin. apply Hnotall. apply in_or_app. left. exact Hin. }
    assert (Hxdom : ~ In x (dom_context Gamma)).
    { intro Hin. apply Hnotall. apply in_or_app. right. apply in_or_app. left. exact Hin. }
    assert (Hxbody : ~ In x (fv_tm t2)).
    { intro Hin. apply Hnotall. apply in_or_app. right. apply in_or_app. right. exact Hin. }
    simpl. unfold term_rel. simpl.
    exists (tm_abs (instantiate_ty theta1 T1) (instantiate theta1 gamma1 t2)),
      (tm_abs (instantiate_ty theta2 T1) (instantiate theta2 gamma2 t2)).
    split; [apply EvalValue; apply v_abs;
      exact (instantiate_lc_at (tm_abs T1 t2) 0 0 theta1 gamma1 Hlc Htheta1 Hgamma1)|].
    split; [apply EvalValue; apply v_abs;
      exact (instantiate_lc_at (tm_abs T1 t2) 0 0 theta2 gamma2 Hlc Htheta2 Hgamma2)|].
    simpl. split.
    + apply v_abs. exact (instantiate_lc_at (tm_abs T1 t2) 0 0 theta1 gamma1 Hlc Htheta1 Hgamma1).
    + split.
      * apply v_abs. exact (instantiate_lc_at (tm_abs T1 t2) 0 0 theta2 gamma2 Hlc Htheta2 Hgamma2).
      * intros a1 a2 Ha1 Ha2 Harg.
        assert (Henv' : value_env_rel (update Gamma x T1) rs rho
          (term_subst_update gamma1 x a1) (term_subst_update gamma2 x a2)).
        { eapply value_env_rel_update; eauto. }
        assert (Hg1' : term_substitution_closed (term_subst_update gamma1 x a1)).
        { apply term_subst_update_closed; [exact Hgamma1|apply value_regular; exact Ha1]. }
        assert (Hg2' : term_substitution_closed (term_subst_update gamma2 x a2)).
        { apply term_subst_update_closed; [exact Hgamma2|apply value_regular; exact Ha2]. }
        assert (Hopenlc : locally_closed_tm (open_tm t2 (tm_fvar x))).
        { eapply has_type_lc_at. apply H0. exact HxL. }
        pose proof (H1 x HxL Hopenlc theta1 theta2 rho rs
          (term_subst_update gamma1 x a1) (term_subst_update gamma2 x a2)
          Htheta1 Htheta2 Hg1' Hg2' Henv') as Hbody.
        assert (Ebody1 : instantiate theta1 (term_subst_update gamma1 x a1)
            (open_tm t2 (tm_fvar x)) = open_tm (instantiate theta1 gamma1 t2) a1).
        { rewrite (instantiate_open_tm t2 theta1 (term_subst_update gamma1 x a1)
            (tm_fvar x) Hg1').
          simpl. unfold term_subst_update. rewrite Nat.eqb_refl.
          f_equal. apply instantiate_term_update_absent. exact Hxbody. }
        assert (Ebody2 : instantiate theta2 (term_subst_update gamma2 x a2)
            (open_tm t2 (tm_fvar x)) = open_tm (instantiate theta2 gamma2 t2) a2).
        { rewrite (instantiate_open_tm t2 theta2 (term_subst_update gamma2 x a2)
            (tm_fvar x) Hg2').
          simpl. unfold term_subst_update. rewrite Nat.eqb_refl.
          f_equal. apply instantiate_term_update_absent. exact Hxbody. }
        unfold term_rel in Hbody. rewrite Ebody1, Ebody2 in Hbody.
        exact Hbody.
  - (* application *)
    pose proof (IHHty1 (has_type_lc_at _ _ _ _ Hty1) theta1 theta2 rho rs gamma1 gamma2
      Htheta1 Htheta2 Hgamma1 Hgamma2 Henv) as Hf.
    pose proof (IHHty2 (has_type_lc_at _ _ _ _ Hty2) theta1 theta2 rho rs gamma1 gamma2
      Htheta1 Htheta2 Hgamma1 Hgamma2 Henv) as Ha.
    unfold term_rel in *. simpl. eapply eval_app_rel; eauto.
  - (* type abstraction *)
    set (X := fresh (L ++ fv_ty T ++ ftv_tm t ++ ftv_context Gamma)).
    assert (HXnotall : ~ In X (L ++ fv_ty T ++ ftv_tm t ++ ftv_context Gamma)).
    { unfold X. apply fresh_notin. }
    assert (HXL : ~ In X L).
    { intro Hin. apply HXnotall. apply in_or_app. left. exact Hin. }
    assert (HXty : ~ In X (fv_ty T)).
    { intro Hin. apply HXnotall. apply in_or_app. right. apply in_or_app. left. exact Hin. }
    assert (HXterm : ~ In X (ftv_tm t)).
    { intro Hin. apply HXnotall. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hin. }
    assert (HXctx : ~ In X (ftv_context Gamma)).
    { intro Hin. apply HXnotall. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact Hin. }
    simpl. unfold term_rel. simpl.
    exists (tm_tabs (instantiate theta1 gamma1 t)), (tm_tabs (instantiate theta2 gamma2 t)).
    split; [apply EvalValue; apply v_tabs;
      exact (instantiate_lc_at (tm_tabs t) 0 0 theta1 gamma1 Hlc Htheta1 Hgamma1)|].
    split; [apply EvalValue; apply v_tabs;
      exact (instantiate_lc_at (tm_tabs t) 0 0 theta2 gamma2 Hlc Htheta2 Hgamma2)|].
    simpl. split.
    + apply v_tabs. exact (instantiate_lc_at (tm_tabs t) 0 0 theta1 gamma1 Hlc Htheta1 Hgamma1).
    + split.
      * apply v_tabs. exact (instantiate_lc_at (tm_tabs t) 0 0 theta2 gamma2 Hlc Htheta2 Hgamma2).
      * intros U1 U2 R HU1 HU2.
        assert (Henv' : value_env_rel Gamma rs (rel_subst_update rho X R) gamma1 gamma2).
        { intros y S Hlook.
          destruct (Henv y S Hlook) as [Hv1 [Hv2 Hr]].
          assert (~ In X (fv_ty S)) as HnotS.
          { intro Hin. apply HXctx. eapply lookup_context_in_ftv; eauto. }
          pose proof (value_rel_rho_update_absent S rs rho X R (gamma1 y) (gamma2 y) HnotS) as Hsame.
          repeat split; try assumption. apply (proj2 Hsame); exact Hr. }
        assert (Hbodylc : locally_closed_tm (open_tm_ty t (Ty_FVar X))).
        { exact (@has_type_lc_at (X :: Delta) Gamma
            (open_tm_ty t (Ty_FVar X)) (open_ty T (Ty_FVar X)) (H X HXL)). }
        pose proof (H0 X HXL Hbodylc
          (type_subst_update theta1 X U1) (type_subst_update theta2 X U2)
          (rel_subst_update rho X R) rs gamma1 gamma2
          (type_subst_update_closed theta1 X U1 Htheta1 HU1)
          (type_subst_update_closed theta2 X U2 Htheta2 HU2)
          Hgamma1 Hgamma2 Henv') as Hbody.
        assert (Eopen1 : instantiate (type_subst_update theta1 X U1) gamma1
            (open_tm_ty t (Ty_FVar X)) = open_tm_ty (instantiate theta1 gamma1 t) U1).
        { eapply instantiate_tm_open_ty; eauto. }
        assert (Eopen2 : instantiate (type_subst_update theta2 X U2) gamma2
            (open_tm_ty t (Ty_FVar X)) = open_tm_ty (instantiate theta2 gamma2 t) U2).
        { eapply instantiate_tm_open_ty; eauto. }
        unfold term_rel in Hbody. rewrite Eopen1, Eopen2 in Hbody.
        destruct Hbody as [w1 [w2 [E1 [E2 Hr]]]].
        exists w1, w2. split; [exact E1|]. split; [exact E2|].
        assert (Hopened : value_rel rs (rel_subst_update rho X R)
          (open_ty T (Ty_FVar X)) w1 w2) by exact Hr.
        pose proof (@has_type_type_lc (X :: Delta) Gamma (open_tm_ty t (Ty_FVar X))
          (open_ty T (Ty_FVar X)) (H X HXL)) as HTopen.
        pose proof (lc_ty_at_open_inv T 0 X HTopen) as HTlc.
        pose proof (value_rel_open_ty_rec T 0 rs (rel_subst_update rho X R)
          (Ty_FVar X) w1 w2 HTlc (lc_ty_fvar 0 X)) as Hopen.
        cbn [value_rel rel_subst_update] in Hopen.
        unfold rel_subst_update in Hopen. rewrite Nat.eqb_refl in Hopen.
        apply (proj1 (value_rel_rho_update_absent T (R :: rs) rho X R w1 w2 HXty)).
        apply (proj2 Hopen). exact Hopened.
  - (* type application *)
    pose proof (IHHty (has_type_lc_at _ _ _ _ Hty) theta1 theta2 rho rs gamma1 gamma2
      Htheta1 Htheta2 Hgamma1 Hgamma2 Henv) as Hpolyterm.
    unfold term_rel in Hpolyterm.
    destruct Hpolyterm as [f1 [f2 [Ef1 [Ef2 Hforall]]]].
    destruct f1 as [|x1|A1 b1|f1 a1|b1|f1 A1| | | | | |];
    destruct f2 as [|x2|A2 b2|f2 a2|b2|f2 A2| | | | | |]; simpl in Hforall; try contradiction.
    destruct Hforall as [_ [_ Hpoly]].
    assert (HU1 : locally_closed_ty (instantiate_ty theta1 U)).
    { eapply instantiate_ty_lc_at; [eapply wf_ty_lc_at; eauto|exact Htheta1]. }
    assert (HU2 : locally_closed_ty (instantiate_ty theta2 U)).
    { eapply instantiate_ty_lc_at; [eapply wf_ty_lc_at; eauto|exact Htheta2]. }
    destruct (Hpoly (instantiate_ty theta1 U) (instantiate_ty theta2 U)
      (value_rel rs rho U) HU1 HU2) as [w1 [w2 [Ebody1 [Ebody2 Hrel]]]].
    pose proof (@has_type_type_lc Delta Gamma t (Ty_All T) Hty) as Halllc.
    inversion Halllc; subst.
    pose proof (value_rel_open_ty_rec T 0 rs rho U w1 w2 H2
      (wf_ty_lc_at U Delta H)) as Hopen.
    unfold term_rel. simpl. exists w1, w2. split.
    + eapply EvalTApp; eauto.
    + split.
      * eapply EvalTApp; eauto.
      * apply (proj1 Hopen). exact Hrel.
  - simpl. unfold term_rel. simpl. exists tm_true, tm_true.
    split; [apply EvalValue; constructor|].
    split; [apply EvalValue; constructor|]. left; split; reflexivity.
  - simpl. unfold term_rel. simpl. exists tm_false, tm_false.
    split; [apply EvalValue; constructor|].
    split; [apply EvalValue; constructor|]. right; split; reflexivity.
  - (* conditional *)
    pose proof (IHHty1 (has_type_lc_at _ _ _ _ Hty1) theta1 theta2 rho rs gamma1 gamma2
      Htheta1 Htheta2 Hgamma1 Hgamma2 Henv) as Hc.
    pose proof (IHHty2 (has_type_lc_at _ _ _ _ Hty2) theta1 theta2 rho rs gamma1 gamma2
      Htheta1 Htheta2 Hgamma1 Hgamma2 Henv) as Hthen.
    pose proof (IHHty3 (has_type_lc_at _ _ _ _ Hty3) theta1 theta2 rho rs gamma1 gamma2
      Htheta1 Htheta2 Hgamma1 Hgamma2 Henv) as Helse.
    unfold term_rel in Hc. destruct Hc as [c1 [c2 [Ec1 [Ec2 Hbool]]]].
    simpl in Hbool. destruct Hbool as [[-> ->]|[-> ->]].
    + destruct Hthen as [v1 [v2 [Et1 [Et2 Hr]]]].
      unfold term_rel. simpl. exists v1, v2. split.
      * eapply EvalIfTrue; [exact Ec1|exact Et1|].
        eapply instantiate_lc_at; [exact (has_type_lc_at _ _ _ _ Hty3)|exact Htheta1|exact Hgamma1].
      * split.
        -- eapply EvalIfTrue; [exact Ec2|exact Et2|].
           eapply instantiate_lc_at; [exact (has_type_lc_at _ _ _ _ Hty3)|exact Htheta2|exact Hgamma2].
        -- exact Hr.
    + destruct Helse as [v1 [v2 [Ee1 [Ee2 Hr]]]].
      unfold term_rel. simpl. exists v1, v2. split.
      * eapply EvalIfFalse; [exact Ec1| |exact Ee1].
        eapply instantiate_lc_at; [exact (has_type_lc_at _ _ _ _ Hty2)|exact Htheta1|exact Hgamma1].
      * split.
        -- eapply EvalIfFalse; [exact Ec2| |exact Ee2].
           eapply instantiate_lc_at; [exact (has_type_lc_at _ _ _ _ Hty2)|exact Htheta2|exact Hgamma2].
        -- exact Hr.
  - simpl. unfold term_rel. simpl. exists tm_zero, tm_zero.
    split; [apply EvalValue; apply v_nat; constructor|].
    split; [apply EvalValue; apply v_nat; constructor|].
    split; [reflexivity|constructor].
  - (* successor *)
    pose proof (IHHty (has_type_lc_at _ _ _ _ Hty) theta1 theta2 rho rs gamma1 gamma2
      Htheta1 Htheta2 Hgamma1 Hgamma2 Henv) as Hn.
    unfold term_rel in Hn. destruct Hn as [n1 [n2 [E1 [E2 Hnr]]]].
    simpl in Hnr. destruct Hnr as [Heq Hnum]. subst n2.
    unfold term_rel. simpl. exists (tm_succ n1), (tm_succ n1).
    split; [eapply EvalSucc; eauto|].
    split; [eapply EvalSucc; eauto|].
    split; [reflexivity|constructor; exact Hnum].
  - (* natural recursion *)
    pose proof (IHHty1 (has_type_lc_at _ _ _ _ Hty1) theta1 theta2 rho rs gamma1 gamma2
      Htheta1 Htheta2 Hgamma1 Hgamma2 Henv) as Hn.
    pose proof (IHHty2 (has_type_lc_at _ _ _ _ Hty2) theta1 theta2 rho rs gamma1 gamma2
      Htheta1 Htheta2 Hgamma1 Hgamma2 Henv) as Hb.
    pose proof (IHHty3 (has_type_lc_at _ _ _ _ Hty3) theta1 theta2 rho rs gamma1 gamma2
      Htheta1 Htheta2 Hgamma1 Hgamma2 Henv) as Hs.
    unfold term_rel in Hn. destruct Hn as [n1 [n2 [En1 [En2 Hnr]]]].
    simpl in Hnr. destruct Hnr as [Heq Hnum]. subst n2.
    simpl. eapply eval_natrec_related; eauto.
Qed.

Lemma evaluates_lc : forall t v, evaluates t v -> locally_closed_tm t.
Proof.
  intros t v He. induction He; simpl; eauto using lc_tm_at, value_regular.
  - apply lc_tm_app; assumption.
  - apply lc_tm_tapp; assumption.
  - apply lc_tm_if; assumption.
  - apply lc_tm_if; assumption.
  - apply lc_tm_succ. assumption.
  - apply lc_tm_rec; assumption.
  - apply lc_tm_rec; assumption.
Qed.

Lemma evaluates_multi : forall t v, evaluates t v -> t -->* v.
Proof.
  intros t v He. induction He.
  - constructor.
  - eapply multi_trans.
    + eapply multi_app_left; [exact IHHe1|exact (evaluates_lc arg v He2)].
    + eapply multi_trans.
      * eapply multi_app_right.
        -- exact (evaluates_value f (tm_abs U body) He1).
        -- exact IHHe2.
      * eapply multi_trans.
        -- eapply multi_step.
           ++ apply ST_AppAbs.
              ** exact (value_regular (tm_abs U body) (evaluates_value f (tm_abs U body) He1)).
              ** exact (evaluates_value arg v He2).
           ++ constructor.
        -- exact IHHe3.
  - eapply multi_trans.
    + eapply multi_tapp; [exact IHHe1|exact H].
    + eapply multi_step.
      * apply ST_TAppTabs; [exact (value_regular (tm_tabs body) (evaluates_value f (tm_tabs body) He1))|exact H].
      * exact IHHe2.
  - eapply multi_trans.
    + eapply multi_if; [exact IHHe1|eapply evaluates_lc; eauto|assumption].
    + eapply multi_step.
      * apply ST_IfTrue; [eapply evaluates_lc; eauto|assumption].
      * exact IHHe2.
  - eapply multi_trans.
    + eapply multi_if; [exact IHHe1|assumption|eapply evaluates_lc; eauto].
    + eapply multi_step.
      * apply ST_IfFalse; [assumption|eapply evaluates_lc; eauto].
      * exact IHHe2.
  - apply multi_succ. exact IHHe.
  - eapply multi_trans with (tm_natrec tm_zero b s).
    + eapply multi_rec_arg; [exact IHHe1|exact (evaluates_lc b vb He2)|exact (evaluates_lc s vs He3)].
    + eapply multi_trans with (tm_natrec tm_zero vb s).
      * eapply multi_rec_base; [apply nv_zero|exact IHHe2|exact (evaluates_lc s vs He3)].
      * eapply multi_trans with (tm_natrec tm_zero vb vs).
        -- eapply multi_rec_step; [apply nv_zero|exact (evaluates_value b vb He2)|exact IHHe3].
        -- eapply multi_step.
           ++ apply ST_RecZero; [exact (evaluates_value b vb He2)|exact (evaluates_value s vs He3)].
           ++ constructor.
  - eapply multi_trans with (tm_natrec (tm_succ k) vb vs).
    + eapply multi_trans with (tm_natrec (tm_succ k) b s).
      * eapply multi_rec_arg; [exact IHHe1|exact (evaluates_lc b vb He2)|exact (evaluates_lc s vs He3)].
      * eapply multi_trans with (tm_natrec (tm_succ k) vb s).
        -- eapply multi_rec_base; [constructor; assumption|exact IHHe2|exact (evaluates_lc s vs He3)].
        -- eapply multi_rec_step; [constructor; assumption|exact (evaluates_value b vb He2)|exact IHHe3].
    + eapply multi_step.
      * apply ST_RecSucc; [assumption|exact (evaluates_value b vb He2)|exact (evaluates_value s vs He3)].
      * exact IHHe4.
Qed.

Lemma instantiate_ty_identity : forall T,
  instantiate_ty identity_type_substitution T = T.
Proof. induction T; simpl; try rewrite ?IHT1, ?IHT2, ?IHT; reflexivity. Qed.

Lemma instantiate_identity : forall t,
  instantiate identity_type_substitution identity_term_substitution t = t.
Proof.
  induction t; simpl; try rewrite ?instantiate_ty_identity, ?IHt, ?IHt1, ?IHt2, ?IHt3;
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
  intros t Hty U v HU Hv Hvt.
  pose proof (@fundamental [] empty t
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) Hty
    (has_type_lc_at _ _ _ _ Hty)
    identity_type_substitution identity_type_substitution
    (fun (_ : atom) (_ _ : tm) => False) []
    identity_term_substitution identity_term_substitution
    identity_type_substitution_closed identity_type_substitution_closed
    identity_term_substitution_closed identity_term_substitution_closed) as Hfund.
  assert (Henv : value_env_rel empty []
    (fun (_ : atom) (_ _ : tm) => False)
    identity_term_substitution identity_term_substitution).
  { intros x T Hlook. unfold empty in Hlook. discriminate. }
  specialize (Hfund Henv).
  rewrite !instantiate_identity in Hfund.
  unfold term_rel in Hfund.
  destruct Hfund as [f1 [f2 [Ef1 [Ef2 Hrel]]]].
  simpl in Hrel.
  destruct f1 as [|x1|A1 b1|f1 a1|b1|f1 A1| | | | | |];
  destruct f2 as [|x2|A2 b2|f2 a2|b2|f2 A2| | | | | |];
    simpl in Hrel; try contradiction.
  destruct Hrel as [_ [_ Hpoly]].
  pose proof (Hpoly U U (fun a b => a = v /\ b = v)
    (wf_ty_lc_at U [] HU) (wf_ty_lc_at U [] HU)) as Hinst.
  destruct Hinst as [w1 [w2 [Ew1 [Ew2 Hwr]]]].
  simpl in Hwr.
  destruct w1 as [|x1|A1 c1|f1 a1|c1|f1 A1| | | | | |];
  destruct w2 as [|x2|A2 c2|f2 a2|c2|f2 A2| | | | | |];
    simpl in Hwr; try contradiction.
  destruct Hwr as [_ [_ Hfun]].
  assert (Hvr : value_rel [fun a b => a = v /\ b = v]
    (fun (_ : atom) (_ _ : tm) => False) (Ty_BVar 0) v v).
  { simpl. split; reflexivity. }
  destruct (Hfun v v Hv Hv Hvr) as [q1 [q2 [Eq1 [Eq2 Hqr]]]].
  simpl in Hqr.
  destruct Hqr as [-> ->].
  eapply evaluates_multi.
  eapply EvalApp with (U := A1)
    (body := c1) (v := v).
  - eapply EvalTApp with (body := b1) (result := tm_abs A1 c1).
    + exact Ef1.
    + exact (wf_ty_lc_at U [] HU).
    + exact Ew1.
  - constructor. exact Hv.
  - exact Eq1.
Qed.

End SystemFParametricityIfRecursionEasyTask.
