(** System F CBV strong-normalization benchmark, Easy variant.
    Features: if-recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia Program.Equality.
Import ListNotations.

Module SystemFNormalizationIfRecursionEasyTask.

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

Lemma sn_to_acc : forall t, strongly_normalizing t ->
  Acc (fun x y => y --> x) t.
Proof.
  intros t H. induction H.
  constructor. intros u Hu. eapply H0. exact Hu.
Qed.

Lemma sn_step : forall t u, strongly_normalizing t -> t --> u ->
  strongly_normalizing u.
Proof.
  intros t u Hsn Hs. inversion Hsn as [t0 Hred]; subst.
  exact (Hred u Hs).
Qed.

Lemma sn_induction : forall (P : tm -> Prop) t,
  strongly_normalizing t ->
  (forall t, (forall u, t --> u -> P u) -> P t) -> P t.
Proof.
  intros P t Hsn Hstep. inversion Hsn as [t0 Hred]; subst.
  induction (sn_to_acc _ Hsn) as [t Hacc IH].
  apply Hstep. intros u Hu.
  pose proof (Hred u Hu) as Hsu. inversion Hsu as [u0 Hred_u]; subst.
  exact (IH u Hu Hsu Hred_u).
Qed.

Lemma sn_succ : forall t, strongly_normalizing t ->
  strongly_normalizing (tm_succ t).
Proof.
  intros t Ht. eapply sn_induction with (t := t) (P := fun n => strongly_normalizing (tm_succ n)).
  - exact Ht.
  - intros n IH. constructor. intros u Hu. inversion Hu; subst.
    eapply IH; eassumption.
Qed.

Lemma sn_if : forall c a b,
  strongly_normalizing c -> strongly_normalizing a -> strongly_normalizing b ->
  strongly_normalizing (tm_if c a b).
Proof.
  intros c a b Hc Ha Hb.
  eapply sn_induction with (t := c)
    (P := fun c0 => strongly_normalizing (tm_if c0 a b)).
  - exact Hc.
  - intros c0 IH. constructor. intros u Hu. inversion Hu; subst.
    + exact Ha.
    + exact Hb.
    + eapply IH; eassumption.
Qed.

Lemma sn_app_left : forall t u,
  locally_closed_tm u -> strongly_normalizing (tm_app t u) ->
  strongly_normalizing t.
Proof.
  intros t u Hu Happ.
  assert (Q : forall a, Acc (fun x y => y --> x) a ->
      forall t0, a = tm_app t0 u -> strongly_normalizing t0).
  { intros a Ha. induction Ha as [a Hred IH]. intros t0 E. subst a.
    apply SN_intro. intros t1 Hstep.
    eapply IH with (y := tm_app t1 u).
    - apply ST_App1; assumption.
    - reflexivity. }
  eapply Q; [apply sn_to_acc; exact Happ|reflexivity].
Qed.

Lemma sn_tapp_left : forall t T,
  locally_closed_ty T -> strongly_normalizing (tm_tapp t T) ->
  strongly_normalizing t.
Proof.
  intros t T HT Happ.
  assert (Q : forall a, Acc (fun x y => y --> x) a ->
      forall t0, a = tm_tapp t0 T -> strongly_normalizing t0).
  { intros a Ha. induction Ha as [a Hred IH]. intros t0 E. subst a.
    apply SN_intro. intros t1 Hstep.
    eapply IH with (y := tm_tapp t1 T).
    - apply ST_TApp; assumption.
    - reflexivity. }
  eapply Q; [apply sn_to_acc; exact Happ|reflexivity].
Qed.

Lemma step_preserves_lc : forall t u,
  locally_closed_tm t -> t --> u -> locally_closed_tm u.
Proof.
  intros t u Hlc Hs. revert Hlc. induction Hs; intros Hlc; inversion Hlc; subst.
  all: try (unfold locally_closed_tm in *).
  all: try solve [eauto 10 using lc_tm_at, numeric_value_lc, value_regular].
  all: try match goal with
    | |- lc_tm_at 0 0 (open_tm _ _) =>
        inversion H5; subst;
        eapply open_tm_preserves_lc_at; eauto
    | |- lc_tm_at 0 0 (open_tm_ty _ _) =>
        inversion H5; subst;
        eapply open_tm_ty_preserves_lc_at; eauto
  end.
  all: try solve [apply lc_tm_app; [apply lc_tm_app; [eapply value_regular; eassumption|apply numeric_value_lc; assumption]|apply lc_tm_rec; [apply numeric_value_lc; assumption|eapply value_regular; eassumption|eapply value_regular; eassumption]]].
  all: try solve [eauto 10 using lc_tm_at, numeric_value_lc, value_regular].
Qed.

Record reducibility : Type := RedCandidate {
  red_rel : tm -> Prop;
  red_lc : forall t, red_rel t -> locally_closed_tm t;
  red_sn : forall t, red_rel t -> strongly_normalizing t;
  red_step : forall t u, red_rel t -> t --> u -> red_rel u;
  red_sat : forall t, locally_closed_tm t ->
    (forall u, t --> u -> red_rel u) ->
    (value t -> False) -> red_rel t
}.

Definition sn_candidate : reducibility.
Proof.
  refine (RedCandidate (fun t => locally_closed_tm t /\ strongly_normalizing t) _ _ _ _).
  - intros t [Hlc _]. exact Hlc.
  - intros t [_ Hsn]. exact Hsn.
  - intros t u [Hlc Hsn] Hs. split.
    + eapply step_preserves_lc; eassumption.
    + eapply sn_step; eassumption.
  - intros t Hlc Hred Hnv. split; [exact Hlc|]. constructor. intros u Hs.
    apply Hred; assumption.
Defined.

Lemma fvar_not_value : forall x, value (tm_fvar x) -> False.
Proof. intros x H; inversion H; subst; inversion H0. Qed.

Lemma fvar_lc : forall x, locally_closed_tm (tm_fvar x).
Proof. intros; apply lc_tm_fvar. Qed.

Lemma fvar_no_step : forall x u, ~ (tm_fvar x --> u).
Proof. intros x u H; inversion H. Qed.

Definition cand_arrow (A B : reducibility) : reducibility.
Proof.
  refine (RedCandidate
    (fun t => locally_closed_tm t /\
      forall u, red_rel A u -> red_rel B (tm_app t u)) _ _ _ _).
  - intros t [Hlc _]. exact Hlc.
  - intros t [Hlc Hfun].
    assert (HA : red_rel A (tm_fvar 0)).
    { apply red_sat; [apply fvar_lc|intros u Hu; exfalso; eapply fvar_no_step; eassumption|apply fvar_not_value]. }
    pose proof (red_sn B (tm_app t (tm_fvar 0)) (Hfun (tm_fvar 0) HA)) as Hs.
    eapply sn_app_left; [apply fvar_lc|exact Hs].
  - intros t t' [Hlc Hfun] Hs. split.
    + eapply step_preserves_lc; eassumption.
    + intros u Hu.
      exact (red_step B (tm_app t u) (tm_app t' u)
        (Hfun u Hu)
        (ST_App1 t t' u Hs (red_lc A u Hu))).
  - intros t Hlc Hred Hnv. split; [exact Hlc|]. intros u Hu.
    eapply (red_sat B).
    + apply lc_tm_app; [exact Hlc|exact (red_lc A u Hu)].
    + intros z Hz. inversion Hz; subst.
      * exfalso. apply Hnv. constructor. assumption.
      * match goal with
        | Hst : ?a --> ?b |- _ =>
            pose proof (Hred b Hst) as Hr; exact (proj2 Hr u Hu)
        end.
      * exfalso. apply Hnv. assumption.
    + intros Hv. inversion Hv; subst; try discriminate.
      match goal with Hn : numeric_value (tm_app _ _) |- _ => inversion Hn end.
Defined.

Lemma numeric_sn : forall n, numeric_value n -> strongly_normalizing n.
Proof.
  intros n Hn. constructor. intros u Hs. exfalso. eapply numeric_no_step; eauto.
Qed.

Definition cand_all (F : reducibility -> reducibility) : reducibility.
Proof.
  refine (RedCandidate
    (fun t => locally_closed_tm t /\
      forall (C : reducibility) (U : ty), locally_closed_ty U ->
        red_rel (F C) (tm_tapp t U)) _ _ _ _).
  - intros t [Hlc _]. exact Hlc.
  - intros t [Hlc Hpoly].
    pose proof (Hpoly sn_candidate Ty_Bool (lc_ty_bool 0)) as HR.
    pose proof (red_sn (F sn_candidate) (tm_tapp t Ty_Bool) HR) as Hst.
    eapply sn_tapp_left; [apply lc_ty_bool|exact Hst].
  - intros t t' [Hlc Hpoly] Hs. split.
    + eapply step_preserves_lc; eassumption.
    + intros C U HU. eapply red_step.
      * apply Hpoly. exact HU.
      * apply ST_TApp; assumption.
  - intros t Hlc Hred Hnv. split; [exact Hlc|]. intros C U HU.
    eapply (red_sat (F C)).
    + apply lc_tm_tapp; assumption.
    + intros z Hz. inversion Hz; subst.
      * exfalso. apply Hnv. constructor. assumption.
      * match goal with
        | Hst : t --> ?t' |- _ => exact (proj2 (Hred t' Hst) C U HU)
        end.
    + intros Hv. inversion Hv; subst; try discriminate.
      match goal with Hn : numeric_value (tm_tapp _ _) |- _ => inversion Hn end.
Defined.

Fixpoint interp_ty (rho : atom -> reducibility) (bs : list reducibility)
    (T : ty) : reducibility :=
  match T with
  | Ty_BVar i => nth i bs sn_candidate
  | Ty_FVar X => rho X
  | Ty_Arrow T1 T2 => cand_arrow (interp_ty rho bs T1) (interp_ty rho bs T2)
  | Ty_All T1 => cand_all (fun C => interp_ty rho (C :: bs) T1)
  | Ty_Bool => sn_candidate
  | Ty_Nat => sn_candidate
  end.

Definition cand_equiv (A B : reducibility) : Prop :=
  forall t, red_rel A t <-> red_rel B t.

Lemma cand_arrow_equiv : forall A A' B B',
  cand_equiv A A' -> cand_equiv B B' ->
  cand_equiv (cand_arrow A B) (cand_arrow A' B').
Proof.
  intros A A' B B' HA HB t. simpl. split.
  - intros [Hlc Hf]. split; [exact Hlc|]. intros u Hu.
    apply (proj1 (HB (tm_app t u))). apply Hf. apply (proj2 (HA u)); exact Hu.
  - intros [Hlc Hf]. split; [exact Hlc|]. intros u Hu.
    apply (proj2 (HB (tm_app t u))). apply Hf. apply (proj1 (HA u)); exact Hu.
Qed.

Lemma cand_all_equiv : forall F G,
  (forall C, cand_equiv (F C) (G C)) -> cand_equiv (cand_all F) (cand_all G).
Proof.
  intros F G H t. simpl. split.
  - intros [Hlc Hpoly]. split; [exact Hlc|]. intros C U HU.
    apply (proj1 (H C (tm_tapp t U))). apply Hpoly. exact HU.
  - intros [Hlc Hpoly]. split; [exact Hlc|]. intros C U HU.
    apply (proj2 (H C (tm_tapp t U))). apply Hpoly. exact HU.
Qed.

Lemma interp_stack_irrel : forall k T rho bs bs',
  lc_ty_at k T ->
  (forall i, i < k -> cand_equiv (nth i bs sn_candidate) (nth i bs' sn_candidate)) ->
  cand_equiv (interp_ty rho bs T) (interp_ty rho bs' T).
Proof.
  intros k T rho bs bs' Hlc Hpre. revert k bs bs' Hlc Hpre.
  induction T; intros k bs bs' Hlc Hpre; simpl in *.
  - inversion Hlc; subst. apply Hpre. assumption.
  - intros t. tauto.
  - inversion Hlc; subst. apply cand_arrow_equiv.
    + eapply IHT1; eauto.
    + eapply IHT2; eauto.
  - inversion Hlc; subst. apply cand_all_equiv. intros C.
    eapply IHT; [eassumption|]. intros [|i] Hi; simpl.
    + intros t. tauto.
    + apply Hpre. lia.
  - intros t. tauto.
  - intros t. tauto.
Qed.

Fixpoint insert_candidate (k : nat) (C : reducibility) (bs : list reducibility) : list reducibility :=
  match k with
  | 0 => C :: bs
  | S k' => match bs with
      | [] => sn_candidate :: insert_candidate k' C []
      | b :: bs' => b :: insert_candidate k' C bs'
      end
  end.

Lemma nth_insert_below : forall k C bs i,
  i < k -> nth i (insert_candidate k C bs) sn_candidate = nth i bs sn_candidate.
Proof.
  induction k; intros C bs i Hi; [lia|]. destruct bs as [|b bs].
  - destruct i; simpl; [reflexivity|]. rewrite (IHk C [] i) by lia. destruct i; reflexivity.
  - destruct i; simpl; [reflexivity|]. rewrite (IHk C bs i) by lia. reflexivity.
Qed.

Lemma nth_insert_at : forall k C bs,
  nth k (insert_candidate k C bs) sn_candidate = C.
Proof.
  induction k; intros C bs; simpl; [reflexivity|].
  destruct bs as [|b bs]; simpl; apply IHk.
Qed.

Lemma cand_equiv_trans : forall A B C,
  cand_equiv A B -> cand_equiv B C -> cand_equiv A C.
Proof. intros A B C HAB HBC t. specialize (HAB t); specialize (HBC t). tauto. Qed.

Lemma interp_open_ty : forall k T rho bs C U,
  lc_ty_at (S k) T -> locally_closed_ty U ->
  cand_equiv C (interp_ty rho bs U) ->
  cand_equiv (interp_ty rho (insert_candidate k C bs) T)
    (interp_ty rho bs (open_ty_rec k U T)).
Proof.
  intros k T rho bs C U Hlc HU HC. revert k bs C U Hlc HU HC.
  induction T; intros k bs C U Hlc HU HC; simpl in *.
  - inversion Hlc; subst. destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. rewrite nth_insert_at. exact HC.
    + apply Nat.eqb_neq in E. assert (Hlt : n < k) by lia.
      rewrite nth_insert_below by exact Hlt. intros t. tauto.
  - intros t. tauto.
  - inversion Hlc; subst. apply cand_arrow_equiv.
    + eapply IHT1; eauto.
    + eapply IHT2; eauto.
  - inversion Hlc; subst. apply cand_all_equiv. intros C'.
    eapply IHT with (k := S k) (bs := C' :: bs)
      (C := C) (U := U); [eassumption|exact HU|].
    eapply cand_equiv_trans; [exact HC|].
    apply (interp_stack_irrel 0 U rho bs (C' :: bs) HU). intros i Hi. lia.
  - intros t. tauto.
  - intros t. tauto.
Qed.

Lemma interp_rho_irrel : forall T rho rho' bs X,
  (forall Y, Y <> X -> cand_equiv (rho Y) (rho' Y)) ->
  ~ In X (fv_ty T) ->
  cand_equiv (interp_ty rho bs T) (interp_ty rho' bs T).
Proof.
  induction T; intros rho rho' bs X Hag Hfresh; simpl in *.
  - intros t. tauto.
  - assert (E : a <> X) by (intro E; subst; apply Hfresh; simpl; auto).
    apply Hag. exact E.
  - assert (H1 : ~ In X (fv_ty T1)) by (simpl in Hfresh; intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (H2 : ~ In X (fv_ty T2)) by (simpl in Hfresh; intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
    apply cand_arrow_equiv; [eapply IHT1|eapply IHT2]; eauto.
  - apply cand_all_equiv. intros C. exact (IHT rho rho' (C :: bs) X Hag Hfresh).
  - intros t. tauto.
  - intros t. tauto.
Qed.

Definition type_env_rel (Delta : ty_context) (theta : type_substitution)
    (rho : atom -> reducibility) (bs : list reducibility) : Prop :=
  forall X, In X Delta -> cand_equiv (rho X) (interp_ty rho bs (theta X)).

Definition term_env_rel (Gamma : context) (theta : type_substitution)
    (rho : atom -> reducibility) (bs : list reducibility)
    (gamma : term_substitution) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    red_rel (interp_ty rho bs (instantiate_ty theta T)) (gamma x).

Lemma term_env_rel_update : forall Gamma theta rho bs gamma x T u,
  term_env_rel Gamma theta rho bs gamma ->
  ~ In x (dom_context Gamma) ->
  red_rel (interp_ty rho bs (instantiate_ty theta T)) u ->
  term_env_rel (update Gamma x T) theta rho bs (term_subst_update gamma x u).
Proof.
  intros Gamma theta rho bs gamma x T u Henv Hfresh Hu y Ty Hlook.
  unfold update in Hlook. simpl in Hlook.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y. inversion Hlook; subst Ty.
    unfold term_subst_update. rewrite Nat.eqb_refl. exact Hu.
  - assert (E2 : Nat.eqb x y = false).
    { apply Nat.eqb_neq in E. destruct (Nat.eqb x y) eqn:E2.
      - apply Nat.eqb_eq in E2. exfalso. apply E. symmetry. exact E2.
      - reflexivity. }
    unfold term_subst_update. rewrite E2.
    eapply Henv; eassumption.
Qed.

Lemma term_env_rel_rho_irrel : forall Gamma theta rho rho' bs gamma X,
  term_env_rel Gamma theta rho bs gamma ->
  (forall x T, lookup_context x Gamma = Some T -> ~ In X (fv_ty (instantiate_ty theta T))) ->
  (forall Y, Y <> X -> cand_equiv (rho Y) (rho' Y)) ->
  term_env_rel Gamma theta rho' bs gamma.
Proof.
  intros Gamma theta rho rho' bs gamma X Henv Hfresh Hag x T Hlook.
  specialize (Henv x T Hlook).
  pose proof (interp_rho_irrel (instantiate_ty theta T) rho rho' bs X Hag (Hfresh x T Hlook)) as Heq.
  exact (proj1 (Heq (gamma x)) Henv).
Qed.

Lemma abs_app_admissible : forall A B T body u,
  locally_closed_tm (tm_abs T body) -> red_rel A u ->
  (forall v, red_rel A v -> red_rel B (open_tm body v)) ->
  red_rel B (tm_app (tm_abs T body) u).
Proof.
  intros A B T body u Habs Hu Hbody.
  refine (sn_induction
    (fun u0 => red_rel A u0 -> red_rel B (tm_app (tm_abs T body) u0))
    u (red_sn A u Hu) _ Hu).
  intros u0 IH HAu0. eapply (red_sat B).
  + apply lc_tm_app; [exact Habs|exact (red_lc A u0 HAu0)].
  + intros z Hz. inversion Hz; subst.
      * exact (Hbody u0 HAu0).
      * exfalso. eapply value_no_step; [constructor; exact Habs|eassumption].
      * match goal with Hst : u0 --> ?u' |- _ => exact (IH u' Hst (red_step A u0 u' HAu0 Hst)) end.
  + intros Hv. inversion Hv; subst; try discriminate.
      match goal with Hn : numeric_value (tm_app _ _) |- _ => inversion Hn end.
Qed.

Definition sem_env_rel (Gamma : context) (rho : atom -> reducibility)
    (bs : list reducibility) (gamma : term_substitution) : Prop :=
  forall x T, lookup_context x Gamma = Some T -> red_rel (interp_ty rho bs T) (gamma x).

Lemma sem_env_rel_update : forall Gamma rho bs gamma x T u,
  sem_env_rel Gamma rho bs gamma -> ~ In x (dom_context Gamma) ->
  red_rel (interp_ty rho bs T) u ->
  sem_env_rel (update Gamma x T) rho bs (term_subst_update gamma x u).
Proof.
  intros Gamma rho bs gamma x T u Henv Hfresh Hu y Ty Hlook.
  unfold update in Hlook. simpl in Hlook. destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y. inversion Hlook; subst Ty.
    unfold term_subst_update. rewrite Nat.eqb_refl. exact Hu.
  - assert (E2 : Nat.eqb x y = false).
    { apply Nat.eqb_neq in E. destruct (Nat.eqb x y) eqn:E2.
      - apply Nat.eqb_eq in E2. exfalso. apply E. symmetry. exact E2.
      - reflexivity. }
    unfold term_subst_update. rewrite E2. eapply Henv; eassumption.
Qed.

Lemma sem_env_rel_rho_irrel : forall Gamma rho rho' bs gamma X,
  sem_env_rel Gamma rho bs gamma ->
  (forall x T, lookup_context x Gamma = Some T -> ~ In X (fv_ty T)) ->
  (forall Y, Y <> X -> cand_equiv (rho Y) (rho' Y)) ->
  sem_env_rel Gamma rho' bs gamma.
Proof.
  intros Gamma rho rho' bs gamma X Henv Hfresh Hag x T Hlook.
  specialize (Henv x T Hlook).
  pose proof (interp_rho_irrel T rho rho' bs X Hag (Hfresh x T Hlook)) as Heq.
  exact (proj1 (Heq (gamma x)) Henv).
Qed.

Lemma notin_app_l : forall (x : atom) (A B : list atom), ~ In x (A ++ B) -> ~ In x A.
Proof. intros x A B H Hin. apply H. apply in_or_app. left. exact Hin. Qed.
Lemma notin_app_r : forall (x : atom) (A B : list atom), ~ In x (A ++ B) -> ~ In x B.
Proof. intros x A B H Hin. apply H. apply in_or_app. right. exact Hin. Qed.

Lemma lookup_fv_ty_subset : forall Gamma x T,
  lookup_context x Gamma = Some T ->
  forall X, In X (fv_ty T) -> In X (ftv_context Gamma).
Proof.
  induction Gamma as [|[y U] Gamma IH]; intros x T Hlook X HX; simpl in *; [discriminate|].
  destruct (Nat.eqb x y) eqn:E.
  - inversion Hlook; subst T. apply in_or_app. left. exact HX.
  - apply in_or_app. right. eapply IH; eassumption.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H. induction H.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; assumption.
  - apply lc_ty_all. specialize (H0 (fresh L) (fresh_notin L)) as Hlc.
    unfold locally_closed_ty in Hlc.
    eapply lc_ty_at_open_inv; exact Hlc.
  - apply lc_ty_bool.
  - apply lc_ty_nat.
Qed.

Lemma has_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T Hty. induction Hty.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + eapply wf_ty_lc; eassumption.
    + pose proof (H1 (fresh L) (fresh_notin L)) as Hlc.
      unfold locally_closed_tm in Hlc.
      eapply lc_tm_at_open_tm_inv; exact Hlc.
  - apply lc_tm_app; assumption.
  - apply lc_tm_tabs.
    pose proof (H0 (fresh L) (fresh_notin L)) as Hlc.
    unfold locally_closed_tm in Hlc.
    eapply lc_tm_at_open_ty_inv; exact Hlc.
  - apply lc_tm_tapp; [assumption|eapply wf_ty_lc; eassumption].
  - apply lc_tm_true.
  - apply lc_tm_false.
  - apply lc_tm_if; assumption.
  - apply lc_tm_zero.
  - apply lc_tm_succ. assumption.
  - apply lc_tm_rec; assumption.
Qed.

Lemma has_type_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> lc_ty_at 0 T.
Proof.
  intros Delta Gamma t T Hty. induction Hty.
  - eapply wf_ty_lc; eassumption.
  - apply lc_ty_arrow; [eapply wf_ty_lc; eassumption|].
    specialize (H1 (fresh L) (fresh_notin L)). exact H1.
  - inversion IHHty1; assumption.
  - apply lc_ty_all. specialize (H0 (fresh L) (fresh_notin L)).
    eapply lc_ty_at_open_inv; exact H0.
  - inversion IHHty; subst. eapply lc_ty_at_open; [eassumption|].
    eapply wf_ty_lc; eassumption.
  - apply lc_ty_bool.
  - apply lc_ty_bool.
  - assumption.
  - apply lc_ty_nat.
  - apply lc_ty_nat.
  - assumption.
Qed.

Lemma instantiate_ty_lc_at : forall theta K T,
  type_substitution_closed theta -> lc_ty_at K T ->
  lc_ty_at K (instantiate_ty theta T).
Proof.
  intros theta K T Htheta Hlc. induction Hlc; simpl.
  - apply lc_ty_bvar. assumption.
  - eapply lc_ty_at_monotone; [apply Htheta|lia].
  - apply lc_ty_arrow; assumption.
  - apply lc_ty_all. assumption.
  - apply lc_ty_bool.
  - apply lc_ty_nat.
Qed.

Lemma instantiate_lc_at : forall theta gamma K k t,
  type_substitution_closed theta -> term_substitution_closed gamma ->
  lc_tm_at K k t -> lc_tm_at K k (instantiate theta gamma t).
Proof.
  intros theta gamma K k t Htheta Hgamma Hlc. induction Hlc; simpl.
  - apply lc_tm_bvar. assumption.
  - eapply lc_tm_at_monotone; [apply Hgamma|lia|lia].
  - apply lc_tm_abs.
    + eapply instantiate_ty_lc_at; eassumption.
    + assumption.
  - apply lc_tm_app; assumption.
  - apply lc_tm_tabs. assumption.
  - apply lc_tm_tapp; [assumption|eapply instantiate_ty_lc_at; eassumption].
  - apply lc_tm_true.
  - apply lc_tm_false.
  - apply lc_tm_if; assumption.
  - apply lc_tm_zero.
  - apply lc_tm_succ. assumption.
  - apply lc_tm_rec; assumption.
Qed.

Lemma instantiate_open_tm_rec : forall t k theta gamma x u,
  term_substitution_closed gamma ->
  ~ In x (fv_tm t) ->
  instantiate theta (term_subst_update gamma x u) (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k u (instantiate theta gamma t).
Proof.
  induction t; intros k theta gamma x u Hgamma Hfresh; simpl in *; try reflexivity.
  - destruct (Nat.eqb k n); simpl; unfold term_subst_update; rewrite ?Nat.eqb_refl; reflexivity.
  - destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply Hfresh. simpl. auto.
    + unfold term_subst_update. rewrite E.
      assert (Hg : lc_tm_at 0 k (gamma a)).
      { eapply lc_tm_at_monotone; [exact (Hgamma a)|lia|lia]. }
      rewrite (open_tm_rec_lc_at (gamma a) 0 k u Hg). reflexivity.
  - f_equal. apply IHt; [exact Hgamma|exact Hfresh].
  - assert (H1 : ~ In x (fv_tm t1)) by (simpl in Hfresh; intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (H2 : ~ In x (fv_tm t2)) by (simpl in Hfresh; intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
    rewrite (IHt1 k theta gamma x u Hgamma H1), (IHt2 k theta gamma x u Hgamma H2). reflexivity.
  - f_equal. apply IHt; assumption.
  - f_equal. apply IHt; assumption.
  - assert (HF : ~ In x (fv_tm t1 ++ fv_tm t2 ++ fv_tm t3)) by exact Hfresh.
    assert (H1 : ~ In x (fv_tm t1)) by (intro Hin; apply HF; apply in_or_app; left; exact Hin).
    assert (H2 : ~ In x (fv_tm t2)) by (intro Hin; apply HF; apply in_or_app; right; apply in_or_app; left; exact Hin).
    assert (H3 : ~ In x (fv_tm t3)) by (intro Hin; apply HF; apply in_or_app; right; apply in_or_app; right; exact Hin).
    rewrite (IHt1 k theta gamma x u Hgamma H1), (IHt2 k theta gamma x u Hgamma H2), (IHt3 k theta gamma x u Hgamma H3). reflexivity.
  - f_equal. apply IHt; assumption.
  - assert (HF : ~ In x (fv_tm t1 ++ fv_tm t2 ++ fv_tm t3)) by exact Hfresh.
    assert (H1 : ~ In x (fv_tm t1)) by (intro Hin; apply HF; apply in_or_app; left; exact Hin).
    assert (H2 : ~ In x (fv_tm t2)) by (intro Hin; apply HF; apply in_or_app; right; apply in_or_app; left; exact Hin).
    assert (H3 : ~ In x (fv_tm t3)) by (intro Hin; apply HF; apply in_or_app; right; apply in_or_app; right; exact Hin).
    rewrite (IHt1 k theta gamma x u Hgamma H1), (IHt2 k theta gamma x u Hgamma H2), (IHt3 k theta gamma x u Hgamma H3). reflexivity.
Qed.

Lemma instantiate_ty_open_rec : forall T k theta X U,
  type_substitution_closed theta ->
  ~ In X (fv_ty T) ->
  instantiate_ty (type_subst_update theta X U)
    (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k U (instantiate_ty theta T).
Proof.
  induction T; intros k theta X U Htheta Hfresh; simpl in *; try reflexivity.
  - destruct (Nat.eqb k n) eqn:E; simpl.
    + unfold type_subst_update. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply Hfresh. simpl. auto.
    + unfold type_subst_update. rewrite E.
      assert (Hlc : lc_ty_at k (theta a)).
      { eapply lc_ty_at_monotone; [apply Htheta|lia]. }
      rewrite (open_ty_rec_lc_at (theta a) k U Hlc). reflexivity.
  - assert (H1 : ~ In X (fv_ty T1)) by (simpl in Hfresh; intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (H2 : ~ In X (fv_ty T2)) by (simpl in Hfresh; intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
    rewrite (IHT1 k theta X U Htheta H1), (IHT2 k theta X U Htheta H2). reflexivity.
  - f_equal. apply IHT; assumption.
Qed.

Lemma instantiate_open_tm_ty_rec : forall t k theta gamma X U,
  type_substitution_closed theta -> term_substitution_closed gamma ->
  ~ In X (ftv_tm t) ->
  instantiate (type_subst_update theta X U) gamma
    (open_tm_ty_rec k (Ty_FVar X) t) =
  open_tm_ty_rec k U (instantiate theta gamma t).
Proof.
  induction t; intros k theta gamma X U Htheta Hgamma Hfresh; simpl in *; try reflexivity.
  - unfold term_substitution_closed in Hgamma.
    assert (Hlc : lc_tm_at k 0 (gamma a)).
    { eapply lc_tm_at_monotone; [exact (Hgamma a)|lia|lia]. }
    rewrite (open_tm_ty_rec_lc_at (gamma a) k 0 U Hlc). reflexivity.
  - assert (Hty : ~ In X (fv_ty t)) by (simpl in Hfresh; intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (Htm : ~ In X (ftv_tm t0)) by (simpl in Hfresh; intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
    rewrite (instantiate_ty_open_rec t k theta X U Htheta Hty).
    f_equal. apply IHt; assumption.
  - assert (H1 : ~ In X (ftv_tm t1)) by (simpl in Hfresh; intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (H2 : ~ In X (ftv_tm t2)) by (simpl in Hfresh; intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
    rewrite (IHt1 k theta gamma X U Htheta Hgamma H1), (IHt2 k theta gamma X U Htheta Hgamma H2). reflexivity.
  - f_equal. apply IHt with (k := S k); assumption.
  - assert (H1 : ~ In X (ftv_tm t)) by (simpl in Hfresh; intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (H2 : ~ In X (fv_ty t0)) by (simpl in Hfresh; intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
    rewrite (IHt k theta gamma X U Htheta Hgamma H1).
    rewrite (instantiate_ty_open_rec t0 k theta X U Htheta H2). reflexivity.
  - assert (H1 : ~ In X (ftv_tm t1)) by (simpl in Hfresh; repeat rewrite in_app_iff in Hfresh; tauto).
    assert (H2 : ~ In X (ftv_tm t2)) by (simpl in Hfresh; repeat rewrite in_app_iff in Hfresh; tauto).
    assert (H3 : ~ In X (ftv_tm t3)) by (simpl in Hfresh; repeat rewrite in_app_iff in Hfresh; tauto).
    rewrite (IHt1 k theta gamma X U Htheta Hgamma H1), (IHt2 k theta gamma X U Htheta Hgamma H2), (IHt3 k theta gamma X U Htheta Hgamma H3). reflexivity.
  - f_equal. apply IHt; assumption.
  - assert (H1 : ~ In X (ftv_tm t1)) by (simpl in Hfresh; repeat rewrite in_app_iff in Hfresh; tauto).
    assert (H2 : ~ In X (ftv_tm t2)) by (simpl in Hfresh; repeat rewrite in_app_iff in Hfresh; tauto).
    assert (H3 : ~ In X (ftv_tm t3)) by (simpl in Hfresh; repeat rewrite in_app_iff in Hfresh; tauto).
    rewrite (IHt1 k theta gamma X U Htheta Hgamma H1), (IHt2 k theta gamma X U Htheta Hgamma H2), (IHt3 k theta gamma X U Htheta Hgamma H3). reflexivity.
Qed.




Lemma fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall theta rho bs gamma,
    type_substitution_closed theta -> term_substitution_closed gamma ->
    sem_env_rel Gamma rho bs gamma ->
    red_rel (interp_ty rho bs T) (instantiate theta gamma t).
Proof.
  intros Delta Gamma t T Hty. induction Hty; intros theta rho bs gamma Htheta Hgamma Henv.
  - unfold sem_env_rel in Henv. eapply Henv; eassumption.
  - simpl. split.
    + apply instantiate_lc_at; [exact Htheta|exact Hgamma|].
      pose proof (has_type_lc _ _ _ _ (T_Abs L Delta Gamma T1 t2 T2 H H0)) as Hlc.
      exact Hlc.
    + intros u Hu.
      set (x := fresh (L ++ dom_context Gamma ++ fv_tm t2)).
      assert (HxL : ~ In x L) by (unfold x; apply notin_app_l with (B := dom_context Gamma ++ fv_tm t2); apply fresh_notin).
      assert (HxD : ~ In x (dom_context Gamma)) by (unfold x; apply notin_app_r with (A := L); apply notin_app_l with (B := fv_tm t2); apply fresh_notin).
      assert (HxF : ~ In x (fv_tm t2)) by (unfold x; apply notin_app_r with (A := L ++ dom_context Gamma); apply fresh_notin).
      pose proof (term_env_rel_update Gamma rho bs gamma x T1 u Henv HxD Hu) as Henv'.
      specialize (H0 x HxL).
      pose proof (IHhas_type x HxL theta rho bs (term_subst_update gamma x u)
        Htheta (term_subst_update_closed gamma x u Hgamma (red_lc (interp_ty rho bs T1) u Hu)) Henv') as HB.
      rewrite instantiate_open_tm_rec with (k := 0) (theta := theta) (gamma := gamma) (x := x) (u := u) in HB; [|exact Hgamma|exact HxF].
      eapply abs_app_admissible; [|exact Hu|].
      * pose proof (has_type_lc _ _ _ _ (T_Abs L Delta Gamma T1 t2 T2 H (fun y Hy => H0))) as Hlc.
        apply instantiate_lc_at; [exact Htheta|exact Hgamma|exact Hlc].
      * exact HB.
  - simpl. destruct (IHhas_type1 theta rho bs gamma Htheta Hgamma Henv) as [_ Hfun].
    specialize (IHhas_type2 theta rho bs gamma Htheta Hgamma Henv).
    exact (Hfun (instantiate theta gamma t2) IHhas_type2).
  - simpl. split.
    + apply instantiate_lc_at; [exact Htheta|exact Hgamma|].
      pose proof (has_type_lc _ _ _ _ (T_TAbs L Delta Gamma t T H)) as Hlc. exact Hlc.
    + intros C U HU.
      set (X := fresh (L ++ Delta ++ ftv_tm t ++ fv_ty T ++ ftv_context Gamma)).
      assert (HX_L : ~ In X L) by (unfold X; apply notin_app_l with (B := Delta ++ ftv_tm t ++ fv_ty T ++ ftv_context Gamma); apply fresh_notin).
      assert (HX_D : ~ In X Delta) by (unfold X; apply notin_app_r with (A := L); apply notin_app_l with (B := ftv_tm t ++ fv_ty T ++ ftv_context Gamma); apply fresh_notin).
      assert (HX_tm : ~ In X (ftv_tm t)) by (unfold X; apply notin_app_r with (A := L ++ Delta); apply notin_app_l with (B := fv_ty T ++ ftv_context Gamma); apply fresh_notin).
      assert (HX_ty : ~ In X (fv_ty T)) by (unfold X; apply notin_app_r with (A := L ++ Delta ++ ftv_tm t); apply notin_app_l with (B := ftv_context Gamma); apply fresh_notin).
      assert (HX_ctx : forall x Ty, lookup_context x Gamma = Some Ty -> ~ In X (fv_ty Ty)).
      { intros x Ty Hlook Hin. apply (fresh_notin X (L ++ Delta ++ ftv_tm t ++ fv_ty T ++ ftv_context Gamma)).
        unfold X. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
        eapply lookup_fv_ty_subset; eassumption. }
      set (rho' := fun Y => if Nat.eqb X Y then C else rho Y).
      set (theta' := type_subst_update theta X U).
      pose proof (sem_env_rel_rho_irrel Gamma rho rho' bs gamma X Henv HX_ctx) as Henv'.
      assert (HXeq : forall Y, Y <> X -> cand_equiv (rho Y) (rho' Y)).
      { intros Y HY. unfold rho'. destruct (Nat.eqb X Y) eqn:E.
        - apply Nat.eqb_eq in E. exfalso. apply HY. symmetry. exact E.
        - intros z. tauto. }
      specialize (H X HX_L).
      pose proof (IHhas_type X HX_L theta' rho' bs gamma
        (type_subst_update_closed theta X U Htheta HU) Hgamma Henv') as HB.
      assert (HTlc : lc_ty_at 1 T).
      { pose proof (has_type_type_lc _ _ _ _ (H X HX_L)) as Hopen.
        eapply lc_ty_at_open_inv; exact Hopen. }
      assert (HE : cand_equiv (interp_ty rho' (C :: bs) T)
          (interp_ty rho bs (C :: bs) T)).
      { apply interp_rho_irrel with (X := X); [exact HXeq|].
        intro Hin. apply HX_ty. exact Hin. }
      assert (HC : cand_equiv C (interp_ty rho' bs (Ty_FVar X))).
      { intros z. simpl. unfold rho'. rewrite Nat.eqb_refl. tauto. }
      pose proof (interp_open_ty 0 T rho' bs C (Ty_FVar X) HTlc (lc_ty_fvar 0) HC) as Hopen.
      assert (Htype : cand_equiv (interp_ty rho' bs (open_ty T (Ty_FVar X))) (interp_ty rho bs (Ty_All T))).
      { simpl. eapply cand_equiv_trans; [apply Hopen|].
        intros z. simpl. apply (proj1 (HE z)). }
      pose proof (instantiate_open_tm_ty_rec t 0 theta gamma X U Htheta Hgamma HX_tm) as Hterm.
      rewrite Hterm in HB.
      eapply (red_sat (interp_ty rho bs (Ty_All T))).
      * apply lc_tm_tapp; [|exact HU].
        apply instantiate_lc_at; [exact Htheta|exact Hgamma|].
        pose proof (has_type_lc _ _ _ _ (T_TAbs L Delta Gamma t T H)) as Hlc. exact Hlc.
      * intros z Hz. inversion Hz; subst.
        -- exact (proj1 (Htype (open_tm_ty (instantiate theta gamma t) U)) HB).
        -- inversion Hnv.
      * intros Hv. inversion Hv; subst; try discriminate.
        match goal with Hn : numeric_value (tm_tapp _ _) |- _ => inversion Hn end.
  - simpl. destruct (IHhas_type theta rho bs gamma Htheta Hgamma Henv) as [_ Hpoly].
    pose proof (has_type_type_lc _ _ _ _ H) as Htylc. inversion Htylc; subst.
    set (U' := instantiate_ty theta U).
    assert (HU' : locally_closed_ty U').
    { unfold U'. apply instantiate_ty_lc_at; [exact Htheta|eapply wf_ty_lc; eassumption]. }
    pose proof (Hpoly (interp_ty rho bs U) U' HU') as Hres.
    pose proof (interp_open_ty 0 T rho bs (interp_ty rho bs U) U H1 (wf_ty_lc _ _ H0)
      (fun z => iff_refl (red_rel (interp_ty rho bs U) z))) as Hopen.
    exact (proj2 (Hopen (instantiate theta gamma t [instantiate_ty theta U])) Hres).
  - simpl. split; [apply lc_tm_true|]. constructor. intros u Hs. inversion Hs.
  - simpl. split; [apply lc_tm_false|]. constructor. intros u Hs. inversion Hs.
  - simpl. eapply if_admissible.
    + exact (IHhas_type1 theta rho bs gamma Htheta Hgamma Henv).
    + exact (IHhas_type2 theta rho bs gamma Htheta Hgamma Henv).
    + exact (IHhas_type3 theta rho bs gamma Htheta Hgamma Henv).
  - simpl. split; [apply lc_tm_zero|]. constructor. intros u Hs. inversion Hs.
  - simpl. destruct (IHhas_type theta rho bs gamma Htheta Hgamma Henv) as [Hlc Hsn].
    split; [apply lc_tm_succ; exact Hlc|apply sn_succ; exact Hsn].
  - simpl. eapply natrec_admissible.
    + exact (IHhas_type1 theta rho bs gamma Htheta Hgamma Henv).
    + exact (IHhas_type2 theta rho bs gamma Htheta Hgamma Henv).
    + exact (IHhas_type3 theta rho bs gamma Htheta Hgamma Henv).
Qed.

Lemma type_env_rel_update : forall Delta theta rho bs X U C,
  type_env_rel Delta theta rho bs ->
  ~ In X Delta -> ~ In X (fv_ty U) ->
  (forall Y, In Y Delta -> ~ In X (fv_ty (theta Y))) ->
  cand_equiv C (interp_ty rho bs U) ->
  type_env_rel (X :: Delta) (type_subst_update theta X U)
    (fun Y => if Nat.eqb X Y then C else rho Y) bs.
Proof.
  intros Delta theta rho bs X U C Henv HX HU Htheta HC Y HY.
  simpl in HY. destruct HY as [HEq|HY].
  - { subst Y. unfold type_subst_update. rewrite Nat.eqb_refl.
      eapply cand_equiv_trans; [exact HC|].
      eapply interp_rho_irrel with (X := X).
      * intros Z HZX. simpl. destruct (Nat.eqb X Z) eqn:E.
        -- apply Nat.eqb_eq in E. exfalso. apply HZX. symmetry. exact E.
        -- intros t. tauto.
      * exact HU. }
  - { assert (E : Nat.eqb X Y = false).
      { destruct (Nat.eqb X Y) eqn:E; [apply Nat.eqb_eq in E; subst; contradiction|reflexivity]. }
      unfold type_subst_update. rewrite E. simpl.
      specialize (Henv Y HY).
      eapply cand_equiv_trans; [exact Henv|].
      apply interp_rho_irrel with (X := X).
      * intros Z HZX. simpl. destruct (Nat.eqb X Z) eqn:EZ.
        -- apply Nat.eqb_eq in EZ. exfalso. apply HZX. symmetry. exact EZ.
        -- intros t. tauto.
      * apply Htheta. exact HY. }
Qed.

Lemma rec_not_value : forall n b s, value (tm_natrec n b s) -> False.
Proof. intros n b s H; inversion H; subst; try discriminate; match goal with Hn : numeric_value (tm_natrec _ _ _) |- _ => inversion Hn end. Qed.

Lemma natrec_numeric : forall R n,
  numeric_value n -> forall b s, red_rel R b ->
  red_rel (cand_arrow sn_candidate (cand_arrow R R)) s ->
  red_rel R (tm_natrec n b s).
Proof.
  intros R n Hn. induction Hn as [|n Hn IHn]; intros b s Hb Hs.
  - refine (sn_induction
      (fun b0 => forall s0, strongly_normalizing s0 -> red_rel R b0 ->
        red_rel (cand_arrow sn_candidate (cand_arrow R R)) s0 -> red_rel R (tm_natrec tm_zero b0 s0))
      b (red_sn R b Hb) _ s
      (red_sn (cand_arrow sn_candidate (cand_arrow R R)) s Hs) Hb Hs).
    intros b0 IHb s0 Hss Hb0 Hs0.
    refine (sn_induction
      (fun s1 => red_rel R b0 -> red_rel (cand_arrow sn_candidate (cand_arrow R R)) s1 ->
        red_rel R (tm_natrec tm_zero b0 s1)) s0 Hss _ Hb0 Hs0).
    intros s1 IHs Hb1 Hs1. eapply (red_sat R).
    + apply lc_tm_rec; [apply lc_tm_zero|exact (red_lc R b0 Hb1)|exact (red_lc (cand_arrow sn_candidate (cand_arrow R R)) s1 Hs1)].
    + intros z Hz. inversion Hz; subst.
      * exfalso. exact (numeric_no_step tm_zero nv_zero n' H2).
      * exact (IHb b' H4 s1 (red_sn (cand_arrow sn_candidate (cand_arrow R R)) s1 Hs1) (red_step R b0 b' Hb1 H4) Hs1).
      * exact (IHs s' H5 Hb1 (red_step (cand_arrow sn_candidate (cand_arrow R R)) s1 s' Hs1 H5)).
      * exact Hb1.
    + apply rec_not_value.
  - refine (sn_induction
      (fun b0 => forall s0, strongly_normalizing s0 -> red_rel R b0 ->
        red_rel (cand_arrow sn_candidate (cand_arrow R R)) s0 -> red_rel R (tm_natrec (tm_succ n) b0 s0))
      b (red_sn R b Hb) _ s
      (red_sn (cand_arrow sn_candidate (cand_arrow R R)) s Hs) Hb Hs).
    intros b0 IHb s0 Hss Hb0 Hs0.
    refine (sn_induction
      (fun s1 => red_rel R b0 -> red_rel (cand_arrow sn_candidate (cand_arrow R R)) s1 ->
        red_rel R (tm_natrec (tm_succ n) b0 s1)) s0 Hss _ Hb0 Hs0).
    intros s1 IHs Hb1 Hs1. eapply (red_sat R).
    + apply lc_tm_rec; [apply lc_tm_succ; apply numeric_value_lc; assumption|exact (red_lc R b0 Hb1)|exact (red_lc (cand_arrow sn_candidate (cand_arrow R R)) s1 Hs1)].
    + intros z Hz. inversion Hz; subst.
      * exfalso. exact (numeric_no_step (tm_succ n) (nv_succ n Hn) n' H2).
      * exact (IHb b' H4 s1 (red_sn (cand_arrow sn_candidate (cand_arrow R R)) s1 Hs1) (red_step R b0 b' Hb1 H4) Hs1).
      * exact (IHs s' H5 Hb1 (red_step (cand_arrow sn_candidate (cand_arrow R R)) s1 s' Hs1 H5)).
      * pose proof (IHn b0 s1 Hb1 Hs1) as Hrec.
        pose proof (proj2 Hs1 n (conj (numeric_value_lc n Hn) (numeric_sn n Hn))) as Hstep1.
        exact (proj2 Hstep1 (tm_natrec n b0 s1) Hrec).
    + apply rec_not_value.
Qed.

Lemma natrec_admissible : forall R n b s,
  red_rel sn_candidate n -> red_rel R b ->
  red_rel (cand_arrow sn_candidate (cand_arrow R R)) s ->
  red_rel R (tm_natrec n b s).
Proof.
  intros R n b s Hn Hb Hs.
  refine (sn_induction
    (fun n0 => forall b0 s0, strongly_normalizing b0 -> strongly_normalizing s0 ->
      red_rel sn_candidate n0 -> red_rel R b0 ->
      red_rel (cand_arrow sn_candidate (cand_arrow R R)) s0 ->
      red_rel R (tm_natrec n0 b0 s0))
    n (red_sn sn_candidate n Hn) _ b s (red_sn R b Hb)
    (red_sn (cand_arrow sn_candidate (cand_arrow R R)) s Hs) Hn Hb Hs).
  intros n0 IHn b0 s0 Hbn Hss Hn0 Hb0 Hs0.
  refine (sn_induction
    (fun b1 => forall s1, strongly_normalizing s1 -> red_rel sn_candidate n0 ->
      red_rel R b1 -> red_rel (cand_arrow sn_candidate (cand_arrow R R)) s1 ->
      red_rel R (tm_natrec n0 b1 s1))
    b0 (red_sn R b0 Hb0) _ s0
    (red_sn (cand_arrow sn_candidate (cand_arrow R R)) s0 Hs0) Hn0 Hb0 Hs0).
  intros b1 IHb s1 Hss1 Hn1 Hb1 Hs1.
  refine (sn_induction
    (fun s2 => red_rel sn_candidate n0 -> red_rel R b1 ->
      red_rel (cand_arrow sn_candidate (cand_arrow R R)) s2 ->
      red_rel R (tm_natrec n0 b1 s2))
    s1 (red_sn (cand_arrow sn_candidate (cand_arrow R R)) s1 Hs1) _ Hn1 Hb1 Hs1).
  intros s2 IHs Hn2 Hb2 Hs2. eapply (red_sat R).
  - apply lc_tm_rec; [exact (red_lc sn_candidate n0 Hn2)|exact (red_lc R b1 Hb2)|exact (red_lc (cand_arrow sn_candidate (cand_arrow R R)) s2 Hs2)].
  - intros z Hz. inversion Hz; subst.
    + exact (IHn n' H2 b1 s2 (red_sn R b1 Hb2) (red_sn (cand_arrow sn_candidate (cand_arrow R R)) s2 Hs2) (red_step sn_candidate n0 n' Hn2 H2) Hb2 Hs2).
    + exact (IHb b' H4 s2 (red_sn (cand_arrow sn_candidate (cand_arrow R R)) s2 Hs2) Hn2 (red_step R b1 b' Hb2 H4) Hs2).
    + exact (IHs s' H5 Hn2 Hb2 (red_step (cand_arrow sn_candidate (cand_arrow R R)) s2 s' Hs2 H5)).
    + exact Hb2.
    + pose proof (natrec_numeric R n1 H2 b1 s2 Hb2 Hs2) as Hrec.
      pose proof (proj2 Hs2 n1 (conj (numeric_value_lc n1 H2) (numeric_sn n1 H2))) as Hfn.
      exact (proj2 Hfn (tm_natrec n1 b1 s2) Hrec).
  - apply rec_not_value.
Qed.

Lemma if_not_value : forall c a b, value (tm_if c a b) -> False.
Proof. intros c a b H; inversion H; subst; try discriminate; match goal with Hn : numeric_value (tm_if _ _ _) |- _ => inversion Hn end. Qed.

Lemma if_admissible : forall R c a b,
  red_rel sn_candidate c -> red_rel R a -> red_rel R b ->
  red_rel R (tm_if c a b).
Proof.
  intros R c a b Hc Ha Hb.
  refine (sn_induction
    (fun c0 => red_rel sn_candidate c0 -> forall a0 b0, red_rel R a0 -> red_rel R b0 -> red_rel R (tm_if c0 a0 b0))
    c (red_sn sn_candidate c Hc) _ Hc a b Ha Hb).
  intros c0 IHstep Hc0 a0 b0 Ha0 Hb0. eapply (red_sat R).
  - apply lc_tm_if; [exact (red_lc sn_candidate c0 Hc0)|exact (red_lc R a0 Ha0)|exact (red_lc R b0 Hb0)].
  - intros z Hz. inversion Hz; subst.
    + exact Ha0.
    + exact Hb0.
    + exact (IHstep t1' H2 (red_step sn_candidate c0 t1' Hc0 H2) a0 b0 Ha0 Hb0).
  - apply if_not_value.
Qed.

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  (* Complete this proof. *)
Qed.

End SystemFNormalizationIfRecursionEasyTask.
