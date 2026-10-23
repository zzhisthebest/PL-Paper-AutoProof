(** System F parametricity benchmark, Easy variant.
    Features: if-nondeterminism-recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFParametricityIfNondeterminismRecursionEasyTask.

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

(* A unary, evaluation based logical relation.  The two environments record
   predicates for free and bound type variables. *)
Definition value_pred := tm -> Prop.
Definition rel_env := list value_pred.
Definition free_rel_env := atom -> value_pred.

Definition free_rel_update (sigma : free_rel_env) (X : atom) (P : value_pred) : free_rel_env :=
  fun Y => if Nat.eqb X Y then P else sigma Y.

Definition valid_rel_env (Delta : ty_context) (sigma : free_rel_env) : Prop :=
  forall X, In X Delta -> forall v, sigma X v -> value v.

Fixpoint rel_lookup (n : nat) (rho : rel_env) : value_pred :=
  match n, rho with
  | O, P :: _ => P
  | S n', _ :: rho' => rel_lookup n' rho'
  | _, _ => fun _ => False
  end.

Definition false_pred : value_pred := fun _ => False.

Lemma rel_lookup_nil : forall i, rel_lookup i [] = false_pred.
Proof. destruct i; reflexivity. Qed.

Fixpoint insert_rel (k : nat) (P : value_pred) (rho : rel_env) : rel_env :=
  match k, rho with
  | O, _ => P :: rho
  | S k', [] => false_pred :: insert_rel k' P []
  | S k', Q :: rho' => Q :: insert_rel k' P rho'
  end.

Lemma rel_lookup_insert_lt : forall k P rho i,
  i < k -> forall v, rel_lookup i (insert_rel k P rho) v <-> rel_lookup i rho v.
Proof.
  induction k; intros P rho i Hi v; [lia|].
  destruct rho as [|Q rho']; simpl in *.
  - destruct i; [tauto|]. simpl.
    pose proof (IHk P [] i ltac:(lia) v) as H.
    rewrite rel_lookup_nil in H. exact H.
  - destruct i; [tauto|]. simpl. apply IHk. lia.
Qed.

Lemma rel_lookup_insert_eq : forall k P rho,
  forall v, rel_lookup k (insert_rel k P rho) v <-> P v.
Proof.
  induction k; intros P rho v; [tauto|].
  destruct rho as [|Q rho']; simpl.
  - apply IHk.
  - apply IHk.
Qed.

Definition rel_agree (k : nat) (rho rho' : rel_env) : Prop :=
  forall i, i < k -> forall v,
    rel_lookup i rho v <-> rel_lookup i rho' v.

Lemma rel_agree_cons : forall k P rho rho',
  rel_agree k rho rho' -> rel_agree (S k) (P :: rho) (P :: rho').
Proof.
  intros k P rho rho' Hag i Hi v. destruct i; [tauto|].
  simpl. apply Hag; lia.
Qed.


Definition realizes (P : value_pred) (t : tm) : Prop :=
  exists v, evaluates t v /\ P v.

Fixpoint logical_relation (rho : rel_env) (sigma : free_rel_env)
    (T : ty) : value_pred :=
  match T with
  | Ty_BVar n => rel_lookup n rho
  | Ty_FVar X => sigma X
  | Ty_Arrow A B => fun f =>
      match f with
      | tm_abs _ body => value f /\ forall a,
          logical_relation rho sigma A a ->
          realizes (logical_relation rho sigma B) (open_tm body a)
      | _ => False
      end
  | Ty_All A => fun f =>
      match f with
      | tm_tabs body => value f /\ forall U P,
          locally_closed_ty U ->
          (forall v, P v -> value v) ->
          realizes (logical_relation (P :: rho) sigma A)
            (open_tm_ty body U)
      | _ => False
      end
  | Ty_Bool => fun v => v = tm_true \/ v = tm_false
  | Ty_Nat => numeric_value
  end.

Lemma realizes_mono : forall P Q t,
  (forall v, P v -> Q v) -> realizes P t -> realizes Q t.
Proof. intros P Q t Hpq [v [He HP]]. exists v; split; [exact He|auto]. Qed.

Lemma logical_relation_agree : forall T k rho rho' sigma,
  lc_ty_at k T -> rel_agree k rho rho' ->
  forall v, logical_relation rho sigma T v <-> logical_relation rho' sigma T v.
Proof.
  induction T; intros k rho rho' sigma Hlc Hag v; simpl in *.
  - inversion Hlc; subst. specialize (Hag n H1 v). tauto.
  - tauto.
  - inversion Hlc; subst. destruct v; simpl; try tauto.
    split.
    + intros [Hv Hfun]. split; [exact Hv|]. intros a Ha.
      pose proof (proj2 (IHT1 k rho rho' sigma H2 Hag a) Ha) as Ha'.
      specialize (Hfun a Ha').
      eapply realizes_mono; [|exact Hfun].
      intros w Hw. apply (proj1 (IHT2 k rho rho' sigma H3 Hag w)); exact Hw.
    + intros [Hv Hfun]. split; [exact Hv|]. intros a Ha.
      pose proof (proj1 (IHT1 k rho rho' sigma H2 Hag a) Ha) as Ha'.
      specialize (Hfun a Ha').
      eapply realizes_mono; [|exact Hfun].
      intros w Hw. apply (proj2 (IHT2 k rho rho' sigma H3 Hag w)); exact Hw.
  - inversion Hlc; subst. destruct v; simpl; try tauto.
    split.
    + intros [Hv Hall]. split; [exact Hv|]. intros U P HU HP.
      specialize (Hall U P HU HP).
      eapply realizes_mono; [|exact Hall].
      intros w Hw. apply (proj1 (IHT (S k) (P :: rho) (P :: rho') sigma H1
        (rel_agree_cons k P rho rho' Hag) w)); exact Hw.
    + intros [Hv Hall]. split; [exact Hv|]. intros U P HU HP.
      specialize (Hall U P HU HP).
      eapply realizes_mono; [|exact Hall].
      intros w Hw. apply (proj2 (IHT (S k) (P :: rho) (P :: rho') sigma H1
        (rel_agree_cons k P rho rho' Hag) w)); exact Hw.
  - tauto.
  - tauto.
Qed.

Lemma logical_relation_closed_env : forall T rho rho' sigma,
  lc_ty_at 0 T -> forall v,
  logical_relation rho sigma T v <-> logical_relation rho' sigma T v.
Proof.
  intros T rho rho' sigma Hlc v.
  eapply logical_relation_agree; [exact Hlc|].
  intros i Hi. lia.
Qed.

Lemma rel_insert_cons_agree : forall k P rho Q Q',
  (forall v, Q v <-> Q' v) ->
  rel_agree (S (S k))
    (insert_rel (S k) Q (P :: rho))
    (P :: insert_rel k Q' rho).
Proof.
  intros k P rho Q Q' HQ i Hi v. destruct i as [|i]; [tauto|].
  simpl. destruct (Nat.lt_ge_cases i k) as [Hlt|Hge].
  - pose proof (rel_lookup_insert_lt k Q rho i Hlt v) as H1.
    pose proof (rel_lookup_insert_lt k Q' rho i Hlt v) as H2.
    simpl in *. tauto.
  - assert (i = k) by lia. subst i.
    rewrite (rel_lookup_insert_eq k Q rho v).
    rewrite (rel_lookup_insert_eq k Q' rho v). exact (HQ v).
Qed.

Lemma logical_relation_open_ty_rec : forall T k U rho sigma,
  lc_ty_at (S k) T -> lc_ty_at 0 U -> forall v,
  logical_relation rho sigma (open_ty_rec k U T) v <->
  logical_relation (insert_rel k (logical_relation rho sigma U) rho) sigma T v.
Proof.
  induction T; intros k U rho sigma HT HU v; simpl in *.
  - inversion HT; subst.
    destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. rewrite rel_lookup_insert_eq. tauto.
    + apply Nat.eqb_neq in E.
      assert (n < k) by lia.
      rewrite rel_lookup_insert_lt by assumption. tauto.
  - tauto.
  - inversion HT; subst. split; intro H.
    + destruct v; simpl in H; try contradiction.
      destruct H as [Hv Hfun]. split; [exact Hv|]. intros a Ha.
      pose proof (proj2 (IHT1 k U rho sigma H2 HU a) Ha) as Ha'.
      specialize (Hfun a Ha').
      eapply realizes_mono; [|exact Hfun].
      intros w Hw. apply (proj1 (IHT2 k U rho sigma H3 HU w)); exact Hw.
    + destruct v; simpl in H; try contradiction.
      destruct H as [Hv Hfun]. split; [exact Hv|]. intros a Ha.
      pose proof (proj1 (IHT1 k U rho sigma H2 HU a) Ha) as Ha'.
      specialize (Hfun a Ha').
      eapply realizes_mono; [|exact Hfun].
      intros w Hw. apply (proj2 (IHT2 k U rho sigma H3 HU w)); exact Hw.
  - inversion HT; subst. destruct v; simpl; try tauto.
    split.
    + intros [Hv Hall]. split; [exact Hv|]. intros U0 P HU0 HP.
      specialize (Hall U0 P HU0 HP).
      eapply realizes_mono; [|exact Hall].
      intros w Hw.
      assert (Hagree := rel_insert_cons_agree k P rho
        (logical_relation (P :: rho) sigma U) (logical_relation rho sigma U)
        (fun z => logical_relation_closed_env U (P :: rho) rho sigma HU z)).
      apply (proj1 (logical_relation_agree T (S (S k))
        (insert_rel (S k) (logical_relation (P :: rho) sigma U) (P :: rho))
        (P :: insert_rel k (logical_relation rho sigma U) rho) sigma H1 Hagree w)).
      apply (proj1 (IHT (S k) U (P :: rho) sigma H1 HU w)). exact Hw.
    + intros [Hv Hall]. split; [exact Hv|]. intros U0 P HU0 HP.
      specialize (Hall U0 P HU0 HP).
      eapply realizes_mono; [|exact Hall].
      intros w Hw.
      assert (Hagree := rel_insert_cons_agree k P rho
        (logical_relation (P :: rho) sigma U) (logical_relation rho sigma U)
        (fun z => logical_relation_closed_env U (P :: rho) rho sigma HU z)).
      apply (proj2 (IHT (S k) U (P :: rho) sigma H1 HU w)).
      apply (proj2 (logical_relation_agree T (S (S k))
        (insert_rel (S k) (logical_relation (P :: rho) sigma U) (P :: rho))
        (P :: insert_rel k (logical_relation rho sigma U) rho) sigma H1 Hagree w)).
      exact Hw.
  - tauto.
  - tauto.
Qed.

Lemma logical_relation_fresh_update : forall T rho sigma X P,
  ~ In X (fv_ty T) -> forall v,
  logical_relation rho (free_rel_update sigma X P) T v <->
  logical_relation rho sigma T v.
Proof.
  induction T; intros rho sigma X P Hfresh v; simpl in *.
  - tauto.
  - destruct (Nat.eqb X a) eqn:E.
    + exfalso. apply Hfresh. simpl. left. apply Nat.eqb_eq in E. symmetry. exact E.
    + unfold free_rel_update. rewrite E. tauto.
  - repeat rewrite in_app_iff in Hfresh. destruct v; simpl; try tauto.
    split.
    + intros [Hv Hfun]. split; [exact Hv|]. intros a Ha.
      pose proof (proj2 (IHT1 rho sigma X P ltac:(tauto) a) Ha) as Ha'.
      specialize (Hfun a Ha'). eapply realizes_mono; [|exact Hfun].
      intros w Hw. apply (proj1 (IHT2 rho sigma X P ltac:(tauto) w)); exact Hw.
    + intros [Hv Hfun]. split; [exact Hv|]. intros a Ha.
      pose proof (proj1 (IHT1 rho sigma X P ltac:(tauto) a) Ha) as Ha'.
      specialize (Hfun a Ha'). eapply realizes_mono; [|exact Hfun].
      intros w Hw. apply (proj2 (IHT2 rho sigma X P ltac:(tauto) w)); exact Hw.
  - destruct v; simpl; try tauto.
    split.
    + intros [Hv Hall]. split; [exact Hv|]. intros U P0 HU HP.
      specialize (Hall U P0 HU HP). eapply realizes_mono; [|exact Hall].
      intros w Hw. apply (proj1 (IHT (P0 :: rho) sigma X P Hfresh w)); exact Hw.
    + intros [Hv Hall]. split; [exact Hv|]. intros U P0 HU HP.
      specialize (Hall U P0 HU HP). eapply realizes_mono; [|exact Hall].
      intros w Hw. apply (proj2 (IHT (P0 :: rho) sigma X P Hfresh w)); exact Hw.
  - tauto.
  - tauto.
Qed.

Lemma logical_relation_wf_value : forall Delta T,
  wf_ty Delta T -> forall rho sigma,
  valid_rel_env Delta sigma -> forall v,
  logical_relation rho sigma T v -> value v.
Proof.
  intros Delta T Hwf. induction Hwf; intros rho sigma Hvalid v Hrel; simpl in Hrel.
  - apply Hvalid with X; assumption.
  - destruct v; simpl in Hrel; try contradiction. tauto.
  - destruct v; simpl in Hrel; try contradiction. tauto.
  - destruct Hrel as [Heq|Heq]; subst; constructor.
  - constructor. exact Hrel.
Qed.

Lemma instantiate_ty_lc : forall T K theta,
  lc_ty_at K T -> type_substitution_closed theta ->
  lc_ty_at K (instantiate_ty theta T).
Proof.
  induction T; intros K theta Hlc Htheta; simpl in *.
  - inversion Hlc; subst. constructor. assumption.
  - specialize (Htheta a). eapply lc_ty_at_monotone; [exact Htheta|lia].
  - inversion Hlc; subst. constructor; eauto.
  - inversion Hlc; subst. constructor. eauto.
  - constructor.
  - constructor.
Qed.

Lemma instantiate_lc : forall t K k theta gamma,
  lc_tm_at K k t -> type_substitution_closed theta ->
  term_substitution_closed gamma ->
  lc_tm_at K k (instantiate theta gamma t).
Proof.
  induction t; intros K k theta gamma Hlc Htheta Hgamma; simpl in *;
    inversion Hlc; subst; eauto 10 using lc_tm_at, instantiate_ty_lc,
      lc_tm_at_monotone.
  all: try (pose proof (Hgamma a) as Hclosed; unfold locally_closed_tm in Hclosed;
    eapply lc_tm_at_monotone; [exact Hclosed|lia|lia]).
Qed.

Lemma instantiate_open_tm_rec : forall t k x u theta gamma,
  ~ In x (fv_tm t) ->
  locally_closed_tm u -> term_substitution_closed gamma ->
  instantiate theta (term_subst_update gamma x u)
    (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k u (instantiate theta gamma t).
Proof.
  induction t; intros k x u theta gamma Hfresh Hu Hgamma; simpl in *.
  - destruct (Nat.eqb k n); [unfold term_subst_update|].
    + change ((if Nat.eqb x x then u else gamma x) = u).
      rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - destruct (Nat.eqb x a) eqn:E.
    + exfalso. apply Hfresh. simpl. left. apply Nat.eqb_eq in E. symmetry. exact E.
    + unfold term_subst_update. rewrite E.
      symmetry. apply open_tm_rec_lc_at with (K := 0).
      * pose proof (Hgamma a) as Hcl. unfold locally_closed_tm in Hcl.
        eapply lc_tm_at_monotone; [exact Hcl|lia|lia].
  - f_equal. eapply IHt; eauto.
  - repeat rewrite in_app_iff in Hfresh.
    f_equal.
    + eapply IHt1; eauto; tauto.
    + eapply IHt2; eauto; tauto.
  - f_equal. eapply IHt; eauto.
  - f_equal. eapply IHt; eauto.
  - reflexivity.
  - reflexivity.
  - repeat rewrite in_app_iff in Hfresh.
    f_equal.
    + eapply IHt1; eauto; tauto.
    + eapply IHt2; eauto; tauto.
    + eapply IHt3; eauto; tauto.
  - reflexivity.
  - f_equal. eapply IHt; eauto.
  - repeat rewrite in_app_iff in Hfresh.
    f_equal.
    + eapply IHt1; eauto; tauto.
    + eapply IHt2; eauto; tauto.
    + eapply IHt3; eauto; tauto.
  - repeat rewrite in_app_iff in Hfresh.
    f_equal; [eapply IHt1|eapply IHt2]; eauto; tauto.
Qed.

Lemma instantiate_open_tm : forall t x u theta gamma,
  ~ In x (fv_tm t) ->
  locally_closed_tm u -> term_substitution_closed gamma ->
  instantiate theta (term_subst_update gamma x u) (open_tm t (tm_fvar x)) =
  open_tm (instantiate theta gamma t) u.
Proof. intros t x u theta gamma Hf Hu Hg. unfold open_tm.
  eapply instantiate_open_tm_rec; eauto. Qed.

Lemma instantiate_ty_open_ty_rec : forall T k X U theta,
  ~ In X (fv_ty T) ->
  type_substitution_closed theta ->
  instantiate_ty (type_subst_update theta X U)
    (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k U (instantiate_ty theta T).
Proof.
  induction T; intros k X U theta Hfresh Htheta; simpl in *.
  - destruct (Nat.eqb k n); [unfold type_subst_update;
      change ((if Nat.eqb X X then U else theta X) = U);
      rewrite Nat.eqb_refl|]; reflexivity.
  - destruct (Nat.eqb X a) eqn:E.
    + exfalso. apply Hfresh. simpl. left. apply Nat.eqb_eq in E. symmetry. exact E.
    + unfold type_subst_update. rewrite E. symmetry.
      apply open_ty_rec_lc_at.
      eapply lc_ty_at_monotone; [apply Htheta|lia].
  - repeat rewrite in_app_iff in Hfresh. simpl.
    f_equal; [eapply IHT1|eapply IHT2]; eauto; tauto.
  - simpl. f_equal. eapply IHT; eauto.
  - reflexivity.
  - reflexivity.
Qed.

Lemma instantiate_open_tm_ty_rec : forall t K X U theta gamma,
  ~ In X (ftv_tm t) ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  instantiate (type_subst_update theta X U) gamma
    (open_tm_ty_rec K (Ty_FVar X) t) =
  open_tm_ty_rec K U (instantiate theta gamma t).
Proof.
  induction t; intros K X U theta gamma Hfresh Htheta Hgamma; simpl in *.
  - reflexivity.
  - symmetry. apply open_tm_ty_rec_lc_at with (k := 0).
    pose proof (Hgamma a) as Hcl. unfold locally_closed_tm in Hcl.
    eapply lc_tm_at_monotone; [exact Hcl|lia|lia].
  - repeat rewrite in_app_iff in Hfresh. simpl. f_equal.
    + eapply instantiate_ty_open_ty_rec; [tauto|exact Htheta].
    + eapply IHt; [tauto|exact Htheta|exact Hgamma].
  - repeat rewrite in_app_iff in Hfresh. simpl. f_equal.
    + eapply IHt1; [tauto|exact Htheta|exact Hgamma].
    + eapply IHt2; [tauto|exact Htheta|exact Hgamma].
  - simpl. f_equal. eapply IHt; [exact Hfresh|exact Htheta|exact Hgamma].
  - repeat rewrite in_app_iff in Hfresh. simpl. f_equal.
    + eapply IHt; [tauto|exact Htheta|exact Hgamma].
    + eapply instantiate_ty_open_ty_rec; [tauto|exact Htheta].
  - reflexivity.
  - reflexivity.
  - repeat rewrite in_app_iff in Hfresh. simpl. f_equal.
    + eapply IHt1; [tauto|exact Htheta|exact Hgamma].
    + eapply IHt2; [tauto|exact Htheta|exact Hgamma].
    + eapply IHt3; [tauto|exact Htheta|exact Hgamma].
  - reflexivity.
  - simpl. f_equal. eapply IHt; [exact Hfresh|exact Htheta|exact Hgamma].
  - repeat rewrite in_app_iff in Hfresh. simpl. f_equal;
      [eapply IHt1|eapply IHt2|eapply IHt3]; try tauto; assumption.
  - repeat rewrite in_app_iff in Hfresh. simpl. f_equal;
      [eapply IHt1|eapply IHt2]; try tauto; assumption.
Qed.

Lemma instantiate_open_tm_ty : forall t X U theta gamma,
  ~ In X (ftv_tm t) ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  instantiate (type_subst_update theta X U) gamma (open_tm_ty t (Ty_FVar X)) =
  open_tm_ty (instantiate theta gamma t) U.
Proof.
  intros t X U theta gamma Hfresh Htheta Hgamma. unfold open_tm_ty.
  eapply instantiate_open_tm_ty_rec; eauto.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> lc_ty_at 0 T.
Proof.
  intros Delta T Hwf.
  induction Hwf as
    [Delta X Hin
    |Delta T1 T2 H1 IH1 H2 IH2
    |L Delta T Hprem IHprem
    |Delta
    |Delta].
  - constructor.
  - constructor; assumption.
  - specialize (IHprem (fresh L) (fresh_notin L)).
    apply lc_ty_all. eapply lc_ty_at_open_inv. exact IHprem.
  - constructor.
  - constructor.
Qed.

Lemma has_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> lc_tm_at 0 0 t.
Proof.
  intros Delta Gamma t T Hty.
  induction Hty as
    [Delta Gamma x T Hlook Hwf
    |L Delta Gamma T1 t2 T2 Hwf Hbody IHbody
    |Delta Gamma t1 t2 T1 T2 Ht1 IHt1 Ht2 IHt2
    |L Delta Gamma t T Hbody IHbody
    |Delta Gamma t T U Ht IHt Hwf
    |Delta Gamma
    |Delta Gamma
    |Delta Gamma t1 t2 t3 T H1 IH1 H2 IH2 H3 IH3
    |Delta Gamma
    |Delta Gamma n Hn IHn
    |Delta Gamma n b s T Hn IHn Hb IHb Hs IHs
    |Delta Gamma t1 t2 T H1 IH1 H2 IH2].
  - constructor.
  - apply lc_tm_abs.
    + eapply wf_ty_lc; eassumption.
    + pose (x := fresh (L ++ fv_tm t2)).
      assert (HxL : ~ In x L).
      { subst x. intro Hin. apply fresh_notin with (L := L ++ fv_tm t2).
        apply in_or_app. left. exact Hin. }
      pose proof (IHbody x HxL) as Hopenlc.
      eapply lc_tm_at_open_tm_inv. exact Hopenlc.
  - eapply lc_tm_app; eassumption.
  - apply lc_tm_tabs.
    pose (X := fresh (L ++ ftv_tm t)).
    assert (HX : ~ In X L).
    { subst X. intro Hin. apply fresh_notin with (L := L ++ ftv_tm t).
      apply in_or_app. left. exact Hin. }
    pose proof (IHbody X HX) as Hopenlc.
    eapply lc_tm_at_open_ty_inv. exact Hopenlc.
  - eapply lc_tm_tapp; [exact IHt|eapply wf_ty_lc; eassumption].
  - constructor.
  - constructor.
  - eapply lc_tm_if; eassumption.
  - constructor.
  - eapply lc_tm_succ; eassumption.
  - eapply lc_tm_rec; eassumption.
  - eapply lc_tm_choice; eassumption.
Qed.

Definition gamma_related (Gamma : context) (rho : rel_env)
    (sigma : free_rel_env) (gamma : term_substitution) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    logical_relation rho sigma T (gamma x).

Definition context_wf (Delta : ty_context) (Gamma : context) : Prop :=
  forall x T, lookup_context x Gamma = Some T -> wf_ty Delta T.

Lemma context_wf_update : forall Delta Gamma x T,
  context_wf Delta Gamma -> wf_ty Delta T ->
  context_wf Delta (update Gamma x T).
Proof.
  intros Delta Gamma x T Hctx Hwf y S Hlook.
  unfold update in Hlook. simpl in Hlook.
  destruct (Nat.eqb y x) eqn:E.
  - inversion Hlook; subst. exact Hwf.
  - eapply Hctx. exact Hlook.
Qed.

Lemma wf_ty_mono : forall Delta Delta' T,
  (forall X, In X Delta -> In X Delta') ->
  wf_ty Delta T -> wf_ty Delta' T.
Proof.
  intros Delta Delta' T Hin Hwf. revert Delta' Hin.
  induction Hwf as
    [Delta X Hmem
    |Delta A B HA IHA HB IHB
    |L Delta A Hprem IHprem
    |Delta
    |Delta].
  - intros Delta' Hin. constructor. apply Hin. exact Hmem.
  - intros Delta' Hin. apply WF_Arrow; [apply IHA|apply IHB]; exact Hin.
  - intros Delta' Hin. eapply WF_All with (L := L). intros Z HZ.
    apply (IHprem Z HZ (Z :: Delta')).
    intros Y HY. simpl in HY. destruct HY as [->|HY].
    + simpl. auto.
    + simpl. right. apply Hin. exact HY.
  - intros Delta' Hin. constructor.
  - intros Delta' Hin. constructor.
Qed.

Lemma context_wf_ty_extend : forall Delta Gamma X,
  context_wf Delta Gamma -> context_wf (X :: Delta) Gamma.
Proof.
  intros Delta Gamma X Hctx y T Hlook.
  apply (wf_ty_mono Delta (X :: Delta) T).
  - intros Z HZ. simpl. auto.
  - eapply Hctx. exact Hlook.
Qed.

Lemma gamma_related_update : forall Gamma rho sigma gamma x T a,
  gamma_related Gamma rho sigma gamma ->
  logical_relation rho sigma T a ->
  gamma_related (update Gamma x T) rho sigma
    (term_subst_update gamma x a).
Proof.
  intros Gamma rho sigma gamma x T a Henv Ha y S Hlookup.
  unfold update in Hlookup. simpl in Hlookup.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y. inversion Hlookup; subst S.
    unfold term_subst_update. rewrite Nat.eqb_refl. exact Ha.
  - assert (Hlookold : lookup_context y Gamma = Some S).
    { exact Hlookup. }
    specialize (Henv y S Hlookold).
    unfold term_subst_update. assert (Nat.eqb x y = false).
    { apply Nat.eqb_neq. intro Heq. subst. rewrite Nat.eqb_refl in E. discriminate. }
    rewrite H. exact Henv.
Qed.

Lemma valid_rel_update : forall Delta sigma X P,
  valid_rel_env Delta sigma -> ~ In X Delta ->
  (forall v, P v -> value v) ->
  valid_rel_env (X :: Delta) (free_rel_update sigma X P).
Proof.
  intros Delta sigma X P Hvalid Hfresh HP Y HY v Hv.
  simpl in HY. destruct HY as [->|HY].
  - unfold free_rel_update in Hv.
    destruct (Nat.eqb Y Y) eqn:E; [apply HP; exact Hv|].
    apply Nat.eqb_neq in E. exfalso. apply E. reflexivity.
  - unfold free_rel_update. destruct (Nat.eqb X Y) eqn:E.
    + apply Nat.eqb_eq in E. subst. contradiction.
    + unfold free_rel_update in Hv. rewrite E in Hv. exact (Hvalid Y HY v Hv).
Qed.

Lemma lookup_context_some_ftv : forall Gamma x T X,
  lookup_context x Gamma = Some T -> In X (fv_ty T) ->
  In X (ftv_context Gamma).
Proof.
  induction Gamma as [|[y S] Gamma IH]; intros x T X Hlook Hfv; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + inversion Hlook; subst. apply in_or_app. left. exact Hfv.
    + apply in_or_app. right. eapply IH; eauto.
Qed.

Lemma has_type_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> lc_ty_at 0 T.
Proof.
  intros Delta Gamma t T Hty.
  induction Hty as
    [Delta Gamma x T Hlook Hwf
    |L Delta Gamma T1 t2 T2 Hwf Hbody IHbody
    |Delta Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
    |L Delta Gamma t T Hbody IHbody
    |Delta Gamma t T U Ht IHt HwfU
    |Delta Gamma
    |Delta Gamma
    |Delta Gamma c t u T Hc IHc Ht IHt Hu IHu
    |Delta Gamma
    |Delta Gamma n Hn IHn
    |Delta Gamma n b s T Hn IHn Hb IHb Hs IHs
    |Delta Gamma t1 t2 T H1 IH1 H2 IH2].
  - eapply wf_ty_lc. exact Hwf.
  - apply lc_ty_arrow.
    + eapply wf_ty_lc. exact Hwf.
    + pose (x := fresh L). assert (Hx : ~ In x L) by (subst x; apply fresh_notin).
      exact (IHbody x Hx).
  - inversion IH1; assumption.
  - apply lc_ty_all.
    pose (X := fresh L). assert (HX : ~ In X L) by (subst X; apply fresh_notin).
    specialize (IHbody X HX). eapply lc_ty_at_open_inv. exact IHbody.
  - inversion IHt; subst. eapply lc_ty_at_open; [eassumption|].
    eapply wf_ty_lc. exact HwfU.
  - constructor.
  - constructor.
  - exact IHt.
  - constructor.
  - constructor.
  - exact IHb.
  - exact IH1.
Qed.

Lemma fundamental_theorem : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall theta rho sigma gamma,
    type_substitution_closed theta ->
    term_substitution_closed gamma ->
    valid_rel_env Delta sigma ->
    context_wf Delta Gamma ->
    gamma_related Gamma rho sigma gamma ->
    realizes (logical_relation rho sigma T) (instantiate theta gamma t).
Proof.
  intros Delta Gamma t T Hty.
  induction Hty as
    [Delta Gamma x T Hlook Hwf
    |L Delta Gamma T1 t2 T2 Hwf Hbody IHbody
    |Delta Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
    |L Delta Gamma t T Hbody IHbody
    |Delta Gamma t T U Ht IHt HwfU
    |Delta Gamma
    |Delta Gamma
    |Delta Gamma c t u T Hc IHc Ht IHt Hu IHu
    |Delta Gamma
    |Delta Gamma n Hn IHn
    |Delta Gamma n b s T Hn IHn Hb IHb Hs IHs
    |Delta Gamma t1 t2 T H1 IH1 H2 IH2];
    intros theta rho sigma gamma Htheta Hgamma Hvalid Hctx Henv.
  - specialize (Henv x T Hlook).
    exists (gamma x). split; [apply EvalValue; eapply logical_relation_wf_value; eauto|exact Henv].
  - (* term abstraction *)
    set (x := fresh (L ++ fv_tm t2)).
    assert (HxL : ~ In x L).
    { subst x. intro Hin. apply fresh_notin with (L := L ++ fv_tm t2).
      apply in_or_app. left. exact Hin. }
    assert (HxFV : ~ In x (fv_tm t2)).
    { subst x. intro Hin. apply fresh_notin with (L := L ++ fv_tm t2).
      apply in_or_app. right. exact Hin. }
    assert (Hbodylc : lc_tm_at 0 1 t2).
    { pose proof (has_type_lc Delta (update Gamma x T1)
        (open_tm t2 (tm_fvar x)) T2 (Hbody x HxL)) as Hlc.
      eapply lc_tm_at_open_tm_inv. exact Hlc. }
    assert (Hsrclc : lc_tm_at 0 0 (tm_abs T1 t2)).
    { apply lc_tm_abs; [eapply wf_ty_lc; eassumption|exact Hbodylc]. }
    pose proof (instantiate_lc (tm_abs T1 t2) 0 0 theta gamma
      Hsrclc Htheta Hgamma) as Hinstlc.
    assert (Habsval : value (tm_abs (instantiate_ty theta T1) (instantiate theta gamma t2))).
    { apply v_abs. exact Hinstlc. }
    exists (tm_abs (instantiate_ty theta T1) (instantiate theta gamma t2)).
    split.
    + apply EvalValue. exact Habsval.
    + simpl. split; [exact Habsval|]. intros a Ha.
      pose proof (logical_relation_wf_value Delta T1 Hwf rho sigma Hvalid a Ha) as Haval.
      pose proof (term_subst_update_closed gamma x a Hgamma
        (value_regular a Haval)) as Hgamma'.
      pose proof (gamma_related_update Gamma rho sigma gamma x T1 a Henv Ha) as Henv'.
      pose proof (context_wf_update Delta Gamma x T1 Hctx Hwf) as Hctx'.
      pose proof (IHbody x HxL theta rho sigma
        (term_subst_update gamma x a) Htheta Hgamma' Hvalid Hctx' Henv') as Hreal.
      rewrite (instantiate_open_tm t2 x a theta gamma HxFV
        (value_regular a Haval) Hgamma) in Hreal.
      exact Hreal.
  - (* term application *)
    destruct (IH1 theta rho sigma gamma Htheta Hgamma Hvalid Hctx Henv)
      as [f [Hf Hfrel]].
    destruct (IH2 theta rho sigma gamma Htheta Hgamma Hvalid Hctx Henv)
      as [a [Ha Harel]].
    destruct f; simpl in Hfrel; try contradiction.
    destruct Hfrel as [Hfv Hfun].
    specialize (Hfun a Harel).
    destruct Hfun as [b [Hbody Hbrel]].
    exists b. split.
    + eapply EvalApp; eassumption.
    + exact Hbrel.
  - (* type abstraction *)
    set (X := fresh (L ++ ftv_tm t ++ ftv_context Gamma ++ fv_ty T ++ Delta)).
    assert (HX : ~ In X L).
    { subst X. intro Hin. apply fresh_notin with
        (L := L ++ ftv_tm t ++ ftv_context Gamma ++ fv_ty T ++ Delta).
      repeat apply in_or_app; left. exact Hin. }
    assert (HXtm : ~ In X (ftv_tm t)).
    { subst X. intro Hin. apply fresh_notin with
        (L := L ++ ftv_tm t ++ ftv_context Gamma ++ fv_ty T ++ Delta).
      repeat apply in_or_app; right. apply in_or_app; left. exact Hin. }
    assert (HXgamma : ~ In X (ftv_context Gamma)).
    { subst X. intro Hin. apply fresh_notin with
        (L := L ++ ftv_tm t ++ ftv_context Gamma ++ fv_ty T ++ Delta).
      repeat apply in_or_app; right. apply in_or_app; right.
      apply in_or_app; left. exact Hin. }
    assert (HXtype : ~ In X (fv_ty T)).
    { subst X. intro Hin. apply fresh_notin with
        (L := L ++ ftv_tm t ++ ftv_context Gamma ++ fv_ty T ++ Delta).
      repeat apply in_or_app; right. apply in_or_app; right.
      apply in_or_app; right. apply in_or_app; left. exact Hin. }
    assert (HXDelta : ~ In X Delta).
    { subst X. intro Hin. apply fresh_notin with
        (L := L ++ ftv_tm t ++ ftv_context Gamma ++ fv_ty T ++ Delta).
      repeat apply in_or_app; right. apply in_or_app; right.
      apply in_or_app; right. apply in_or_app; right. exact Hin. }
    pose proof (Hbody X HX) as Hopened.
    pose proof (has_type_lc (X :: Delta) Gamma (open_tm_ty t (Ty_FVar X))
      (open_ty T (Ty_FVar X)) Hopened) as Hopenlc.
    pose proof (has_type_type_lc (X :: Delta) Gamma (open_tm_ty t (Ty_FVar X))
      (open_ty T (Ty_FVar X)) Hopened) as Htypeopen.
    assert (Htlc : lc_ty_at 1 T).
    { eapply lc_ty_at_open_inv. exact Htypeopen. }
    assert (Hsrclc : lc_tm_at 0 0 (tm_tabs t)).
    { apply lc_tm_tabs. eapply lc_tm_at_open_ty_inv. exact Hopenlc. }
    pose proof (instantiate_lc (tm_tabs t) 0 0 theta gamma Hsrclc Htheta Hgamma) as Hinstlc.
    assert (Htabsval : value (tm_tabs (instantiate theta gamma t))).
    { apply v_tabs. exact Hinstlc. }
    exists (tm_tabs (instantiate theta gamma t)). split.
    + apply EvalValue. exact Htabsval.
    + simpl. split; [exact Htabsval|]. intros U0 P HU0 HP.
      assert (Hvalid' : valid_rel_env (X :: Delta) (free_rel_update sigma X P)).
      { eapply valid_rel_update; eauto. }
      assert (Hctx' : context_wf (X :: Delta) Gamma).
      { eapply context_wf_ty_extend. exact Hctx. }
      assert (Henv' : gamma_related Gamma (P :: rho)
        (free_rel_update sigma X P) gamma).
      { intros y S Hlook.
        pose proof (Henv y S Hlook) as Hrel0.
        pose proof (Hctx y S Hlook) as HwfS.
        pose proof (wf_ty_lc Delta S HwfS) as HlcS.
        assert (Hnot : ~ In X (fv_ty S)).
        { intro Hin. apply HXgamma. eapply lookup_context_some_ftv; eauto. }
        apply (proj2 (logical_relation_fresh_update S (P :: rho) sigma X P Hnot
          (gamma y))).
        apply (proj1 (logical_relation_closed_env S rho (P :: rho) sigma HlcS
          (gamma y))). exact Hrel0. }
      pose proof (IHbody X HX (type_subst_update theta X U0) (P :: rho)
        (free_rel_update sigma X P) gamma
        (type_subst_update_closed theta X U0 Htheta HU0) Hgamma Hvalid' Hctx' Henv') as Hreal.
      rewrite (instantiate_open_tm_ty t X U0 theta gamma HXtm Htheta Hgamma) in Hreal.
      eapply realizes_mono; [|exact Hreal].
      intros w Hw.
      assert (HsemX : logical_relation (P :: rho) (free_rel_update sigma X P)
        (Ty_FVar X) = P).
      { unfold logical_relation, free_rel_update. rewrite Nat.eqb_refl. reflexivity. }
      pose proof (logical_relation_open_ty_rec T 0 (Ty_FVar X) (P :: rho)
        (free_rel_update sigma X P) Htlc (lc_ty_fvar 0 X) w) as Hopenrel.
      pose proof (proj1 Hopenrel Hw) as Hbound.
      assert (Hagree : rel_agree 1
        (logical_relation (P :: rho) (free_rel_update sigma X P) (Ty_FVar X) :: P :: rho)
        (P :: rho)).
      { intros i Hi. destruct i; [rewrite HsemX; tauto|lia]. }
      pose proof (proj1 (logical_relation_agree T 1
        (logical_relation (P :: rho) (free_rel_update sigma X P) (Ty_FVar X) :: P :: rho)
        (P :: rho) (free_rel_update sigma X P) Htlc Hagree w) Hbound) as Hbound'.
      apply (proj1 (logical_relation_fresh_update T (P :: rho) sigma X P HXtype w)).
      exact Hbound'.
  - (* type application *)
    pose proof (IHt theta rho sigma gamma Htheta Hgamma Hvalid Hctx Henv) as Hfunreal.
    destruct Hfunreal as [f [HfunEval HfunRel]].
    simpl in HfunRel.
    destruct f; simpl in HfunRel; try contradiction.
    destruct HfunRel as [Htabs Hforall].
    assert (HUinst : locally_closed_ty (instantiate_ty theta U)).
    { eapply instantiate_ty_lc; eauto. eapply wf_ty_lc; eauto. }
    assert (HUrelval : forall a, logical_relation rho sigma U a -> value a).
    { intros a Ha. eapply logical_relation_wf_value; eauto. }
    specialize (Hforall (instantiate_ty theta U) (logical_relation rho sigma U)
      HUinst HUrelval).
    destruct Hforall as [w [HbodyEval HbodyRel]].
    assert (Htlc : lc_ty_at 1 T).
    { pose proof (has_type_type_lc _ _ _ _ Ht) as Hlcfull. inversion Hlcfull; assumption. }
    assert (HUlc : locally_closed_ty U) by (eapply wf_ty_lc; eauto).
    exists w. split.
    + simpl. eapply EvalTApp.
      * exact HfunEval.
      * exact HUinst.
      * exact HbodyEval.
    + simpl.
      change (logical_relation rho sigma (open_ty T U) w).
      apply (proj2 (logical_relation_open_ty_rec T 0 U rho sigma
        Htlc HUlc w)).
      change (logical_relation (logical_relation rho sigma U :: rho) sigma T w).
      exact HbodyRel.
  - exists tm_true. split; [apply EvalValue; constructor|simpl; auto].
  - exists tm_false. split; [apply EvalValue; constructor|simpl; auto].
  - (* conditional *)
    pose proof (IHc theta rho sigma gamma Htheta Hgamma Hvalid Hctx Henv) as Hcreal.
    destruct Hcreal as [cv [Hce Hcv]].
    simpl in Hcv. destruct Hcv as [Htrue|Hfalse].
    + subst cv.
      pose proof (IHt theta rho sigma gamma Htheta Hgamma Hvalid Hctx Henv) as Htreal.
      destruct Htreal as [r [Hre Hrel]].
      pose proof (has_type_lc _ _ _ _ Hu) as Hulc.
      pose proof (instantiate_lc u 0 0 theta gamma Hulc Htheta Hgamma) as Huilc.
      exists r. split.
      * simpl. eapply EvalIfTrue; eauto.
      * exact Hrel.
    + subst cv.
      pose proof (IHu theta rho sigma gamma Htheta Hgamma Hvalid Hctx Henv) as Hureal.
      destruct Hureal as [r [Hre Hrel]].
      pose proof (has_type_lc _ _ _ _ Ht) as Htlc.
      pose proof (instantiate_lc t 0 0 theta gamma Htlc Htheta Hgamma) as Htilc.
      exists r. split.
      * simpl. eapply EvalIfFalse; eauto.
      * exact Hrel.
  - exists tm_zero. split; [apply EvalValue; constructor; constructor|constructor].
  - (* successor *)
    pose proof (IHn theta rho sigma gamma Htheta Hgamma Hvalid Hctx Henv) as Hnreal.
    destruct Hnreal as [nv [Hne Hnv]].
    exists (tm_succ nv). split.
    + simpl. apply EvalSucc; assumption.
    + simpl. constructor. exact Hnv.
  - (* primitive recursion *)
    pose proof (IHn theta rho sigma gamma Htheta Hgamma Hvalid Hctx Henv) as Hnreal.
    pose proof (IHb theta rho sigma gamma Htheta Hgamma Hvalid Hctx Henv) as Hbrel.
    pose proof (IHs theta rho sigma gamma Htheta Hgamma Hvalid Hctx Henv) as Hsrel.
    destruct Hnreal as [nv [Hne Hnv]].
    destruct Hbrel as [vb [Hbe Hbv]].
    destruct Hsrel as [vs [Hse Hsv]].
    simpl in Hsv. destruct vs; simpl in Hsv; try contradiction.
    destruct Hsv as [Hvs HstepN].
    assert (Hvbval : value vb).
    { induction Hbe; eauto using value, numeric_value. }
    assert (Hrec : forall ns bs ss q, numeric_value q -> evaluates ns q ->
      evaluates bs vb -> evaluates ss (tm_abs t vs) ->
      realizes (logical_relation rho sigma T) (tm_natrec ns bs ss)).
    { intros ns bs ss q Hq. revert ns bs ss.
      induction Hq as [|k Hk IH]; intros ns bs ss Hns Hbs Hss.
      - exists vb. split.
        + simpl. eapply EvalRecZero; eauto.
        + exact Hbv.
      -
        assert (Hkval : value k).
        { apply v_nat. assumption. }
        specialize (HstepN k Hk).
        destruct HstepN as [g [Hge Hgrelation]].
        simpl in Hgrelation.
        destruct g; simpl in Hgrelation; try contradiction.
        destruct Hgrelation as [Hgv HstepT].
        specialize (IH k vb (tm_abs t vs)
          (EvalValue k Hkval) (EvalValue vb Hvbval)
          (EvalValue (tm_abs t vs) Hvs)) as Hrecsmaller.
        destruct Hrecsmaller as [rv [Hrecrec Hrval]].
        specialize (HstepT rv Hrval).
        destruct HstepT as [result [Hresult Hresultrel]].
        exists result. split.
        + eapply (EvalRecSucc ns bs ss k vb (tm_abs t vs) result).
          * exact Hns.
          * exact Hk.
          * exact Hbs.
          * exact Hss.
          * eapply EvalApp.
            -- eapply EvalApp.
               ++ apply EvalValue. exact Hvs.
               ++ apply EvalValue. exact Hkval.
               ++ exact Hge.
            -- exact Hrecrec.
            -- exact Hresult.
        + exact Hresultrel.
    }
    specialize (Hrec (instantiate theta gamma n)
      (instantiate theta gamma b) (instantiate theta gamma s) nv Hnv Hne Hbe Hse).
    destruct Hrec as [result [Hresult Hresultrel]].
    exists result. split; [simpl; exact Hresult|exact Hresultrel].
  - (* choice *)
    pose proof (IH1 theta rho sigma gamma Htheta Hgamma Hvalid Hctx Henv) as Hreal.
    destruct Hreal as [v [Hve Hvrel]].
    pose proof (has_type_lc _ _ _ _ H2) as H2lc.
    pose proof (instantiate_lc t2 0 0 theta gamma H2lc Htheta Hgamma) as H2ilc.
    exists v. split.
    + simpl. eapply EvalChoiceLeft; eauto.
    + exact Hvrel.
Qed.

Lemma evaluates_lc : forall t v, evaluates t v -> locally_closed_tm t.
Proof.
  intros t v H. induction H; unfold locally_closed_tm in *;
    eauto 12 using lc_tm_at, value_regular, numeric_value_lc,
      open_tm_preserves_lc_at.
  all: try (change (locally_closed_tm v); apply value_regular; assumption).
Qed.

Lemma evaluates_result_value : forall t v, evaluates t v -> value v.
Proof.
  intros t v H. induction H; eauto using value, numeric_value.
Qed.

Lemma evaluates_multi : forall t v, evaluates t v -> t -->* v.
Proof.
  intros t v He. induction He.
  - constructor.
  - eapply multi_trans.
    + eapply multi_app_left; [exact IHHe1|eapply evaluates_lc; eassumption].
    + eapply multi_trans.
      * eapply multi_app_right; [eapply evaluates_result_value; eassumption|exact IHHe2].
      * eapply multi_trans.
        -- eapply multi_step.
           ++ apply ST_AppAbs.
              ** eapply value_regular. eapply evaluates_result_value; eassumption.
              ** eapply evaluates_result_value; eassumption.
           ++ exact IHHe3.
        -- constructor.
  - eapply multi_trans.
    + eapply multi_tapp; [exact IHHe1|assumption].
    + eapply multi_trans.
      * eapply multi_step. apply ST_TAppTabs.
        -- eapply value_regular. eapply evaluates_result_value; eassumption.
        -- assumption.
        -- exact IHHe2.
      * constructor.
  - eapply multi_trans.
    + eapply multi_if; [exact IHHe1|eapply evaluates_lc; eassumption|assumption].
    + eapply multi_trans.
      * eapply multi_step. apply ST_IfTrue.
        -- eapply evaluates_lc; eassumption.
        -- assumption.
        -- exact IHHe2.
      * constructor.
  - eapply multi_trans.
    + eapply multi_if; [exact IHHe1|assumption|eapply evaluates_lc; eassumption].
    + eapply multi_trans.
      * eapply multi_step. apply ST_IfFalse.
        -- assumption.
        -- eapply evaluates_lc; eassumption.
        -- exact IHHe2.
      * constructor.
  - eapply multi_trans.
    + apply multi_succ. exact IHHe.
    + constructor.
  - eapply multi_trans.
    + eapply multi_rec_arg; [exact IHHe1|eapply evaluates_lc; eassumption|eapply evaluates_lc; eassumption].
    + eapply multi_trans.
      * eapply multi_rec_base; [constructor; assumption|exact IHHe2|eapply evaluates_lc; eassumption].
      * eapply multi_trans.
        -- eapply multi_rec_step; [constructor; assumption|eapply evaluates_result_value; eassumption|exact IHHe3].
        -- eapply multi_step.
           ++ apply ST_RecZero.
              ** eapply evaluates_result_value; eassumption.
              ** eapply evaluates_result_value; eassumption.
           ++ constructor.
  - eapply multi_trans.
    + eapply multi_rec_arg; [exact IHHe1|eapply evaluates_lc; eassumption|eapply evaluates_lc; eassumption].
    + eapply multi_trans.
      * eapply multi_rec_base; [constructor; assumption|exact IHHe2|eapply evaluates_lc; eassumption].
      * eapply multi_trans.
        -- eapply multi_rec_step; [constructor; assumption|eapply evaluates_result_value; eassumption|exact IHHe3].
        -- eapply multi_step.
           ++ apply ST_RecSucc.
              ** assumption.
              ** eapply evaluates_result_value; eassumption.
              ** eapply evaluates_result_value; eassumption.
           ++ exact IHHe4.
  - eapply multi_trans.
    + eapply multi_step. apply ST_ChoiceLeft; [eapply evaluates_lc; eassumption|assumption].
      exact IHHe.
    + constructor.
  - eapply multi_trans.
    + eapply multi_step. apply ST_ChoiceRight; [assumption|eapply evaluates_lc; eassumption].
      exact IHHe.
    + constructor.
Qed.

Lemma logical_identity_evaluates : forall sigma body U v,
  locally_closed_ty U -> value v ->
  logical_relation [] sigma
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) (tm_tabs body) ->
  evaluates (tm_app (tm_tapp (tm_tabs body) U) v) v.
Proof.
  intros sigma body U v HU Hv Hrel. simpl in Hrel.
  destruct Hrel as [Htabs Hall].
  specialize (Hall U (fun x => x = v) HU).
  assert (Hpred : forall x, x = v -> value x).
  { intros x Heq. subst. exact Hv. }
  specialize (Hall Hpred).
  destruct Hall as [f [Hpolybody Hfun]].
  destruct f; simpl in Hfun; try contradiction.
  destruct Hfun as [Hfv Happly].
  specialize (Happly v eq_refl).
  destruct Happly as [z [Hbody Hz]].
  subst z.
  eapply EvalApp.
  - eapply EvalTApp.
    + apply EvalValue. exact Htabs.
    + exact HU.
    + exact Hpolybody.
  - apply EvalValue. exact Hv.
  - exact Hbody.
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
  intros t Ht U v HwfU Hv Htyv.
  set (sigma := fun (_ : atom) (_ : tm) => False).
  assert (Hvalid : valid_rel_env [] sigma).
  { intros X HX. contradiction. }
  assert (Hctx : context_wf [] empty).
  { intros x T Hlook. discriminate. }
  assert (Henv : gamma_related empty [] sigma identity_term_substitution).
  { intros x T Hlook. discriminate. }
  assert (Hidty : forall A, instantiate_ty identity_type_substitution A = A).
  { induction A; simpl; try rewrite IHA1; try rewrite IHA2;
      try rewrite IHA; reflexivity. }
  assert (Hidtm : forall q,
      instantiate identity_type_substitution identity_term_substitution q = q).
  { induction q; simpl; try rewrite Hidty; try rewrite IHq;
      try rewrite IHq1; try rewrite IHq2; try rewrite IHq3; reflexivity. }
  assert (Hfund : realizes
      (logical_relation [] sigma
        (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0)))) t).
  { pose proof (fundamental_theorem [] empty t
      (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) Ht
      identity_type_substitution [] sigma identity_term_substitution
      identity_type_substitution_closed identity_term_substitution_closed
      Hvalid Hctx Henv) as H.
    rewrite <- (Hidtm t).
    exact H. }
  destruct Hfund as [z [Hteval Hzrel]].
  destruct z; simpl in Hzrel; try contradiction.
  destruct Hzrel as [Htabs Hforall].
  assert (HU : locally_closed_ty U) by (eapply wf_ty_lc; eauto).
  specialize (Hforall U (fun w => w = v) HU).
  assert (HP : forall w, w = v -> value w).
  { intros w Hw. subst. exact Hv. }
  specialize (Hforall HP).
  destruct Hforall as [f [Hpolybody Hfrel]].
  destruct f; simpl in Hfrel; try contradiction.
  destruct Hfrel as [Hfv Happly].
  specialize (Happly v eq_refl).
  destruct Happly as [r [Hbody Hr]].
  subst r.
  apply evaluates_multi.
  eapply EvalApp.
  - eapply EvalTApp.
    + exact Hteval.
    + exact HU.
    + exact Hpolybody.
  - apply EvalValue. exact Hv.
  - exact Hbody.
Qed.

End SystemFParametricityIfNondeterminismRecursionEasyTask.
