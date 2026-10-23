(** System F CBV strong-normalization benchmark, Easy variant.
    Features: if-nondeterminism-recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFNormalizationIfNondeterminismRecursionEasyTask.

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

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T Hwf. induction Hwf.
  - unfold locally_closed_ty. constructor.
  - unfold locally_closed_ty in *. constructor; assumption.
  - unfold locally_closed_ty. constructor.
    apply lc_ty_at_open_inv with (X:=fresh L).
    apply H0. apply fresh_notin.
  - unfold locally_closed_ty. constructor.
  - unfold locally_closed_ty. constructor.
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

Lemma multi_trans : forall t u v,
  t -->* u -> u -->* v -> t -->* v.
Proof.
  intros t u v Htu Huv. induction Htu.
  - exact Huv.
  - econstructor; eauto.
Qed.

Lemma step_lc : forall t u,
  locally_closed_tm t -> t --> u -> locally_closed_tm u.
Proof.
  intros t u Hlc Hs. revert Hlc. induction Hs; intros Hlc; inversion Hlc; subst;
    unfold locally_closed_tm in *;
    repeat match goal with
    | Hx : lc_tm_at _ _ (tm_abs _ _) |- _ => inversion Hx; subst; clear Hx
    | Hx : lc_tm_at _ _ (tm_tabs _) |- _ => inversion Hx; subst; clear Hx
    end;
    try (unfold locally_closed_tm; eapply open_tm_preserves_lc_at; eauto);
    try (unfold locally_closed_tm; eapply open_tm_ty_preserves_lc_at; eauto);
    eauto 10 using lc_tm_at, open_tm_preserves_lc_at,
      open_tm_ty_preserves_lc_at, value_regular, numeric_value_lc;
    try solve [apply lc_tm_app; eauto using value_regular];
    try solve [apply lc_tm_tapp; eauto];
    try solve [apply lc_tm_succ; eauto];
    try solve [apply lc_tm_rec; eauto using value_regular, numeric_value_lc];
    try solve [apply lc_tm_if; eauto].
  apply lc_tm_app.
  - apply lc_tm_app.
    + apply value_regular. exact H1.
    + apply numeric_value_lc. exact H.
  - apply lc_tm_rec.
    + apply numeric_value_lc. exact H.
    + apply value_regular. exact H0.
    + apply value_regular. exact H1.
Qed.

(** Erasing type annotations makes type substitution computationally inert. *)
Fixpoint erase_tm (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs _ t1 => tm_abs Ty_Bool (erase_tm t1)
  | tm_app t1 t2 => tm_app (erase_tm t1) (erase_tm t2)
  | tm_tabs t1 => tm_tabs (erase_tm t1)
  | tm_tapp t1 _ => tm_tapp (erase_tm t1) Ty_Bool
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (erase_tm t1) (erase_tm t2) (erase_tm t3)
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (erase_tm t1)
  | tm_natrec n b s => tm_natrec (erase_tm n) (erase_tm b) (erase_tm s)
  | tm_choice t1 t2 => tm_choice (erase_tm t1) (erase_tm t2)
  end.

Lemma erase_open_tm_rec : forall k t u,
  erase_tm (open_tm_rec k u t) = open_tm_rec k (erase_tm u) (erase_tm t).
Proof.
  intros k t. revert k. induction t; intros k u; simpl;
    try rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3; try reflexivity.
  destruct (Nat.eqb k n); reflexivity.
Qed.

Lemma erase_open_tm : forall t u,
  erase_tm (open_tm t u) = open_tm (erase_tm t) (erase_tm u).
Proof. intros; unfold open_tm; apply erase_open_tm_rec. Qed.

Lemma erase_open_tm_ty_rec : forall k t U,
  erase_tm (open_tm_ty_rec k U t) = erase_tm t.
Proof.
  intros k t. revert k. induction t; intros k U; simpl; try rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3;
    try reflexivity.
Qed.

Lemma erase_open_tm_ty : forall t U,
  erase_tm (open_tm_ty t U) = erase_tm t.
Proof. intros; apply erase_open_tm_ty_rec. Qed.

Lemma open_tm_ty_rec_erase : forall k t U,
  open_tm_ty_rec k U (erase_tm t) = erase_tm t.
Proof.
  intros k t. revert k. induction t; intros k U; simpl; try rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3;
    try reflexivity.
Qed.

Lemma open_tm_ty_erase : forall t U,
  open_tm_ty (erase_tm t) U = erase_tm t.
Proof. intros; apply open_tm_ty_rec_erase. Qed.

Lemma erase_lc_at : forall K k t,
  lc_tm_at K k t -> lc_tm_at K k (erase_tm t).
Proof.
  intros K k t. revert K k. induction t; intros K k Hlc;
    inversion Hlc; subst; simpl;
    eauto 10 using lc_tm_at.
Qed.

Lemma erase_lc : forall t,
  locally_closed_tm t -> locally_closed_tm (erase_tm t).
Proof. intros t H; eapply erase_lc_at; exact H. Qed.

Lemma erase_numeric : forall n,
  numeric_value n -> numeric_value (erase_tm n).
Proof. intros n H; induction H; simpl; constructor; assumption. Qed.

Lemma erase_value : forall v,
  value v -> value (erase_tm v).
Proof.
  intros v Hv. destruct Hv as [T t Hlc | t Hlc | | | n Hn].
  - simpl. apply v_abs. unfold locally_closed_tm in Hlc |- *.
    inversion Hlc; subst. apply lc_tm_abs.
    + constructor.
    + eapply erase_lc_at; eauto.
  - simpl. apply v_tabs. unfold locally_closed_tm in Hlc |- *.
    inversion Hlc; subst. apply lc_tm_tabs. eapply erase_lc_at; eauto.
  - simpl. constructor.
  - simpl. constructor.
  - simpl. apply v_nat. eapply erase_numeric; eauto.
Qed.

Lemma erase_step : forall t u,
  t --> u -> erase_tm t --> erase_tm u.
Proof.
  intros t u Hs. induction Hs; simpl; eauto 8 using step, erase_lc, erase_value, erase_numeric.
  - rewrite erase_open_tm. constructor.
    + unfold locally_closed_tm in *.
      inversion H; subst. apply lc_tm_abs.
      * constructor.
      * eapply erase_lc_at; eauto.
    + apply erase_value. assumption.
  - rewrite erase_open_tm_ty.
    assert (Htabs : locally_closed_tm (tm_tabs (erase_tm t))).
    { unfold locally_closed_tm in *. inversion H; subst.
      apply lc_tm_tabs. eapply erase_lc_at; eauto. }
    pose proof (ST_TAppTabs (erase_tm t) Ty_Bool Htabs (lc_ty_bool 0)) as Hred.
    rewrite open_tm_ty_erase in Hred. exact Hred.
  - apply ST_TApp; [exact IHHs|constructor].
Qed.

Lemma sn_erase_preimage : forall t,
  strongly_normalizing (erase_tm t) -> strongly_normalizing t.
Proof.
  intros t Hsn. remember (erase_tm t) as e eqn:E. revert t E.
  induction Hsn as [e Hnext IH]; intros t E. constructor.
  intros u Hs. eapply (IH (erase_tm u)).
  - rewrite E. eapply erase_step; eauto.
  - reflexivity.
Qed.

Lemma sn_app_left : forall t,
  strongly_normalizing (tm_app t (tm_fvar 0)) -> strongly_normalizing t.
Proof.
  intros t H. remember (tm_app t (tm_fvar 0)) as e eqn:E. revert t E.
  induction H as [e Hnext IH]; intros t E. constructor. intros u Hs.
  assert (Hr : tm_app t (tm_fvar 0) --> tm_app u (tm_fvar 0)).
  { apply ST_App1; [exact Hs|constructor]. }
  eapply IH.
  - rewrite E. exact Hr.
  - reflexivity.
Qed.

Lemma sn_tapp_left : forall t,
  strongly_normalizing (tm_tapp t Ty_Bool) -> strongly_normalizing t.
Proof.
  intros t H. remember (tm_tapp t Ty_Bool) as e eqn:E. revert t E.
  induction H as [e Hnext IH]; intros t E. constructor. intros u Hs.
  assert (Hr : tm_tapp t Ty_Bool --> tm_tapp u Ty_Bool).
  { apply ST_TApp; [exact Hs|constructor]. }
  eapply IH.
  - rewrite E. exact Hr.
  - reflexivity.
Qed.

(** Reducibility candidates and the interpretation of types over candidates. *)
Definition candidate := tm -> Prop.
Definition neutral (t : tm) : Prop := ~ value t.

Lemma sn_reduct : forall t u,
  strongly_normalizing t -> t --> u -> strongly_normalizing u.
Proof. intros t u Hsn Hs. inversion Hsn; subst. eauto. Qed.

Record reducible (P : candidate) : Prop := Reducible {
  p_lc : forall t, P t -> locally_closed_tm t;
  p_sn : forall t, P t -> strongly_normalizing t;
  p_cl : forall t u, P t -> t --> u -> P u;
  p_nc : forall t, neutral t -> locally_closed_tm t ->
    (forall u, t --> u -> P u) -> P t
}.

Definition admissible (rho : list candidate) (theta : atom -> candidate) : Prop :=
  Forall reducible rho /\ (forall X, reducible (theta X)).

Definition theta_update (theta : atom -> candidate) (X : atom)
    (P : candidate) : atom -> candidate :=
  fun Y => if Nat.eqb X Y then P else theta Y.

Definition sn_lc_candidate : candidate :=
  fun t => locally_closed_tm t /\ strongly_normalizing t.

Lemma reducible_sn_lc : reducible sn_lc_candidate.
Proof.
  constructor.
  - intros t [Hlc _]. exact Hlc.
  - intros t [_ Hsn]. exact Hsn.
  - intros t u [Hlc Hsn] Hs. split.
    + eapply step_lc; eauto.
    + eapply sn_reduct; eauto.
  - intros t Hne Hlc Hred. split; [exact Hlc|]. constructor.
    intros u Hs. apply Hred; assumption.
Qed.

Fixpoint interp (rho : list candidate) (theta : atom -> candidate)
    (T : ty) : candidate :=
  match T with
  | Ty_BVar i => nth i rho sn_lc_candidate
  | Ty_FVar X => theta X
  | Ty_Arrow A B =>
      fun t => locally_closed_tm t /\
        forall u, interp rho theta A u -> interp rho theta B (tm_app t u)
  | Ty_All B =>
      fun t => forall P, reducible P ->
        interp (P :: rho) theta B (tm_tapp t Ty_Bool)
  | Ty_Bool | Ty_Nat => sn_lc_candidate
  end.

Lemma nth_reducible : forall rho i,
  Forall reducible rho -> reducible (nth i rho sn_lc_candidate).
Proof.
  induction rho as [|P rho IH]; intros [|i] Hall; simpl.
  - exact reducible_sn_lc.
  - exact reducible_sn_lc.
  - inversion Hall; assumption.
  - inversion Hall; eauto.
Qed.

Lemma neutral_fvar : forall x, neutral (tm_fvar x).
Proof.
  intros x H. unfold neutral in H. inversion H; subst; try discriminate.
  match goal with Hn : numeric_value (tm_fvar _) |- _ => inversion Hn end.
Qed.
Lemma neutral_app : forall t u, neutral (tm_app t u).
Proof.
  intros t u H. unfold neutral in H. inversion H; subst; try discriminate.
  match goal with Hn : numeric_value (tm_app _ _) |- _ => inversion Hn end.
Qed.
Lemma neutral_tapp : forall t T, neutral (tm_tapp t T).
Proof.
  intros t T H. unfold neutral in H. inversion H; subst; try discriminate.
  match goal with Hn : numeric_value (tm_tapp _ _) |- _ => inversion Hn end.
Qed.

Lemma lc_app_left : forall t u,
  locally_closed_tm (tm_app t u) -> locally_closed_tm t.
Proof. intros t u H; unfold locally_closed_tm in *; inversion H; assumption. Qed.
Lemma lc_tapp_left : forall t T,
  locally_closed_tm (tm_tapp t T) -> locally_closed_tm t.
Proof. intros t T H; unfold locally_closed_tm in *; inversion H; assumption. Qed.

Lemma interp_variable : forall rho theta T x,
  reducible (interp rho theta T) -> interp rho theta T (tm_fvar x).
Proof.
  intros rho theta T x Hred.
  apply (@p_nc (interp rho theta T) Hred (tm_fvar x)).
  - apply neutral_fvar.
  - constructor.
  - intros u Hs. inversion Hs.
Qed.

Theorem interp_reducible : forall rho theta T,
  admissible rho theta -> reducible (interp rho theta T).
Proof.
  intros rho theta T. revert rho theta.
  induction T; intros rho theta Had; simpl.
  - destruct Had as [Hrho _]. apply nth_reducible. exact Hrho.
  - destruct Had as [_ Htheta]. apply Htheta.
  - destruct (IHT1 rho theta Had) as [HAlc HAsn HAcl HAnc].
    destruct (IHT2 rho theta Had) as [HBlc HBsn HBcl HBnc].
    constructor.
    + intros t Ht. destruct Ht as [Hlc _]. exact Hlc.
    + intros t Ht. destruct Ht as [Hlc Happ].
      specialize (Happ (tm_fvar 0)
        (interp_variable rho theta T1 0 (IHT1 rho theta Had))).
      eapply sn_app_left. eapply HBsn. exact Happ.
    + intros t u [Hlc Happ] Hstep. split.
      * eapply step_lc; eauto.
      * intros v Hv. eapply HBcl with (t := tm_app t v).
        -- apply Happ. exact Hv.
        -- apply ST_App1; [exact Hstep|].
           eapply HAlc; exact Hv.
    + intros t Hneutral Hlc Hsteps. split; [exact Hlc|].
      intros v Hv. apply (HBnc (tm_app t v)).
      * apply neutral_app.
      * apply lc_tm_app; [exact Hlc|]. eapply HAlc; exact Hv.
      * intros w Hstepapp. inversion Hstepapp; subst.
        -- match goal with
           | Habs : locally_closed_tm (tm_abs _ _) |- _ =>
               exfalso; apply Hneutral; apply v_abs; exact Habs
           end.
        -- specialize (Hsteps t1' H1) as [_ Happ]. exact (Happ v Hv).
        -- match goal with
           | Hval : value t |- _ => exfalso; apply Hneutral; exact Hval
           end.
  - destruct Had as [Hrho Htheta].
    constructor.
    + intros t Ht. pose proof (Ht sn_lc_candidate reducible_sn_lc) as Hb.
      assert (HadQ : admissible (sn_lc_candidate :: rho) theta).
      { split; [constructor; [exact reducible_sn_lc|exact Hrho]|exact Htheta]. }
      pose proof (IHT (sn_lc_candidate :: rho) theta HadQ) as HR.
      apply lc_tapp_left with (T := Ty_Bool).
      eapply p_lc; [exact HR|exact Hb].
    + intros t Ht. pose proof (Ht sn_lc_candidate reducible_sn_lc) as Hb.
      assert (HadQ : admissible (sn_lc_candidate :: rho) theta).
      { split; [constructor; [exact reducible_sn_lc|exact Hrho]|exact Htheta]. }
      pose proof (IHT (sn_lc_candidate :: rho) theta HadQ) as HR.
      eapply sn_tapp_left. eapply p_sn; [exact HR|exact Hb].
    + intros t u Ht Hstep. intros P HP.
      assert (HadP : admissible (P :: rho) theta).
      { split; [constructor; [exact HP|exact Hrho]|exact Htheta]. }
      pose proof (IHT (P :: rho) theta HadP) as HR.
      eapply p_cl; [exact HR|apply Ht; exact HP|].
      apply ST_TApp; [exact Hstep|constructor].
    + intros t Hneutral Hlc Hsteps P HP.
      assert (HadP : admissible (P :: rho) theta).
      { split; [constructor; [exact HP|exact Hrho]|exact Htheta]. }
      pose proof (IHT (P :: rho) theta HadP) as HR.
      apply (@p_nc (interp (P :: rho) theta T) HR (tm_tapp t Ty_Bool)).
      * apply neutral_tapp.
      * apply lc_tm_tapp; [exact Hlc|constructor].
      * intros u Hu. inversion Hu; subst.
        -- exfalso. apply Hneutral. apply v_tabs. assumption.
        -- match goal with
           | Hred : t --> ?q |- _ => exact (Hsteps q Hred P HP)
           end.
  - apply reducible_sn_lc.
  - apply reducible_sn_lc.
Qed.

Fixpoint insert_candidate (k : nat) (P : candidate)
    (rho : list candidate) : list candidate :=
  match k, rho with
  | 0, _ => P :: rho
  | S k', Q :: rho' => Q :: insert_candidate k' P rho'
  | S _, [] => []
  end.

Lemma nth_insert_lt : forall k n P rho,
  n < k -> k <= length rho ->
  nth n (insert_candidate k P rho) sn_lc_candidate =
  nth n rho sn_lc_candidate.
Proof.
  induction k; intros n P rho Hlt Hlen; [lia|].
  destruct rho as [|Q rho']; [simpl in Hlen; lia|].
  destruct n; simpl.
  - reflexivity.
  - apply IHk; simpl in *; lia.
Qed.

Lemma nth_insert_eq : forall k P rho,
  k <= length rho ->
  nth k (insert_candidate k P rho) sn_lc_candidate = P.
Proof.
  induction k; intros P rho Hlen.
  - reflexivity.
  - destruct rho as [|Q rho']; [simpl in Hlen; lia|].
    simpl. apply IHk. simpl in Hlen. lia.
Qed.

Lemma insert_candidate_cons : forall k P Q rho,
  insert_candidate (S k) P (Q :: rho) =
  Q :: insert_candidate k P rho.
Proof. reflexivity. Qed.

Lemma interp_open_candidate : forall k rho theta P X T t,
  k <= length rho ->
  lc_ty_at (S k) T -> ~ In X (fv_ty T) ->
  (interp rho (theta_update theta X P)
      (open_ty_rec k (Ty_FVar X) T) t <->
   interp (insert_candidate k P rho) theta T t).
Proof.
  intros k rho theta P X T. revert k rho theta P X.
  induction T; intros k rho theta P X t Hlen Hlc Hfresh; simpl in *.
  - inversion Hlc; subst.
    destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. simpl. unfold theta_update.
      rewrite Nat.eqb_refl. rewrite nth_insert_eq by assumption. tauto.
    + apply Nat.eqb_neq in E. assert (n < k) by lia.
      simpl. rewrite nth_insert_lt by assumption. tauto.
  - simpl in Hfresh. assert (Hneq : a <> X).
    { intro E. apply Hfresh. simpl. left. exact E. }
    simpl. unfold theta_update.
    destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E. subst. contradiction.
    + tauto.
  - inversion Hlc; subst. simpl.
    assert (Hf1 : ~ In X (fv_ty T1)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (Hf2 : ~ In X (fv_ty T2)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    split.
    + intros [Hterm Hfun]. split; [exact Hterm|].
      intros u Hu. apply (proj1 (IHT2 k rho theta P X (tm_app t u)
        Hlen H3 Hf2)).
      apply Hfun. apply (proj2 (IHT1 k rho theta P X u Hlen H2 Hf1)). exact Hu.
    + intros [Hterm Hfun]. split; [exact Hterm|].
      intros u Hu. apply (proj2 (IHT2 k rho theta P X (tm_app t u)
        Hlen H3 Hf2)).
      apply Hfun. apply (proj1 (IHT1 k rho theta P X u Hlen H2 Hf1)). exact Hu.
  - assert (Hbody : lc_ty_at (S (S k)) T).
    { inversion Hlc; assumption. }
    simpl. split; intros Hbodyrel Q HQ.
    + apply (proj1 (IHT (S k) (Q :: rho) theta P X
        (tm_tapp t Ty_Bool) ltac:(simpl; lia) Hbody Hfresh)).
      apply Hbodyrel. exact HQ.
    + apply (proj2 (IHT (S k) (Q :: rho) theta P X
        (tm_tapp t Ty_Bool) ltac:(simpl; lia) Hbody Hfresh)).
      apply Hbodyrel. exact HQ.
  - tauto.
  - tauto.
Qed.

Lemma interp_theta_irrelevant : forall rho theta P X T t,
  ~ In X (fv_ty T) ->
  (interp rho theta T t <-> interp rho (theta_update theta X P) T t).
Proof.
  intros rho theta P X T. revert rho theta P X.
  induction T; intros rho theta P X t Hfresh; simpl in *.
  - tauto.
  - assert (Hneq : a <> X).
    { intro E. apply Hfresh. simpl. left. exact E. }
    unfold theta_update. destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E. subst. contradiction.
    + tauto.
  - assert (H1 : ~ In X (fv_ty T1)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (H2 : ~ In X (fv_ty T2)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    split.
    + intros [Hlc Happ]. split; [exact Hlc|]. intros u Hu.
      apply (proj1 (IHT2 rho theta P X (tm_app t u) H2)).
      apply Happ. apply (proj2 (IHT1 rho theta P X u H1)). exact Hu.
    + intros [Hlc Happ]. split; [exact Hlc|]. intros u Hu.
      apply (proj2 (IHT2 rho theta P X (tm_app t u) H2)).
      apply Happ. apply (proj1 (IHT1 rho theta P X u H1)). exact Hu.
  - split; intros Hall Q HQ.
    + apply (proj1 (IHT (Q :: rho) theta P X (tm_tapp t Ty_Bool) Hfresh)). apply Hall. exact HQ.
    + apply (proj2 (IHT (Q :: rho) theta P X (tm_tapp t Ty_Bool) Hfresh)). apply Hall. exact HQ.
  - tauto.
  - tauto.
Qed.

Definition candidate_equiv (P Q : candidate) : Prop :=
  forall t, P t <-> Q t.

Lemma forall2_nth_equiv : forall rho rho' i,
  Forall2 candidate_equiv rho rho' ->
  candidate_equiv (nth i rho sn_lc_candidate)
    (nth i rho' sn_lc_candidate).
Proof.
  induction rho as [|P rho IH]; intros rho' i Hrel.
  - destruct i; inversion Hrel; simpl; unfold candidate_equiv; tauto.
  - inversion Hrel; subst. destruct i; simpl.
    + assumption.
    + apply IH. assumption.
Qed.

Lemma interp_env_equiv : forall rho rho' theta theta' T t,
  Forall2 candidate_equiv rho rho' ->
  (forall X, candidate_equiv (theta X) (theta' X)) ->
  (interp rho theta T t <-> interp rho' theta' T t).
Proof.
  intros rho rho' theta theta' T. revert rho rho' theta theta'.
  induction T; intros rho rho' theta theta' t Hr Ht; simpl.
  - apply forall2_nth_equiv. exact Hr.
  - apply Ht.
  - split.
    + intros [Hlc Happ]. split; [exact Hlc|]. intros u Hu.
      apply (proj1 (IHT2 rho rho' theta theta' (tm_app t u) Hr Ht)).
      apply Happ. apply (proj2 (IHT1 rho rho' theta theta' u Hr Ht)). exact Hu.
    + intros [Hlc Happ]. split; [exact Hlc|]. intros u Hu.
      apply (proj2 (IHT2 rho rho' theta theta' (tm_app t u) Hr Ht)).
      apply Happ. apply (proj1 (IHT1 rho rho' theta theta' u Hr Ht)). exact Hu.
  - split.
    + intros Hall P HP. assert (Hrel : Forall2 candidate_equiv (P :: rho) (P :: rho')).
      { constructor; [intro z; tauto|exact Hr]. }
      apply (proj1 (IHT (P :: rho) (P :: rho') theta theta'
        (tm_tapp t Ty_Bool) Hrel Ht)). apply Hall. exact HP.
    + intros Hall P HP. assert (Hrel : Forall2 candidate_equiv (P :: rho) (P :: rho')).
      { constructor; [intro z; tauto|exact Hr]. }
      apply (proj2 (IHT (P :: rho) (P :: rho') theta theta'
        (tm_tapp t Ty_Bool) Hrel Ht)). apply Hall. exact HP.
  - tauto.
  - tauto.
Qed.

Lemma interp_insert_weaken : forall k rho theta Q U,
  k <= length rho -> lc_ty_at k U ->
  candidate_equiv (interp rho theta U)
    (interp (insert_candidate k Q rho) theta U).
Proof.
  intros k rho theta Q U Hlen Hlc. revert rho theta Q Hlen.
  induction Hlc; intros rho theta Q Hlen; unfold candidate_equiv; simpl.
  - split; intro Hval.
    + rewrite (nth_insert_lt k i Q rho H Hlen). exact Hval.
    + rewrite <- (nth_insert_lt k i Q rho H Hlen). exact Hval.
  - tauto.
  - split.
    + intros [Hterm Happ]. split; [exact Hterm|]. intros u Hu.
      apply (proj1 (IHHlc2 rho theta Q Hlen (tm_app t u))).
      apply Happ. apply (proj2 (IHHlc1 rho theta Q Hlen u)). exact Hu.
    + intros [Hterm Happ]. split; [exact Hterm|]. intros u Hu.
      apply (proj2 (IHHlc2 rho theta Q Hlen (tm_app t u))).
      apply Happ. apply (proj1 (IHHlc1 rho theta Q Hlen u)). exact Hu.
  - split; intros Hall P HP.
    + assert (Heq := IHHlc (P :: rho) theta Q ltac:(simpl; lia)
        (tm_tapp t Ty_Bool)).
      rewrite insert_candidate_cons in Heq. apply (proj1 Heq). apply Hall; exact HP.
    + assert (Heq := IHHlc (P :: rho) theta Q ltac:(simpl; lia)
        (tm_tapp t Ty_Bool)).
      rewrite insert_candidate_cons in Heq. apply (proj2 Heq). apply Hall; exact HP.
  - tauto.
  - tauto.
Qed.

Lemma interp_closed_weaken : forall rho theta Q U,
  locally_closed_ty U ->
  candidate_equiv (interp rho theta U) (interp (Q :: rho) theta U).
Proof.
  intros rho theta Q U Hlc z.
  pose proof (interp_insert_weaken 0 rho theta Q U ltac:(lia) Hlc) as Heq.
  simpl in Heq. exact (Heq z).
Qed.

Lemma insert_candidate_equiv : forall k P Q rho,
  k <= length rho -> candidate_equiv P Q ->
  Forall2 candidate_equiv (insert_candidate k P rho) (insert_candidate k Q rho).
Proof.
  induction k; intros P Q rho Hlen HPQ; simpl.
  - constructor; [exact HPQ|]. clear P Q HPQ. induction rho as [|R rs IH].
    + constructor.
    + simpl. constructor; [intro z; tauto| apply IH; lia].
  - destruct rho as [|R rs]; simpl in Hlen; [lia|]. simpl.
    constructor; [intro z; tauto|]. apply IHk; [simpl in Hlen; lia|exact HPQ].
Qed.

Lemma interp_open_semantic : forall k rho theta U T,
  k <= length rho -> locally_closed_ty U -> lc_ty_at (S k) T ->
  candidate_equiv
    (interp (insert_candidate k (interp rho theta U) rho) theta T)
    (interp rho theta (open_ty_rec k U T)).
Proof.
  intros k rho theta U T Hlen HU Hlc.
  revert k rho theta U Hlen HU Hlc.
  induction T; intros k rho theta U Hlen HU Hlc; simpl in *.
  - unfold candidate_equiv. intro z. inversion Hlc; subst.
    destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. simpl. rewrite nth_insert_eq by assumption. tauto.
    + apply Nat.eqb_neq in E. assert (n < k) by lia.
      rewrite nth_insert_lt by assumption. tauto.
  - unfold candidate_equiv; tauto.
  - inversion Hlc; subst. unfold candidate_equiv in *.
    split.
    + intros [Hterm Happ]. split; [exact Hterm|]. intros u Hu.
      apply (proj1 (IHT2 k rho theta U Hlen HU H3 (tm_app t u))).
      apply Happ. apply (proj2 (IHT1 k rho theta U Hlen HU H2 u)). exact Hu.
    + intros [Hterm Happ]. split; [exact Hterm|]. intros u Hu.
      apply (proj2 (IHT2 k rho theta U Hlen HU H3 (tm_app t u))).
      apply Happ. apply (proj1 (IHT1 k rho theta U Hlen HU H2 u)). exact Hu.
  - inversion Hlc; subst. unfold candidate_equiv in *.
    split; intros Hall P HP.
    + assert (HeqU : candidate_equiv (interp rho theta U) (interp (P :: rho) theta U)).
      { apply interp_closed_weaken. exact HU. }
      assert (Hlists : Forall2 candidate_equiv
          (P :: insert_candidate k (interp rho theta U) rho)
          (P :: insert_candidate k (interp (P :: rho) theta U) rho)).
      { constructor; [intro z; tauto|].
        apply insert_candidate_equiv; [simpl; lia|intro z; apply HeqU]. }
      match goal with
      | Hbody : lc_ty_at _ T |- _ =>
          pose proof (IHT (S k) (P :: rho) theta U ltac:(simpl; lia) HU Hbody
            (tm_tapp t Ty_Bool)) as IH
      end.
      rewrite insert_candidate_cons in IH.
      apply (proj1 IH).
      assert (Henv := @interp_env_equiv
        (P :: insert_candidate k (interp rho theta U) rho)
        (P :: insert_candidate k (interp (P :: rho) theta U) rho)
        theta theta T (tm_tapp t Ty_Bool) Hlists
        (fun X => fun z => conj (fun H => H) (fun H => H))).
      apply (proj1 Henv).
      apply Hall; exact HP.
    + assert (HeqU : candidate_equiv (interp (P :: rho) theta U) (interp rho theta U)).
      { intro z. symmetry. apply (interp_closed_weaken rho theta P U HU z). }
      assert (Hlists : Forall2 candidate_equiv
          (P :: insert_candidate k (interp (P :: rho) theta U) rho)
          (P :: insert_candidate k (interp rho theta U) rho)).
      { constructor; [intro z; tauto|].
        apply insert_candidate_equiv; [simpl; lia|intro z; apply HeqU]. }
      match goal with
      | Hbody : lc_ty_at _ T |- _ =>
          pose proof (IHT (S k) (P :: rho) theta U ltac:(simpl; lia) HU Hbody
            (tm_tapp t Ty_Bool)) as IH
      end.
      rewrite insert_candidate_cons in IH.
      assert (Henv := @interp_env_equiv
        (P :: insert_candidate k (interp (P :: rho) theta U) rho)
        (P :: insert_candidate k (interp rho theta U) rho)
        theta theta T (tm_tapp t Ty_Bool) Hlists
        (fun X => fun z => conj (fun H => H) (fun H => H))).
      apply (proj1 Henv).
      apply (proj2 IH). apply Hall; exact HP.
  - unfold candidate_equiv; tauto.
  - unfold candidate_equiv; tauto.
Qed.

Fixpoint subst_erased (gamma : term_substitution) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => gamma x
  | tm_abs _ t1 => tm_abs Ty_Bool (subst_erased gamma t1)
  | tm_app t1 t2 => tm_app (subst_erased gamma t1) (subst_erased gamma t2)
  | tm_tabs t1 => tm_tabs (subst_erased gamma t1)
  | tm_tapp t1 _ => tm_tapp (subst_erased gamma t1) Ty_Bool
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (subst_erased gamma t1) (subst_erased gamma t2) (subst_erased gamma t3)
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (subst_erased gamma t1)
  | tm_natrec n b s => tm_natrec (subst_erased gamma n) (subst_erased gamma b) (subst_erased gamma s)
  | tm_choice t1 t2 => tm_choice (subst_erased gamma t1) (subst_erased gamma t2)
  end.

Lemma open_tm_ty_rec_subst_erased : forall t k U gamma,
  term_substitution_closed gamma ->
  open_tm_ty_rec k U (subst_erased gamma t) = subst_erased gamma t.
Proof.
  induction t; intros k U gamma Hgamma; simpl.
  - reflexivity.
  - assert (Hlc : lc_tm_at k 0 (gamma a)).
    { unfold locally_closed_tm in Hgamma.
      eapply lc_tm_at_monotone with (K:=0) (k:=0) (K':=k) (k':=0).
      - exact (Hgamma a).
      - lia.
      - lia. }
    exact (open_tm_ty_rec_lc_at (gamma a) k 0 U Hlc).
  - f_equal. apply IHt. exact Hgamma.
  - f_equal; [apply IHt1|apply IHt2]; exact Hgamma.
  - f_equal. apply IHt. exact Hgamma.
  - f_equal. apply IHt. exact Hgamma.
  - reflexivity.
  - reflexivity.
  - f_equal; [apply IHt1|apply IHt2|apply IHt3]; exact Hgamma.
  - reflexivity.
  - f_equal. apply IHt. exact Hgamma.
  - f_equal; [apply IHt1|apply IHt2|apply IHt3]; exact Hgamma.
  - f_equal; [apply IHt1|apply IHt2]; exact Hgamma.
Qed.

Lemma subst_erased_lc_at : forall gamma,
  term_substitution_closed gamma -> forall K k t,
  lc_tm_at K k t -> lc_tm_at K k (subst_erased gamma t).
Proof.
  intros gamma Hgamma K k t. revert K k. induction t; intros K k Hlc;
    inversion Hlc; subst; simpl; eauto 10 using lc_tm_at.
  all: try (eapply lc_tm_at_monotone; [apply Hgamma|lia|lia]).
Qed.

Lemma subst_erased_open_rec : forall t k gamma x u,
  term_substitution_closed gamma -> locally_closed_tm u ->
  ~ In x (fv_tm t) ->
  subst_erased (term_subst_update gamma x u)
      (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k u (subst_erased gamma t).
Proof.
  induction t; intros k gamma x u Hgamma Hu Hfresh; simpl in *.
  - destruct (Nat.eqb k n); simpl; unfold term_subst_update.
    + rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - assert (Ha : a <> x).
    { intro E. apply Hfresh. simpl. left. exact E. }
    unfold term_subst_update. destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply Ha. reflexivity.
    + rewrite (open_tm_rec_lc_at (gamma a) 0 k u).
      * reflexivity.
      * eapply lc_tm_at_monotone; [apply Hgamma|lia|lia].
  - f_equal. apply IHt; assumption.
  - f_equal.
    + apply IHt1; try assumption.
      simpl in Hfresh. intro Hin. apply Hfresh. apply in_or_app. left. exact Hin.
    + apply IHt2; try assumption.
      simpl in Hfresh. intro Hin. apply Hfresh. apply in_or_app. right. exact Hin.
  - f_equal. apply IHt; assumption.
  - f_equal. apply IHt; assumption.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply IHt1; try assumption.
      simpl in Hfresh. intro Hin. apply Hfresh. apply in_or_app. left. exact Hin.
    + apply IHt2; try assumption.
      simpl in Hfresh. intro Hin. apply Hfresh. apply in_or_app. right. apply in_or_app. left. exact Hin.
    + apply IHt3; try assumption.
      simpl in Hfresh. intro Hin. apply Hfresh. apply in_or_app. right. apply in_or_app. right. exact Hin.
  - reflexivity.
  - f_equal. apply IHt; assumption.
  - f_equal.
    + apply IHt1; try assumption.
      simpl in Hfresh. intro Hin. apply Hfresh. apply in_or_app. left. exact Hin.
    + apply IHt2; try assumption.
      simpl in Hfresh. intro Hin. apply Hfresh. apply in_or_app. right. apply in_or_app. left. exact Hin.
    + apply IHt3; try assumption.
      simpl in Hfresh. intro Hin. apply Hfresh. apply in_or_app. right. apply in_or_app. right. exact Hin.
  - f_equal.
    + apply IHt1; try assumption.
      simpl in Hfresh. intro Hin. apply Hfresh. apply in_or_app. left. exact Hin.
    + apply IHt2; try assumption.
      simpl in Hfresh. intro Hin. apply Hfresh. apply in_or_app. right. exact Hin.
Qed.

Lemma subst_erased_open_tm_ty_rec : forall t k U gamma,
  subst_erased gamma (open_tm_ty_rec k U t) = subst_erased gamma t.
Proof.
  induction t; intros k U gamma; simpl; try rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3; reflexivity.
Qed.

Definition env_related (rho : list candidate) (theta : atom -> candidate)
    (Gamma : context) (gamma : term_substitution) : Prop :=
  forall x A, lookup_context x Gamma = Some A ->
    interp rho theta A (gamma x).

Lemma lookup_in_dom : forall Gamma x A,
  lookup_context x Gamma = Some A -> In x (dom_context Gamma).
Proof.
  induction Gamma as [|[y B] G IH]; simpl; intros x A H; [discriminate|].
  destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. subst. simpl. auto.
  - simpl. right. eapply IH; eauto.
Qed.

Lemma lookup_fv_context : forall Gamma x A Y,
  lookup_context x Gamma = Some A -> In Y (fv_ty A) -> In Y (ftv_context Gamma).
Proof.
  induction Gamma as [|[z B] G IH]; simpl; intros x A Y Hlookup Hin; [discriminate|].
  destruct (Nat.eqb x z) eqn:E.
  - inversion Hlookup; subst. apply in_or_app. left. exact Hin.
  - apply in_or_app. right. eapply IH; eauto.
Qed.

Lemma env_related_type_update : forall rho theta P X Gamma gamma,
  ~ In X (ftv_context Gamma) ->
  env_related rho theta Gamma gamma ->
  env_related rho (theta_update theta X P) Gamma gamma.
Proof.
  intros rho theta P X Gamma gamma Hfresh Henv y A Hlookup.
  assert (HfreshA : ~ In X (fv_ty A)).
  { intro Hin. apply Hfresh. eapply lookup_fv_context; eauto. }
  pose proof (interp_theta_irrelevant rho theta P X A (gamma y) HfreshA) as Heq.
  apply (proj1 Heq). apply Henv with (x:=y); exact Hlookup.
Qed.

Lemma env_related_term_update : forall rho theta Gamma gamma x A u,
  ~ In x (dom_context Gamma) ->
  env_related rho theta Gamma gamma ->
  interp rho theta A u ->
  env_related rho theta (update Gamma x A) (term_subst_update gamma x u).
Proof.
  intros rho theta Gamma gamma x A u Hfresh Henv Hu y B Hlookup.
  unfold update in Hlookup. simpl in Hlookup.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y. inversion Hlookup; subst B.
    unfold term_subst_update. rewrite Nat.eqb_refl. exact Hu.
  - assert (Hneq : x <> y) by (intro E'; subst; rewrite Nat.eqb_refl in E; discriminate).
    assert (E' : Nat.eqb x y = false) by (apply Nat.eqb_neq; congruence).
    unfold term_subst_update. rewrite E'. eapply Henv; eauto.
Qed.


Lemma sn_multi_reduct : forall t u,
  strongly_normalizing t -> t -->* u -> strongly_normalizing u.
Proof.
  intros t u Hsn Hmulti. induction Hmulti.
  - exact Hsn.
  - apply IHHmulti. eapply sn_reduct; eauto.
Qed.

Lemma sn_succ : forall t,
  strongly_normalizing t -> strongly_normalizing (tm_succ t).
Proof.
  intros t H. induction H as [t Hnext IH]. constructor. intros u Hs.
  inversion Hs; subst. apply IH. assumption.
Qed.

Lemma sn_choice : forall t1 t2,
  locally_closed_tm t1 -> locally_closed_tm t2 ->
  strongly_normalizing t1 -> strongly_normalizing t2 ->
  strongly_normalizing (tm_choice t1 t2).
Proof.
  intros t1 t2 Hlc1 Hlc2 Hsn1 Hsn2. constructor.
  intros u Hs. inversion Hs; subst; eauto.
Qed.

Lemma sn_if : forall c t1 t2,
  locally_closed_tm t1 -> locally_closed_tm t2 ->
  strongly_normalizing c -> strongly_normalizing t1 ->
  strongly_normalizing t2 ->
  strongly_normalizing (tm_if c t1 t2).
Proof.
  intros c t1 t2 Hlc1 Hlc2 Hsnc. induction Hsnc as [c Hnext IH].
  intros Hsn1 Hsn2. constructor. intros u Hs.
  inversion Hs; subst.
  - exact Hsn1.
  - exact Hsn2.
  - apply IH; assumption.
Qed.

Lemma canonical_bool : forall v,
  value v -> has_type [] empty v Ty_Bool -> v = tm_true \/ v = tm_false.
Proof.
  intros v Hv Hty. destruct Hv as [T t Hlc | t Hlc | | | n Hnum].
  - inversion Hty.
  - inversion Hty.
  - left. reflexivity.
  - right. reflexivity.
  - inversion Hnum; subst; inversion Hty.
Qed.

Lemma canonical_nat : forall v,
  value v -> has_type [] empty v Ty_Nat -> numeric_value v.
Proof.
  intros v Hv Hty. destruct Hv as [T t Hlc | t Hlc | | | n Hnum].
  - inversion Hty.
  - inversion Hty.
  - inversion Hty.
  - inversion Hty.
  - exact Hnum.
Qed.

Lemma sn_accessible : forall t, strongly_normalizing t ->
  Acc (fun u v => v --> u) t.
Proof.
  intros t Hsn. induction Hsn as [t Hnext IH]. constructor.
  intros u Hs. apply IH; exact Hs.
Qed.

Lemma accessible_sn : forall t, Acc (fun u v => v --> u) t -> strongly_normalizing t.
Proof.
  intros t Hacc. induction Hacc as [t IH]. constructor. intros u Hs. exact (H u Hs).
Qed.

Lemma reducible_abs_intro : forall A Q body,
  reducible A -> reducible Q ->
  locally_closed_tm (tm_abs Ty_Bool body) ->
  (forall u, A u -> Q (open_tm body u)) ->
  forall u, A u -> Q (tm_app (tm_abs Ty_Bool body) u).
Proof.
  intros A Q body HA HQ Hlam Hbody u Hu.
  assert (Hmain : forall v, Acc (fun w z => z --> w) v ->
      A v -> Q (tm_app (tm_abs Ty_Bool body) v)).
  { intros v Hacc. induction Hacc as [v IH]. intros Hv.
    apply (@p_nc Q HQ (tm_app (tm_abs Ty_Bool body) v)).
    - apply neutral_app.
    - apply lc_tm_app; [exact Hlam|exact (@p_lc A HA v Hv)].
    - intros w Hstep. inversion Hstep; subst.
      + apply Hbody. exact Hv.
      + inversion H2; subst.
      + eapply H; [exact H4|]. eapply (@p_cl A HA); eauto.
  }
  eapply Hmain; [apply sn_accessible; exact (@p_sn A HA u Hu)|exact Hu].
Qed.

Lemma neutral_if : forall c t1 t2, neutral (tm_if c t1 t2).
Proof. unfold neutral. intros c t1 t2 H; inversion H; subst; try (match goal with Hn : numeric_value _ |- _ => inversion Hn end). Qed.
Lemma neutral_choice : forall t1 t2, neutral (tm_choice t1 t2).
Proof. unfold neutral. intros t1 t2 H; inversion H; subst; try (match goal with Hn : numeric_value _ |- _ => inversion Hn end). Qed.

Lemma reducible_if_intro : forall C c t1 t2,
  reducible C -> locally_closed_tm c -> locally_closed_tm t1 -> locally_closed_tm t2 ->
  strongly_normalizing c -> C t1 -> C t2 -> C (tm_if c t1 t2).
Proof.
  intros C c t1 t2 HC Hlc Hlc1 Hlc2 Hsn.
  induction Hsn as [c Hnext IH]. intros H1 H2.
  apply (@p_nc C HC (tm_if c t1 t2)).
  - apply neutral_if.
  - apply lc_tm_if; assumption.
  - intros u Hstep. inversion Hstep; subst.
    + exact H1.
    + exact H2.
    + pose proof (step_lc c t1' Hlc H4) as Hlc'.
      exact (IH t1' H4 Hlc' H1 H2).
Qed.

Lemma reducible_choice_intro : forall C t1 t2,
  reducible C -> locally_closed_tm t1 -> locally_closed_tm t2 ->
  C t1 -> C t2 -> C (tm_choice t1 t2).
Proof.
  intros C t1 t2 HC Hlc1 Hlc2 H1 H2.
  apply (@p_nc C HC (tm_choice t1 t2)).
  - apply neutral_choice.
  - apply lc_tm_choice; assumption.
  - intros u Hstep. inversion Hstep; subst; assumption.
Qed.


Lemma numeric_sn_lc : forall n, numeric_value n -> sn_lc_candidate n.
Proof.
  intros n Hn. split.
  - induction Hn; constructor; assumption.
  - constructor. intros u Hs. exfalso. eapply numeric_no_step; eauto.
Qed.

Lemma neutral_natrec : forall n b s, neutral (tm_natrec n b s).
Proof.
  unfold neutral. intros n b s Hval. inversion Hval; subst; try discriminate.
  match goal with Hn : numeric_value (tm_natrec _ _ _) |- _ => inversion Hn end.
Qed.

Lemma natrec_with_numeric : forall C F n,
  reducible C -> reducible F ->
  (forall s n r, F s -> sn_lc_candidate n -> C r -> C (tm_app (tm_app s n) r)) ->
  numeric_value n -> sn_lc_candidate n ->
  forall b s, C b -> F s -> C (tm_natrec n b s).
Proof.
  intros C F n HC HF Hfun Hnum.
  induction Hnum as [|n Hnum IH]; intros HN b s Hb Hs.
  - assert (Hmain : forall b', Acc (fun u v => v --> u) b' -> C b' ->
        forall s', Acc (fun u v => v --> u) s' -> F s' -> C (tm_natrec tm_zero b' s')).
    { intros b' Hbacc. induction Hbacc as [b' IHb]. intros Hb' s' Hsacc.
      induction Hsacc as [s' IHs]. intros Hs'.
      apply (@p_nc C HC (tm_natrec tm_zero b' s')).
      - apply neutral_natrec.
      - apply lc_tm_rec; [constructor|exact (@p_lc C HC b' Hb')|exact (@p_lc F HF s' Hs')].
      - intros u Hstep. inversion Hstep; subst.
        + exfalso. eapply numeric_no_step; [constructor|exact H4].
        + eapply H; [exact H6|eapply (@p_cl C HC); eauto|exact (Acc_intro s' IHs)|exact Hs'].
        + eapply H0.
          * match goal with Hred : s' --> ?q |- _ => exact Hred end.
          * eapply (@p_cl F HF); eauto.
        + exact Hb'.
    }
    exact (Hmain b (sn_accessible b (@p_sn C HC b Hb)) Hb
      s (sn_accessible s (@p_sn F HF s Hs)) Hs).
  - assert (Hmain : forall b', Acc (fun u v => v --> u) b' -> C b' ->
        forall s', Acc (fun u v => v --> u) s' -> F s' -> C (tm_natrec (tm_succ n) b' s')).
    { intros b' Hbacc. induction Hbacc as [b' IHb]. intros Hb' s' Hsacc.
      induction Hsacc as [s' IHs]. intros Hs'.
      apply (@p_nc C HC (tm_natrec (tm_succ n) b' s')).
      - apply neutral_natrec.
      - apply lc_tm_rec; [apply lc_tm_succ; exact (proj1 (numeric_sn_lc n Hnum))|exact (@p_lc C HC b' Hb')|exact (@p_lc F HF s' Hs')].
      - intros u Hstep. inversion Hstep; subst.
        + exfalso. eapply numeric_no_step; [constructor; exact Hnum|exact H4].
        + eapply H.
          * match goal with Hred : b' --> ?q |- _ => exact Hred end.
          * eapply (@p_cl C HC); eauto.
          * exact (Acc_intro s' IHs).
          * exact Hs'.
        + eapply H0.
          * match goal with Hred : s' --> ?q |- _ => exact Hred end.
          * eapply (@p_cl F HF); eauto.
        + apply Hfun; [exact Hs'|exact (numeric_sn_lc n Hnum)|].
          apply (IH (numeric_sn_lc n Hnum) b' s' Hb' Hs').
    }
    exact (Hmain b (sn_accessible b (@p_sn C HC b Hb)) Hb
      s (sn_accessible s (@p_sn F HF s Hs)) Hs).
Qed.

Lemma interp_natrec : forall rho theta R n b s,
  admissible rho theta ->
  interp rho theta Ty_Nat n -> interp rho theta R b ->
  interp rho theta (Ty_Arrow Ty_Nat (Ty_Arrow R R)) s ->
  interp rho theta R (tm_natrec n b s).
Proof.
  intros rho theta R n b s Had Hn Hb Hs.
  destruct (interp_reducible rho theta Ty_Nat Had) as [HNlc HNsn HNcl HNnc].
  destruct (interp_reducible rho theta R Had) as [HClc HCsn HCcl HCnc].
  destruct (interp_reducible rho theta (Ty_Arrow Ty_Nat (Ty_Arrow R R)) Had)
    as [HFlc HFsn HFcl HFnc].
  assert (Hgeneral : forall z, strongly_normalizing z -> interp rho theta Ty_Nat z ->
      forall b0, strongly_normalizing b0 -> interp rho theta R b0 ->
      forall s0, strongly_normalizing s0 -> interp rho theta (Ty_Arrow Ty_Nat (Ty_Arrow R R)) s0 ->
      interp rho theta R (tm_natrec z b0 s0)).
  { intros z Hsn. induction Hsn as [z Hnext IHn].
    intros Hnrel b0 HbSN Hbbase s0 HsSN Hsfunc.
    assert (Hmain : forall b', Acc (fun u v => v --> u) b' -> interp rho theta R b' ->
        forall s', Acc (fun u v => v --> u) s' ->
        interp rho theta (Ty_Arrow Ty_Nat (Ty_Arrow R R)) s' ->
        interp rho theta R (tm_natrec z b' s')).
    { intros b' Hbacc. induction Hbacc as [b' IHb]. intros Hbrel s' Hsacc.
      induction Hsacc as [s' IHs]. intros Hsrel.
      apply (@p_nc (interp rho theta R) (interp_reducible rho theta R Had)
        (tm_natrec z b' s')).
      - apply neutral_natrec.
      - apply lc_tm_rec; [exact (HNlc z Hnrel)|exact (HClc b' Hbrel)|exact (HFlc s' Hsrel)].
      - intros u Hstep. inversion Hstep; subst.
        + eapply IHn.
          * exact H4.
          * eapply HNcl; eauto.
          * apply accessible_sn. exact (Acc_intro b' IHb).
          * exact Hbrel.
          * apply accessible_sn. exact (Acc_intro s' IHs).
          * exact Hsrel.
        + eapply H.
          * match goal with Hred : b' --> ?q |- _ => exact Hred end.
          * eapply HCcl; eauto.
          * exact (Acc_intro s' IHs).
          * exact Hsrel.
        + eapply H0.
          * match goal with Hred : s' --> ?q |- _ => exact Hred end.
          * eapply HFcl; eauto.
        + exact Hbrel.
        + pose proof Hsrel as Hsrel0. destruct Hsrel0 as [_ Hsf].
          assert (Hfun : forall sfun qn r, interp rho theta (Ty_Arrow Ty_Nat (Ty_Arrow R R)) sfun ->
              sn_lc_candidate qn -> interp rho theta R r ->
              interp rho theta R (tm_app (tm_app sfun qn) r)).
          { intros sfun qn r Hsfun Hn0 Hr.
            destruct Hsfun as [_ Hsf1]. destruct (Hsf1 qn Hn0) as [_ Hsf2].
            apply Hsf2. exact Hr. }
          assert (Hprev : interp rho theta R (tm_natrec n0 b' s')).
          { eapply natrec_with_numeric.
            - apply interp_reducible; exact Had.
            - apply interp_reducible; exact Had.
            - exact Hfun.
            - exact H4.
            - apply numeric_sn_lc; exact H4.
            - exact Hbrel.
            - exact Hsrel. }
          eapply Hfun; [exact Hsrel|apply numeric_sn_lc; exact H4|exact Hprev].
    }
    exact (Hmain b0 (sn_accessible b0 HbSN) Hbbase
      s0 (sn_accessible s0 HsSN) Hsfunc).
  }
  exact (Hgeneral n (HNsn n Hn) Hn b (HCsn b Hb) Hb s (HFsn s Hs) Hs).
Qed.

Theorem fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall rho theta gamma,
    admissible rho theta -> term_substitution_closed gamma ->
    env_related rho theta Gamma gamma ->
    interp rho theta T (subst_erased gamma t) /\ locally_closed_ty T.
Proof.
  intros Delta Gamma t T Hty. induction Hty;
    intros rho theta gamma Had Hgamma Henv; simpl in *.
  - split.
    + apply Henv with (x:=x); assumption.
    + eapply wf_ty_lc; eauto.
  - (* function abstraction *)
    pose proof (fresh_notin (L ++ dom_context Gamma ++ fv_tm t2)) as Hfreshx.
    assert (HnotL : ~ In (fresh (L ++ dom_context Gamma ++ fv_tm t2)) L).
    { intro Hin. apply Hfreshx. apply in_or_app. left. exact Hin. }
    assert (Hnotdom : ~ In (fresh (L ++ dom_context Gamma ++ fv_tm t2)) (dom_context Gamma)).
    { intro Hin. apply Hfreshx. apply in_or_app. right. apply in_or_app. left. exact Hin. }
    set (x := fresh (L ++ dom_context Gamma ++ fv_tm t2)).
    assert (Hx : ~ In x L) by exact HnotL.
    destruct (interp_reducible rho theta T1 Had) as [HAlc HAsn HAcl HAnc].
    split.
    +
    assert (Harg0 : interp rho theta T1 (tm_fvar 0)).
    { apply interp_variable. constructor; assumption. }
    assert (Henv0 : env_related rho theta (update Gamma x T1)
        (term_subst_update gamma x (tm_fvar 0))).
    { eapply env_related_term_update; [exact Hnotdom|exact Henv|exact Harg0]. }
    pose proof (H1 x Hx rho theta (term_subst_update gamma x (tm_fvar 0))
      Had (term_subst_update_closed gamma x (tm_fvar 0) Hgamma ltac:(unfold locally_closed_tm; constructor)) Henv0) as Hbody0.
    assert (Hfreshbody : ~ In x (fv_tm t2)).
    { intro Hin. apply Hfreshx. apply in_or_app. right. apply in_or_app. right. exact Hin. }
    assert (Heqbody0 : subst_erased (term_subst_update gamma x (tm_fvar 0))
        (open_tm t2 (tm_fvar x)) = open_tm (subst_erased gamma t2) (tm_fvar 0)).
    { unfold open_tm. apply subst_erased_open_rec; try assumption.
      unfold locally_closed_tm; constructor. }
    rewrite Heqbody0 in Hbody0. destruct Hbody0 as [Hbody0 HtyT2].
    assert (HlamLC : locally_closed_tm (tm_abs Ty_Bool (subst_erased gamma t2))).
    { apply lc_tm_abs; [constructor|].
      eapply lc_tm_at_open_tm_inv with (x:=0) (k:=0) (K:=0).
      exact (@p_lc (interp rho theta T2) (interp_reducible rho theta T2 Had)
        (open_tm (subst_erased gamma t2) (tm_fvar 0)) Hbody0). }
    split; [exact HlamLC|].
    intros u Hu.
    assert (Hbody_all : forall v, interp rho theta T1 v ->
       interp rho theta T2 (open_tm (subst_erased gamma t2) v)).
    { intros v Hv.
      assert (Henvv : env_related rho theta (update Gamma x T1)
          (term_subst_update gamma x v)).
      { eapply env_related_term_update; [exact Hnotdom|exact Henv|exact Hv]. }
      pose proof (H1 x Hx rho theta (term_subst_update gamma x v)
        Had (term_subst_update_closed gamma x v Hgamma (HAlc v Hv)) Henvv) as [Hbodyv _].
      unfold open_tm in Hbodyv. rewrite subst_erased_open_rec in Hbodyv.
      - exact Hbodyv.
      - exact Hgamma.
      - exact (HAlc v Hv).
      - exact Hfreshbody. }
    eapply (reducible_abs_intro (interp rho theta T1) (interp rho theta T2)
      (subst_erased gamma t2)); eauto using interp_reducible.
    + unfold locally_closed_ty. constructor.
      * eapply wf_ty_lc; eauto.
      * assert (Hargx : interp rho theta T1 (tm_fvar 0)) by (apply interp_variable; apply interp_reducible; exact Had).
        assert (Henvx : env_related rho theta (update Gamma x T1)
            (term_subst_update gamma x (tm_fvar 0))).
        { eapply env_related_term_update; [exact Hnotdom|exact Henv|exact Hargx]. }
        pose proof (H1 x Hx rho theta (term_subst_update gamma x (tm_fvar 0))
          Had (term_subst_update_closed gamma x (tm_fvar 0) Hgamma ltac:(unfold locally_closed_tm; constructor)) Henvx) as [_ HT2].
        exact HT2.
  - split.
    + pose proof (IHHty1 rho theta gamma Had Hgamma Henv) as [[Hlc1 Hrel] _].
      exact (Hrel (subst_erased gamma t2)
        (proj1 (IHHty2 rho theta gamma Had Hgamma Henv))).
    + pose proof (IHHty1 rho theta gamma Had Hgamma Henv) as [_ Htylc].
      inversion Htylc; assumption.
  - (* universal abstraction *)
    set (X := fresh (L ++ ftv_context Gamma ++ fv_ty T)).
    assert (HX_L : ~ In X L).
    { unfold X. intro Hin. apply (fresh_notin (L ++ ftv_context Gamma ++ fv_ty T)).
      apply in_or_app; left; exact Hin. }
    assert (HX_ctx : ~ In X (ftv_context Gamma)).
    { unfold X. intro Hin. apply (fresh_notin (L ++ ftv_context Gamma ++ fv_ty T)).
      apply in_or_app; right; apply in_or_app; left; exact Hin. }
    assert (HX_T : ~ In X (fv_ty T)).
    { unfold X. intro Hin. apply (fresh_notin (L ++ ftv_context Gamma ++ fv_ty T)).
      apply in_or_app; right; apply in_or_app; right; exact Hin. }
    assert (Htype_open : locally_closed_ty (open_ty T (Ty_FVar X))).
    { pose proof (H0 X HX_L rho theta gamma Had Hgamma Henv) as [_ HT]. exact HT. }
    assert (Hbody_lc : locally_closed_tm (subst_erased gamma t)).
    { pose proof (H0 X HX_L rho theta gamma Had Hgamma Henv) as [HB _].
      unfold open_tm_ty in HB. rewrite subst_erased_open_tm_ty_rec in HB. eapply p_lc; [apply interp_reducible; exact Had|exact HB]. }
    split.
    + intros P HP.
      destruct Had as [Hrho Htheta].
      assert (HadP : admissible rho (theta_update theta X P)).
      { split; [exact Hrho|]. intro Y. unfold theta_update. destruct (Nat.eqb X Y) eqn:E.
        - apply Nat.eqb_eq in E. subst. exact HP.
        - apply Htheta. }
      assert (HenvP : env_related rho (theta_update theta X P) Gamma gamma).
      { eapply env_related_type_update; eauto. }
      pose proof (H0 X HX_L rho (theta_update theta X P) gamma HadP Hgamma HenvP) as [HB _].
      unfold open_tm_ty in HB. rewrite subst_erased_open_tm_ty_rec in HB.
      assert (HlcT : lc_ty_at 1 T).
      { unfold locally_closed_ty in Htype_open. eapply lc_ty_at_open_inv; exact Htype_open. }
      pose proof (interp_open_candidate 0 rho theta P X T (subst_erased gamma t)
        ltac:(simpl; lia) HlcT HX_T) as Hbridge.
      assert (HbodyP : interp (P :: rho) theta T (subst_erased gamma t)).
      { apply (proj1 Hbridge). exact HB. }
      assert (HadPR : admissible (P :: rho) theta).
      { split; [constructor; [exact HP|exact Hrho]|exact Htheta]. }
      assert (HtabsLC : locally_closed_tm (tm_tabs (subst_erased gamma t))).
      { unfold locally_closed_tm. apply lc_tm_tabs.
        eapply lc_tm_at_monotone with (K:=0) (k:=0) (K':=1) (k':=0).
        - eapply p_lc; [apply interp_reducible; exact HadP|exact HB].
        - lia.
        - lia. }
      apply (@p_nc (interp (P :: rho) theta T) (interp_reducible (P :: rho) theta T HadPR)
        (tm_tapp (tm_tabs (subst_erased gamma t)) Ty_Bool)).
      * apply neutral_tapp.
      * apply lc_tm_tapp; [exact HtabsLC|constructor].
      * intros v Hv. inversion Hv; subst.
        -- unfold open_tm_ty; rewrite open_tm_ty_rec_subst_erased by exact Hgamma. exact HbodyP.
        -- inversion H3.
    + unfold locally_closed_ty. constructor.
      eapply lc_ty_at_open_inv with (X:=X). exact Htype_open.
  - (* universal elimination *)
    split.
    + pose proof (IHHty rho theta gamma Had Hgamma Henv) as [Hall HAllLC].
      inversion HAllLC; subst.
      set (P := interp rho theta U).
      assert (HP : reducible P) by (unfold P; apply interp_reducible; exact Had).
      assert (HadP : admissible (P :: rho) theta).
      { destruct Had as [Hrho Htheta]. split; [constructor; [exact HP|exact Hrho]|exact Htheta]. }
      pose proof (Hall P HP) as Hinst.
      assert (Hbridge := interp_open_semantic 0 rho theta U T ltac:(lia)
        (wf_ty_lc _ _ H) H2 (tm_tapp (subst_erased gamma t) Ty_Bool)).
      simpl in Hbridge. exact (proj1 Hbridge Hinst).
    + pose proof (proj2 (IHHty rho theta gamma Had Hgamma Henv)) as HAllLC.
      inversion HAllLC; subst. unfold locally_closed_ty.
      eapply lc_ty_at_open.
      * exact H2.
      * eapply wf_ty_lc; eauto.
  - split.
    + split; [constructor|]. constructor; intros u Hs; inversion Hs.
    + constructor.
  - split.
    + split; [constructor|]. constructor; intros u Hs; inversion Hs.
    + constructor.
  - (* conditional *)
    pose proof (IHHty1 rho theta gamma Had Hgamma Henv) as [HC _].
    pose proof (IHHty2 rho theta gamma Had Hgamma Henv) as [H1 _].
    pose proof (IHHty3 rho theta gamma Had Hgamma Henv) as [H2 _].
    destruct (interp_reducible rho theta Ty_Bool Had) as [HclC HsnC HredC HncC].
    destruct (interp_reducible rho theta T Had) as [HRlc HRsn HRcl HRnc].
    split.
    + exact (@reducible_if_intro (interp rho theta T)
        (subst_erased gamma t1) (subst_erased gamma t2) (subst_erased gamma t3)
        (interp_reducible rho theta T Had)
        (HclC _ HC) (HRlc _ H1) (HRlc _ H2) (HsnC _ HC) H1 H2).
    + exact (proj2 (IHHty2 rho theta gamma Had Hgamma Henv)).
  - split.
    + split; [constructor|]. constructor; intros u Hs; inversion Hs.
    + constructor.
  - pose proof (IHHty rho theta gamma Had Hgamma Henv) as [Hn _].
    destruct Hn as [Hlc Hsn].
    split.
    + split; [apply lc_tm_succ; exact Hlc|apply sn_succ; exact Hsn].
    + constructor.
  - (* primitive recursion *)
    pose proof (IHHty1 rho theta gamma Had Hgamma Henv) as [Hn _].
    pose proof (IHHty2 rho theta gamma Had Hgamma Henv) as [Hb HTlc].
    pose proof (IHHty3 rho theta gamma Had Hgamma Henv) as [Hs _].
    split.
    + eapply interp_natrec; eauto.
    + exact HTlc.
  - (* choice *)
    pose proof (IHHty1 rho theta gamma Had Hgamma Henv) as [HC _].
    pose proof (IHHty2 rho theta gamma Had Hgamma Henv) as [HC2 _].
    destruct (interp_reducible rho theta T Had) as [HRlc HRsn HRcl HRnc].
    split.
    + exact (@reducible_choice_intro (interp rho theta T)
        (subst_erased gamma t1) (subst_erased gamma t2)
        (interp_reducible rho theta T Had) (HRlc _ HC) (HRlc _ HC2) HC HC2).
    + exact (proj2 (IHHty1 rho theta gamma Had Hgamma Henv)).
Qed.

Lemma subst_erased_identity : forall t,
  subst_erased identity_term_substitution t = erase_tm t.
Proof.
  induction t; simpl; try rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3; reflexivity.
Qed.

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  intros t T Hty.
  set (theta := fun _ : atom => sn_lc_candidate).
  assert (Had : admissible [] theta).
  { split; [constructor|]. intro X. apply reducible_sn_lc. }
  assert (Hgamma : term_substitution_closed identity_term_substitution).
  { apply identity_term_substitution_closed. }
  assert (Henv : env_related [] theta empty identity_term_substitution).
  { intros x A Hlookup. discriminate. }
  pose proof (fundamental [] empty t T Hty [] theta identity_term_substitution Had Hgamma Henv)
    as [Hrel _].
  unfold theta in Had.
  pose proof (interp_reducible [] (fun _ : atom => sn_lc_candidate) T Had) as Hred.
  pose proof (@p_sn (interp [] (fun _ : atom => sn_lc_candidate) T) Hred
    (subst_erased identity_term_substitution t) Hrel) as Hsn.
  rewrite subst_erased_identity in Hsn. apply sn_erase_preimage. exact Hsn.
Qed.

End SystemFNormalizationIfNondeterminismRecursionEasyTask.
