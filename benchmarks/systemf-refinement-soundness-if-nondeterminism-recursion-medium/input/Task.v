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
  - apply lc_ty_bool.
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
  - apply lc_tm_true.
  - apply lc_tm_false.
  - apply lc_tm_if; assumption.
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
  - apply lc_ty_bool.
  - apply lc_ty_bool.
  - exact IHHty2.
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
  - apply lc_ty_bool.
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
  - apply lc_tm_true.
  - apply lc_tm_false.
  - eauto using lc_tm_at.
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
  - reflexivity.
  - repeat rewrite in_app_iff in Hfresh.
    rewrite IHt1, IHt2, IHt3 by (try assumption; intuition). reflexivity.
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
      |  |  | c IHc a IHa b IHb |  | n IHn | n IHn b IHb s IHs | a IHa b IHb];
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
  - reflexivity.
  - repeat rewrite in_app_iff in Hfresh.
    rewrite IHc, IHa, IHb by (try assumption; intuition). reflexivity.
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
  | Ty_Bool => value v /\ (v = tm_true \/ v = tm_false)
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

Lemma strong_expression_app : forall T1 T2 t1 t2,
  strong_expression_relation (Ty_Arrow T1 T2) t1 ->
  strong_expression_relation T1 t2 ->
  strong_expression_relation T2 (tm_app t1 t2).
Proof.
  intros T1 T2 t1 t2 [Hlc1 [Hsn1 Hall1]] HE2.
  revert T1 T2 Hlc1 Hall1 t2 HE2.
  induction Hsn1 as [t1 Hnext1 IH1]. intros T1 T2 Hlc1 Hall1 t2 [Hlc2 [Hsn2 Hall2]].
  revert Hlc2 Hall2. induction Hsn2 as [t2 Hnext2 IH2]. intros Hlc2 Hall2.
  apply strong_expression_of_reducts.
  - apply lc_tm_app; assumption.
  - intros Hv. inversion Hv; subst; try match goal with H : numeric_value _ |- _ => inversion H end.
  - intros u Hstep. inversion Hstep; subst.
    + pose proof (Hall1 (tm_abs T t) (multi_refl _) (v_abs T t H1)) as HVfun.
      pose proof (Hall2 t2 (multi_refl _) H3) as HVarg.
      destruct HVfun as [_ [U [body [Heq Hmap]]]].
      injection Heq as E1 E2. subst U body. apply Hmap. exact HVarg.
    + apply (IH1 t1' H1 T1 T2).
      * eapply step_preserves_lc; eauto.
      * intros v Hm Hv. apply (Hall1 v); auto. eapply multi_step; eauto.
      * split. exact Hlc2. split. apply SN_intro. exact Hnext2. exact Hall2.
    + apply (IH2 t2' H3).
      * eapply step_preserves_lc; eauto.
      * intros v Hm Hv. apply (Hall2 v); auto. eapply multi_step; eauto.
Qed.

Lemma strong_expression_choice : forall T t1 t2,
  strong_expression_relation T t1 ->
  strong_expression_relation T t2 ->
  strong_expression_relation T (tm_choice t1 t2).
Proof.
  intros T t1 t2 HE1 HE2.
  destruct HE1 as [Hlc1 [Hsn1 Hall1]].
  destruct HE2 as [Hlc2 [Hsn2 Hall2]].
  apply strong_expression_of_reducts.
  - apply lc_tm_choice; assumption.
  - intro Hvalue. inversion Hvalue; subst; try match goal with H : numeric_value _ |- _ => inversion H end.
  - intros u Hstep. inversion Hstep; subst.
    + exact (conj Hlc1 (conj Hsn1 Hall1)).
    + exact (conj Hlc2 (conj Hsn2 Hall2)).
Qed.

Lemma strong_expression_if : forall T t1 t2 t3,
  strong_expression_relation Ty_Bool t1 ->
  strong_expression_relation T t2 ->
  strong_expression_relation T t3 ->
  strong_expression_relation T (tm_if t1 t2 t3).
Proof.
  intros T t1 t2 t3 [Hlc [Hsn Hall]] H2 H3.
  revert Hlc Hall. induction Hsn as [t1 Hnext IH]. intros Hlc Hall.
  apply strong_expression_of_reducts.
  - apply lc_tm_if.
    + exact Hlc.
    + exact (proj1 H2).
    + exact (proj1 H3).
  - intro Hv. inversion Hv; subst; try match goal with H : numeric_value _ |- _ => inversion H end.
  - intros u Hstep. inversion Hstep; subst.
    + exact H2.
    + exact H3.
    + apply (IH t1' H4).
      * eapply step_preserves_lc; eauto.
      * intros v Hsteps Hv. apply Hall with (v := v); auto.
        eapply multi_step; eauto.
Qed.

Lemma strong_numeral_relation : forall n,
  strong_value_relation Ty_Nat (numeral n).
Proof.
  intros n. split.
  - apply v_nat. apply numeral_numeric.
  - apply numeral_numeric.
Qed.

Lemma strong_expression_succ : forall t,
  strong_expression_relation Ty_Nat t ->
  strong_expression_relation Ty_Nat (tm_succ t).
Proof.
  intros t [Hlc [Hsn Hall]]. revert Hlc Hall.
  induction Hsn as [t Hnext IH]. intros Hlc Hall.
  apply strong_expression_intro.
  - apply lc_tm_succ. exact Hlc.
  - intros Hv. split. exact Hv.
    inversion Hv; subst. assumption.
  - intros u Hstep. inversion Hstep; subst.
    apply (IH t' H0).
    + eapply step_preserves_lc; eauto.
    + intros v Hsteps Hv. apply Hall with (v := v); auto.
      eapply multi_step; eauto.
Qed.

Lemma strong_expression_rec_numeral : forall n T b s,
  strong_value_relation T b ->
  strong_value_relation (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  strong_expression_relation T (tm_natrec (numeral n) b s).
Proof.
  induction n as [|n IH]; intros T b s Hb Hs;
    assert (Hbv : value b) by (eapply strong_value_relation_value; exact Hb);
    assert (Hsv : value s) by (eapply strong_value_relation_value; exact Hs);
    apply strong_expression_of_reducts.
  - apply lc_tm_rec.
    + apply lc_tm_zero.
    + apply value_regular. exact Hbv.
    + apply value_regular. exact Hsv.
  - intros Hv. inversion Hv; subst; try match goal with H : numeric_value _ |- _ => inversion H end.
  - intros u Hstep. inversion Hstep; subst;
      try solve [match goal with HV : value ?v, HS : ?v --> ?w |- _ =>
        exfalso; exact (value_no_step v HV w HS) end];
      try match goal with H : tm_zero --> _ |- _ => inversion H end.
    apply strong_value_is_expression. exact Hb.
  - apply lc_tm_rec.
    + apply numeric_value_lc. apply numeral_numeric.
    + apply value_regular. exact Hbv.
    + apply value_regular. exact Hsv.
  - intros Hv. inversion Hv; subst; try match goal with H : numeric_value _ |- _ => inversion H end.
  - intros u Hstep.
    assert (Hnv : numeric_value (numeral (S n))) by apply numeral_numeric.
    inversion Hstep; subst;
      try solve [match goal with HV : value ?v, HS : ?v --> ?w |- _ =>
        exfalso; exact (value_no_step v HV w HS) end];
      try solve [match goal with HN : numeric_value ?v, HS : ?v --> ?w |- _ =>
        exfalso; exact (numeric_no_step v HN w HS) end].
    apply strong_expression_app with (T1 := T).
    + apply strong_expression_app with (T1 := Ty_Nat).
      * apply strong_value_is_expression. exact Hs.
      * apply strong_value_is_expression. apply strong_numeral_relation.
    + apply IH; assumption.
Qed.

Lemma strong_expression_rec_values : forall T n b s,
  strong_value_relation Ty_Nat n ->
  strong_value_relation T b ->
  strong_value_relation (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  strong_expression_relation T (tm_natrec n b s).
Proof.
  intros T n b s [_ Hnum] Hb Hs.
  destruct (numeric_numeral n Hnum) as [k ->].
  apply strong_expression_rec_numeral; assumption.
Qed.

Lemma strong_expression_rec : forall T n b s,
  strong_expression_relation Ty_Nat n ->
  strong_expression_relation T b ->
  strong_expression_relation (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  strong_expression_relation T (tm_natrec n b s).
Proof.
  intros T n b s [Hnlc [Hnsn Hnall]] Hb Hs.
  revert T Hnlc Hnall b s Hb Hs.
  induction Hnsn as [n Hnnext IHn]. intros T Hnlc Hnall b s Hb Hs.
  destruct Hb as [Hblc [Hbsn Hball]]. revert Hblc Hball s Hs.
  induction Hbsn as [b Hbnext IHb]. intros Hblc Hball s Hs.
  destruct Hs as [Hslc [Hssn Hsall]]. revert Hslc Hsall.
  induction Hssn as [s Hsnext IHs]. intros Hslc Hsall.
  assert (Hready : numeric_value n -> value b -> value s ->
    strong_expression_relation T (tm_natrec n b s)).
  {
    intros Hnum Hbv Hsv. apply strong_expression_rec_values.
    - split. apply v_nat. exact Hnum. exact Hnum.
    - apply Hball. apply multi_refl. exact Hbv.
    - apply Hsall. apply multi_refl. exact Hsv.
  }
  apply strong_expression_of_reducts.
  - apply lc_tm_rec; assumption.
  - intros Hv. inversion Hv; subst; try match goal with H : numeric_value _ |- _ => inversion H end.
  - intros u Hstep. inversion Hstep; subst.
    + eapply IHn.
      * eassumption.
      * eapply step_preserves_lc; eauto.
      * intros v Hsteps Hv. apply Hnall with (v := v); auto. eapply multi_step; eauto.
      * split. exact Hblc. split. apply SN_intro. exact Hbnext. exact Hball.
      * split. exact Hslc. split. apply SN_intro. exact Hsnext. exact Hsall.
    + eapply IHb.
      * eassumption.
      * eapply step_preserves_lc; eauto.
      * intros v Hsteps Hv. apply Hball with (v := v); auto. eapply multi_step; eauto.
      * split. exact Hslc. split. apply SN_intro. exact Hsnext. exact Hsall.
    + eapply IHs.
      * eassumption.
      * eapply step_preserves_lc; eauto.
      * intros v Hsteps Hv. apply Hsall with (v := v); auto. eapply multi_step; eauto.
    + eapply strong_expression_step.
      * apply Hready. apply nv_zero. assumption. assumption.
      * exact Hstep.
    + eapply strong_expression_step.
      * apply Hready. apply nv_succ. assumption. assumption. assumption.
      * exact Hstep.
Qed.

End Compatibility.

Lemma strong_expression_tapp : forall eta rho T t U a,
  expression_relation eta rho (Ty_All T) t -> locally_closed_ty U ->
  expression_relation (a :: eta) rho T (tm_tapp t U).
Proof.
  intros eta rho T t U a [Hlc [Hsn Hall]] HU.
  revert Hlc Hall. induction Hsn as [t Hnext IH]. intros Hlc Hall.
  apply (strong_expression_of_reducts (a :: eta) rho T).
  - apply lc_tm_tapp; assumption.
  - intros Hv. inversion Hv; subst; try match goal with H : numeric_value _ |- _ => inversion H end.
  - intros u Hstep. inversion Hstep; subst.
    + match goal with H : locally_closed_tm (tm_tabs ?b) |- _ =>
        pose proof (Hall _ (multi_refl _) (v_tabs b H)) as HV end.
      destruct HV as [_ [body [Heq Hmap]]]. injection Heq as ->.
      apply Hmap. exact HU.
    + eapply IH.
      * eassumption.
      * eapply step_preserves_lc; eauto.
      * intros v Hm Hv. apply (Hall v); auto. eapply multi_step; eauto.
Qed.

Definition related_substitution (rho : relation_env) (Gamma : context)
    (gamma : term_substitution) : Prop :=
  forall x T, lookup_context x Gamma = Some T -> value_relation [] rho T (gamma x).

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

Theorem fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall theta rho gamma,
    type_substitution_closed theta -> term_substitution_closed gamma ->
    related_substitution rho Gamma gamma ->
    expression_relation [] rho T (instantiate theta gamma t).
Proof.
  intros Delta Gamma t T Hty.
  induction Hty as
      [Delta Gamma x T Hlookup Hwf
      | L Delta Gamma T1 body T2 Hwf Hbody IHbody
      | Delta Gamma t1 t2 T1 T2 Ht1 IHt1 Ht2 IHt2
      | L Delta Gamma body T Hbody IHbody
      | Delta Gamma t T U Ht IHt HU
      | Delta Gamma
      | Delta Gamma
      | Delta Gamma t1 t2 t3 T Ht1 IHt1 Ht2 IHt2 Ht3 IHt3
      | Delta Gamma
      | Delta Gamma n Hn IHn
      | Delta Gamma n b s T Hn IHn Hb IHb Hs IHs
      | Delta Gamma t1 t2 T Ht1 IHt1 Ht2 IHt2];
    intros theta rho gamma Htheta Hgamma Hterms.
  - apply strong_value_is_expression. apply Hterms. exact Hlookup.
  - assert (Hwhole : has_type Delta Gamma (tm_abs T1 body) (Ty_Arrow T1 T2)).
    { eapply T_Abs; eauto. }
    assert (Hvlc : locally_closed_tm (instantiate theta gamma (tm_abs T1 body))).
    { apply instantiate_closed; try assumption. eapply typing_lc; eauto. }
    apply strong_value_is_expression. cbn [value_relation instantiate].
    split. apply v_abs. exact Hvlc.
    exists (instantiate_ty theta T1), (instantiate theta gamma body).
    split. reflexivity. intros arg Harg.
    assert (Harglc : locally_closed_tm arg).
    { apply value_regular. eapply value_relation_value. exact Harg. }
    set (x := fresh (L ++ fv_tm body)).
    assert (Hxall : ~ In x (L ++ fv_tm body)) by (subst x; apply fresh_notin).
    rewrite in_app_iff in Hxall.
    assert (HxL : ~ In x L) by tauto.
    assert (Hxbody : ~ In x (fv_tm body)) by tauto.
    pose proof (IHbody x HxL theta rho (term_subst_update gamma x arg)
      Htheta (term_subst_update_closed gamma x arg Hgamma Harglc)
      (related_substitution_update rho Gamma gamma x T1 arg Hterms Harg)) as IH.
    rewrite (instantiate_open_tm body theta gamma x arg Hxbody Htheta Hgamma Harglc) in IH.
    exact IH.
  - apply strong_expression_app with (T1 := T1); [apply IHt1|apply IHt2]; assumption.
  - assert (Hwhole : has_type Delta Gamma (tm_tabs body) (Ty_All T)).
    { eapply T_TAbs; eauto. }
    assert (Hvlc : locally_closed_tm (instantiate theta gamma (tm_tabs body))).
    { apply instantiate_closed; try assumption. eapply typing_lc; eauto. }
    apply strong_value_is_expression. cbn [value_relation instantiate].
    split. apply v_tabs. exact Hvlc.
    exists (instantiate theta gamma body). split. reflexivity.
    intros U a HU.
    set (X := fresh (L ++ fv_ty T ++ ftv_tm body ++ ftv_context Gamma)).
    assert (HXall : ~ In X (L ++ fv_ty T ++ ftv_tm body ++ ftv_context Gamma))
      by (subst X; apply fresh_notin).
    repeat rewrite in_app_iff in HXall.
    assert (HXL : ~ In X L) by tauto.
    assert (HXT : ~ In X (fv_ty T)) by tauto.
    assert (HXbody : ~ In X (ftv_tm body)) by tauto.
    assert (HXGamma : ~ In X (ftv_context Gamma)) by tauto.
    pose proof (IHbody X HXL (type_subst_update theta X U)
      (relation_update rho X a) gamma
      (type_subst_update_closed theta X U Htheta HU) Hgamma
      (related_substitution_relation_update rho Gamma gamma X a Hterms HXGamma)) as IH.
    rewrite (instantiate_open_ty body theta gamma X U HXbody Htheta Hgamma HU) in IH.
    assert (HTlc : lc_ty_at 1 T).
    { pose proof (typing_type_lc _ _ _ _ Hwhole) as HH. inversion HH; assumption. }
    apply (proj2 (expression_lifting_equiv _ _
      (value_relation_open_relation T 0 [] rho X a eq_refl HTlc HXT) _)).
    exact IH.
  - cbn [instantiate].
    pose proof (IHt theta rho gamma Htheta Hgamma Hterms) as HE.
    assert (HUlc : locally_closed_ty U) by (eapply wf_ty_lc; eauto).
    assert (HUinst : locally_closed_ty (instantiate_ty theta U)).
    { apply instantiate_ty_closed; assumption. }
    pose proof (strong_expression_tapp [] rho T _ (instantiate_ty theta U)
      (interpreted_candidate [] rho U) HE HUinst) as Hout.
    assert (HTlc : lc_ty_at 1 T).
    { pose proof (typing_type_lc _ _ _ _ Ht) as HH. inversion HH; assumption. }
    apply (proj1 (expression_lifting_equiv _ _
      (value_relation_open_type T 0 [] rho U eq_refl HTlc HUlc) _)). exact Hout.
  - apply strong_value_is_expression. split. apply v_true. left. reflexivity.
  - apply strong_value_is_expression. split. apply v_false. right. reflexivity.
  - apply strong_expression_if; [apply IHt1|apply IHt2|apply IHt3]; assumption.
  - apply strong_value_is_expression. apply (strong_numeral_relation [] rho 0).
  - apply strong_expression_succ. apply IHn; assumption.
  - apply strong_expression_rec; [apply IHn|apply IHb|apply IHs]; assumption.
  - apply strong_expression_choice; [apply IHt1|apply IHt2]; assumption.
Qed.

Definition empty_relation_env : relation_env := fun _ => None.

Theorem strong_normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  intros t T HT.
  assert (Hempty : related_substitution empty_relation_env empty identity_term_substitution).
  { intros x U Hlookup. discriminate Hlookup. }
  pose proof (fundamental [] empty t T HT identity_type_substitution empty_relation_env
    identity_term_substitution identity_type_substitution_closed
    identity_term_substitution_closed Hempty) as Hrel.
  rewrite instantiate_identity in Hrel.
  exact (proj1 (proj2 Hrel)).
Qed.

End SystemFNormalizationIfNondeterminismRecursionEasyTask.

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.

Module CombinedCoreTyping.
Import SystemFNormalizationIfNondeterminismRecursionEasyTask.
Import ListNotations.

Definition ty_context_included (Delta Delta' : ty_context) : Prop :=
  forall X, In X Delta -> In X Delta'.

Definition context_included (Gamma Gamma' : context) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    lookup_context x Gamma' = Some T.

Lemma wf_ty_weaken : forall Delta T,
  wf_ty Delta T ->
  forall Delta', ty_context_included Delta Delta' -> wf_ty Delta' T.
Proof.
  intros Delta T Hwf. induction Hwf; intros Delta' Hinc.
  - apply WF_Var. apply Hinc. assumption.
  - apply WF_Arrow; auto.
  - apply WF_All with L. intros X Hfresh.
    apply H0. exact Hfresh.
    unfold ty_context_included in *. simpl. intros Y [E | Hin].
    + left. exact E.
    + right. apply Hinc. exact Hin.
  - apply WF_Bool.
  - apply WF_Nat.
Qed.

Lemma has_type_weaken_context : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall Gamma', context_included Gamma Gamma' ->
  has_type Delta Gamma' t T.
Proof.
  intros Delta Gamma t T Hty. induction Hty; intros Gamma' Hinc.
  - apply T_Var; [apply Hinc; assumption | assumption].
  - apply T_Abs with L; [assumption |]. intros x Hfresh.
    apply H1. exact Hfresh.
    unfold context_included in *. intros y U Hlookup.
    unfold update in *. simpl in *.
    destruct (Nat.eqb y x); [exact Hlookup |].
    apply Hinc. exact Hlookup.
  - apply T_App with T1; auto.
  - apply T_TAbs with L. intros X Hfresh. apply H0; assumption.
  - eapply T_TApp; eauto.
  - apply T_True.
  - apply T_False.
  - eapply T_If; eauto.
  - apply T_Zero.
  - apply T_Succ. auto.
  - eapply T_Rec; eauto.  - eapply T_Choice; eauto.
Qed.

Lemma has_type_weaken_type : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall Delta', ty_context_included Delta Delta' ->
  has_type Delta' Gamma t T.
Proof.
  intros Delta Gamma t T Hty. induction Hty; intros Delta' Hinc.
  - apply T_Var; [assumption | eapply wf_ty_weaken; eauto].
  - apply T_Abs with L.
    + eapply wf_ty_weaken; eauto.
    + intros x Hfresh. apply H1; assumption.
  - apply T_App with T1; auto.
  - apply T_TAbs with L. intros X Hfresh.
    apply H0. exact Hfresh.
    unfold ty_context_included in *. simpl. intros Y [E | Hin].
    + left. exact E.
    + right. apply Hinc. exact Hin.
  - eapply T_TApp; eauto. eapply wf_ty_weaken; eauto.
  - apply T_True.
  - apply T_False.
  - eapply T_If; eauto.
  - apply T_Zero.
  - apply T_Succ. auto.
  - eapply T_Rec; eauto.  - eapply T_Choice; eauto.
Qed.

Definition type_substitution_wf
    (Delta Delta' : ty_context) (theta : type_substitution) : Prop :=
  forall X, In X Delta -> wf_ty Delta' (theta X).

Lemma fv_ty_open_rec_preserves : forall T k U X,
  In X (fv_ty T) -> In X (fv_ty (open_ty_rec k U T)).
Proof.
  induction T; intros k U X Hin; simpl in *.
  - contradiction.
  - exact Hin.
  - apply in_app_iff in Hin. apply in_app_iff.
    destruct Hin as [Hin | Hin].
    + left. apply IHT1. exact Hin.
    + right. apply IHT2. exact Hin.
  - apply IHT. exact Hin.
  - contradiction.
  - contradiction.
Qed.

Lemma wf_ty_fv : forall Delta T,
  wf_ty Delta T -> forall X, In X (fv_ty T) -> In X Delta.
Proof.
  intros Delta T Hwf. induction Hwf; intros Y Hin; simpl in *.
  - destruct Hin as [E | Hin].
    + subst. assumption.
    + contradiction.
  - apply in_app_iff in Hin. destruct Hin; auto.
  - set (X := fresh (L ++ fv_ty T)).
    assert (HX : ~ In X (L ++ fv_ty T)).
    { subst X. apply fresh_notin. }
    rewrite in_app_iff in HX.
    assert (HXL : ~ In X L) by intuition.
    assert (HXfv : ~ In X (fv_ty T)) by intuition.
    pose proof (H0 X HXL Y) as IH.
    assert (Hopen : In Y (fv_ty (open_ty T (Ty_FVar X)))).
    { unfold open_ty. apply fv_ty_open_rec_preserves. exact Hin. }
    specialize (IH Hopen). simpl in IH.
    destruct IH as [E | HinDelta].
    + subst Y. contradiction.
    + exact HinDelta.
  - contradiction.
  - contradiction.
Qed.

Lemma instantiate_ty_open_rec_local : forall T k theta X U,
  ~ In X (fv_ty T) ->
  (forall Y, In Y (fv_ty T) -> locally_closed_ty (theta Y)) ->
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
    rewrite (proj2 (Nat.eqb_neq X a)) by assumption.
    symmetry. apply open_ty_rec_lc_at.
    eapply lc_ty_at_monotone.
    + apply Htheta. auto.
    + lia.
  - rewrite in_app_iff in Hfresh.
    assert (Hfresh1 : ~ In X (fv_ty T1)) by intuition.
    assert (Hfresh2 : ~ In X (fv_ty T2)) by intuition.
    rewrite (IHT1 k theta X U Hfresh1),
      (IHT2 k theta X U Hfresh2); try assumption.
    + reflexivity.
    + intros Y Hin. apply Htheta. apply in_app_iff. auto.
    + intros Y Hin. apply Htheta. apply in_app_iff. auto.
  - rewrite IHT; try assumption. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma instantiate_ty_open_local : forall T theta X U,
  ~ In X (fv_ty T) ->
  (forall Y, In Y (fv_ty T) -> locally_closed_ty (theta Y)) ->
  locally_closed_ty U ->
  instantiate_ty (type_subst_update theta X U)
    (open_ty T (Ty_FVar X)) =
  open_ty (instantiate_ty theta T) U.
Proof.
  intros. unfold open_ty. apply instantiate_ty_open_rec_local; assumption.
Qed.

Lemma wf_ty_instantiate : forall Delta T,
  wf_ty Delta T ->
  forall Delta' theta,
    type_substitution_wf Delta Delta' theta ->
    wf_ty Delta' (instantiate_ty theta T).
Proof.
  intros Delta T Hwf. induction Hwf; intros Delta' theta Htheta; simpl.
  - apply Htheta. assumption.
  - apply WF_Arrow; auto.
  - apply WF_All with (L ++ Delta ++ Delta' ++ fv_ty T).
    intros X Hfresh.
    repeat rewrite in_app_iff in Hfresh.
    assert (HXL : ~ In X L) by intuition.
    assert (HXDelta : ~ In X Delta) by intuition.
    assert (HXDelta' : ~ In X Delta') by intuition.
    assert (HXT : ~ In X (fv_ty T)) by intuition.
    pose proof (H0 X HXL (X :: Delta')
      (type_subst_update theta X (Ty_FVar X))) as IH.
    assert (Hsub : type_substitution_wf (X :: Delta) (X :: Delta')
      (type_subst_update theta X (Ty_FVar X))).
    { unfold type_substitution_wf in *. intros Y [E | Hin].
      - subst Y. unfold type_subst_update. rewrite Nat.eqb_refl.
        apply WF_Var. simpl. auto.
      - assert (Hneq : X <> Y).
        { intro E. subst. contradiction. }
        unfold type_subst_update.
        rewrite (proj2 (Nat.eqb_neq X Y)) by assumption.
        eapply wf_ty_weaken.
        + apply Htheta. exact Hin.
        + unfold ty_context_included. simpl. auto. }
    assert (Hopen :
      instantiate_ty (type_subst_update theta X (Ty_FVar X))
        (open_ty T (Ty_FVar X)) =
      open_ty (instantiate_ty theta T) (Ty_FVar X)).
    { apply instantiate_ty_open_local.
      - exact HXT.
      - intros Y Hin. apply wf_ty_lc with Delta'. apply Htheta.
        assert (Hwhole : wf_ty Delta (Ty_All T)).
        { apply WF_All with L. exact H. }
        eapply wf_ty_fv; [exact Hwhole |]. simpl. exact Hin.
      - apply lc_ty_fvar. }
    rewrite <- Hopen. exact (IH Hsub).
  - apply WF_Bool.
  - apply WF_Nat.
Qed.

Definition context_wf (Delta : ty_context) (Gamma : context) : Prop :=
  forall x T, lookup_context x Gamma = Some T -> wf_ty Delta T.

Definition term_substitution_typed
    (Gamma : context) (Delta' : ty_context) (Gamma' : context)
    (theta : type_substitution) (gamma : term_substitution) : Prop :=
  forall x T,
    lookup_context x Gamma = Some T ->
    has_type Delta' Gamma' (gamma x) (instantiate_ty theta T).

Lemma notin_dom_lookup_none : forall x Gamma,
  ~ In x (dom_context Gamma) -> lookup_context x Gamma = None.
Proof.
  intros x Gamma. induction Gamma as [|[y T] Gamma IH]; intros Hfresh; simpl in *.
  - reflexivity.
  - assert (Hxy : x <> y) by intuition.
    rewrite (proj2 (Nat.eqb_neq x y)) by assumption.
    apply IH. intuition.
Qed.

Lemma context_included_update_fresh : forall Gamma x T,
  ~ In x (dom_context Gamma) ->
  context_included Gamma (update Gamma x T).
Proof.
  intros Gamma x T Hfresh y U Hlookup. unfold update. simpl.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y.
    rewrite notin_dom_lookup_none in Hlookup by assumption. discriminate.
  - exact Hlookup.
Qed.

Lemma context_wf_update : forall Delta Gamma x T,
  context_wf Delta Gamma -> wf_ty Delta T ->
  context_wf Delta (update Gamma x T).
Proof.
  intros Delta Gamma x T Hctx HT y U Hlookup.
  unfold update in Hlookup. simpl in Hlookup.
  destruct (Nat.eqb y x) eqn:E.
  - inversion Hlookup; subst. exact HT.
  - apply Hctx with y. exact Hlookup.
Qed.

Lemma context_wf_weaken_type : forall Delta Gamma,
  context_wf Delta Gamma ->
  forall Delta', ty_context_included Delta Delta' ->
  context_wf Delta' Gamma.
Proof.
  intros Delta Gamma Hctx Delta' Hinc x T Hlookup.
  eapply wf_ty_weaken; [eapply Hctx; eauto | exact Hinc].
Qed.

Lemma instantiate_ty_update_irrelevant : forall T theta X U,
  ~ In X (fv_ty T) ->
  instantiate_ty (type_subst_update theta X U) T = instantiate_ty theta T.
Proof.
  induction T; intros theta X U Hfresh; simpl in *.
  - reflexivity.
  - unfold type_subst_update.
    assert (Hneq : X <> a) by (intro; subst; apply Hfresh; auto).
    rewrite (proj2 (Nat.eqb_neq X a)) by assumption. reflexivity.
  - rewrite in_app_iff in Hfresh.
    rewrite IHT1, IHT2; tauto.
  - f_equal. apply IHT. assumption.
  - reflexivity.
  - reflexivity.
Qed.

Lemma instantiate_ty_open_rec_commute : forall T k U theta,
  type_substitution_closed theta ->
  instantiate_ty theta (open_ty_rec k U T) =
  open_ty_rec k (instantiate_ty theta U) (instantiate_ty theta T).
Proof.
  induction T; intros k U theta Htheta; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. apply open_ty_rec_lc_at.
    eapply lc_ty_at_monotone; [apply Htheta | lia].
  - rewrite IHT1, IHT2; try assumption. reflexivity.
  - rewrite IHT; try assumption. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma instantiate_ty_open_commute : forall T U theta,
  type_substitution_closed theta ->
  instantiate_ty theta (open_ty T U) =
  open_ty (instantiate_ty theta T) (instantiate_ty theta U).
Proof.
  intros. unfold open_ty. apply instantiate_ty_open_rec_commute. assumption.
Qed.

Lemma has_type_instantiate : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  context_wf Delta Gamma ->
  forall Delta' Gamma' theta gamma,
    type_substitution_closed theta ->
    term_substitution_closed gamma ->
    type_substitution_wf Delta Delta' theta ->
    term_substitution_typed Gamma Delta' Gamma' theta gamma ->
    has_type Delta' Gamma'
      (instantiate theta gamma t) (instantiate_ty theta T).
Proof.
  intros Delta Gamma t T Hty. induction Hty as
      [Delta Gamma x T Hlookup Hwf
      | L Delta Gamma T1 body T2 Hwf Hbody IHbody
      | Delta Gamma t1 t2 T1 T2 Ht1 IHt1 Ht2 IHt2
      | L Delta Gamma body T Hbody IHbody
      | Delta Gamma t T U Ht IHt HU
      | Delta Gamma
      | Delta Gamma
      | Delta Gamma t1 t2 t3 T Ht1 IHt1 Ht2 IHt2 Ht3 IHt3
      | Delta Gamma
      | Delta Gamma n Hn IHn
      | Delta Gamma n b s T Hn IHn Hb IHb Hs IHs
      | Delta Gamma t1 t2 T Ht1 IHt1 Ht2 IHt2];
    intros Hctx Delta' Gamma' theta gamma Htheta Hgamma Htheta_wf Hgamma_ty;
    simpl.
  - eapply Hgamma_ty. exact Hlookup.
  - apply T_Abs with (L ++ fv_tm body ++ dom_context Gamma').
    + eapply wf_ty_instantiate; eauto.
    + intros x Hfresh. repeat rewrite in_app_iff in Hfresh.
      assert (HxL : ~ In x L) by intuition.
      assert (Hxbody : ~ In x (fv_tm body)) by intuition.
      assert (HxGamma' : ~ In x (dom_context Gamma')) by intuition.
      pose proof (IHbody x HxL
        (context_wf_update Delta Gamma x T1 Hctx Hwf)
        Delta' (update Gamma' x (instantiate_ty theta T1)) theta
        (term_subst_update gamma x (tm_fvar x))) as IH.
      rewrite <- (instantiate_open_tm body theta gamma x (tm_fvar x));
        try assumption; try apply lc_tm_fvar.
      apply IH; try assumption.
      * apply term_subst_update_closed; [assumption | apply lc_tm_fvar].
      * unfold term_substitution_typed. intros y U Hlookup'.
        unfold update in Hlookup'. simpl in Hlookup'.
        unfold term_subst_update.
        destruct (Nat.eqb y x) eqn:E.
        -- apply Nat.eqb_eq in E. subst y. rewrite Nat.eqb_refl.
           inversion Hlookup'; subst U.
           apply T_Var.
           ++ unfold update. simpl. rewrite Nat.eqb_refl. reflexivity.
           ++ eapply wf_ty_instantiate; eauto.
        -- apply Nat.eqb_neq in E.
           rewrite (proj2 (Nat.eqb_neq x y)) by congruence.
           eapply has_type_weaken_context.
           ++ eapply Hgamma_ty. exact Hlookup'.
           ++ apply context_included_update_fresh. exact HxGamma'.
  - eapply T_App.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
  - apply T_TAbs with
      (L ++ Delta ++ Delta' ++ ftv_tm body ++ fv_ty T).
    intros X Hfresh. repeat rewrite in_app_iff in Hfresh.
    assert (HXL : ~ In X L) by intuition.
    assert (HXDelta : ~ In X Delta) by intuition.
    assert (HXDelta' : ~ In X Delta') by intuition.
    assert (HXbody : ~ In X (ftv_tm body)) by intuition.
    assert (HXT : ~ In X (fv_ty T)) by intuition.
    set (theta' := type_subst_update theta X (Ty_FVar X)).
    assert (Hctx' : context_wf (X :: Delta) Gamma).
    { eapply context_wf_weaken_type; [exact Hctx |].
      unfold ty_context_included. simpl. auto. }
    assert (Htheta_wf' : type_substitution_wf
      (X :: Delta) (X :: Delta') theta').
    { unfold theta', type_substitution_wf, type_subst_update.
      intros Y [E | Hin].
      - subst Y. rewrite Nat.eqb_refl. apply WF_Var. simpl. auto.
      - assert (Hneq : X <> Y) by (intro; subst; contradiction).
        rewrite (proj2 (Nat.eqb_neq X Y)) by assumption.
        eapply wf_ty_weaken.
        + apply Htheta_wf. exact Hin.
        + unfold ty_context_included. simpl. auto. }
    assert (Hgamma_ty' : term_substitution_typed
      Gamma (X :: Delta') Gamma' theta' gamma).
    { unfold term_substitution_typed in *. intros x U Hlookup.
      assert (HwfU : wf_ty Delta U) by (eapply Hctx; eauto).
      assert (HXU : ~ In X (fv_ty U)).
      { intro Hin. apply HXDelta. eapply wf_ty_fv; eauto. }
      unfold theta'.
      rewrite instantiate_ty_update_irrelevant by exact HXU.
      eapply has_type_weaken_type.
      - eapply Hgamma_ty. exact Hlookup.
      - unfold ty_context_included. simpl. auto. }
    pose proof (IHbody X HXL Hctx' (X :: Delta') Gamma'
      theta' gamma) as IH.
    rewrite <- (instantiate_open_ty body theta gamma X (Ty_FVar X));
      try assumption; try apply lc_ty_fvar.
    rewrite <- (instantiate_ty_open T theta X (Ty_FVar X));
      try assumption; try apply lc_ty_fvar.
    assert (Htheta' : type_substitution_closed theta').
    { unfold theta'. apply type_subst_update_closed; auto. apply lc_ty_fvar. }
    exact (IH Htheta' Hgamma Htheta_wf' Hgamma_ty').
  - rewrite instantiate_ty_open_commute by exact Htheta.
    eapply T_TApp.
    + apply IHt; assumption.
    + eapply wf_ty_instantiate; eauto.
  - apply T_True.
  - apply T_False.
  - eapply T_If; [apply IHt1 | apply IHt2 | apply IHt3]; assumption.
  - apply T_Zero.
  - apply T_Succ. apply IHn; assumption.
  - eapply T_Rec.
    + apply IHn; assumption.
    + apply IHb; assumption.
    + apply IHs; assumption.  - eapply T_Choice; [apply IHt1 | apply IHt2]; assumption.
Qed.

Lemma wf_ty_open_all : forall Delta T U,
  wf_ty Delta (Ty_All T) -> wf_ty Delta U -> wf_ty Delta (open_ty T U).
Proof.
  intros Delta T U Hall HU.
  inversion Hall as [| |L Delta0 body Hbody | |]; subst.
  set (X := fresh (L ++ Delta ++ fv_ty T)).
  assert (HX : ~ In X (L ++ Delta ++ fv_ty T)).
  { subst X. apply fresh_notin. }
  repeat rewrite in_app_iff in HX.
  assert (HXL : ~ In X L) by intuition.
  assert (HXDelta : ~ In X Delta) by intuition.
  assert (HXT : ~ In X (fv_ty T)) by intuition.
  pose proof (Hbody X HXL) as Hopened.
  set (theta := type_subst_update identity_type_substitution X U).
  assert (Htheta_closed : type_substitution_closed theta).
  { unfold theta. apply type_subst_update_closed.
    - apply identity_type_substitution_closed.
    - apply wf_ty_lc with Delta. exact HU. }
  assert (Htheta_wf : type_substitution_wf (X :: Delta) Delta theta).
  { unfold theta, type_substitution_wf, type_subst_update,
      identity_type_substitution.
    intros Y [E | Hin].
    - subst Y. rewrite Nat.eqb_refl. exact HU.
    - assert (Hneq : X <> Y) by (intro; subst; contradiction).
      rewrite (proj2 (Nat.eqb_neq X Y)) by assumption.
      apply WF_Var. exact Hin. }
  pose proof (wf_ty_instantiate _ _ Hopened Delta theta Htheta_wf) as Hinst.
  assert (Hopen : instantiate_ty theta (open_ty T (Ty_FVar X)) = open_ty T U).
  { unfold theta.
    rewrite instantiate_ty_open_local.
    - rewrite instantiate_ty_identity. reflexivity.
    - exact HXT.
    - intros Y Hin. apply lc_ty_fvar.
    - apply wf_ty_lc with Delta. exact HU. }
  rewrite Hopen in Hinst. exact Hinst.
Qed.

Lemma typing_type_wf : forall Delta Gamma t T,
  has_type Delta Gamma t T -> wf_ty Delta T.
Proof.
  intros Delta Gamma t T Hty. induction Hty.
  - exact H0.
  - apply WF_Arrow; [exact H |].
    set (x := fresh L). apply H1 with x. subst x. apply fresh_notin.
  - inversion IHHty1. assumption.
  - apply WF_All with L. intros X Hfresh. apply H0. exact Hfresh.
  - eapply wf_ty_open_all; eauto.
  - apply WF_Bool.
  - apply WF_Bool.
  - exact IHHty2.
  - apply WF_Nat.
  - apply WF_Nat.
  - exact IHHty2.
  - exact IHHty1.
Qed.

End CombinedCoreTyping.

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Module CombinedCoreMetatheory.
Import SystemFNormalizationIfNondeterminismRecursionEasyTask.
Import CombinedCoreTyping.

Lemma canonical_arrow : forall v T1 T2,
  value v ->
  has_type [] empty v (Ty_Arrow T1 T2) ->
  exists U body, v = tm_abs U body.
Proof.
  intros v T1 T2 Hv Hty. inversion Hv; subst.
  - exists T, t. reflexivity.
  - inversion Hty.
  - inversion Hty.
  - inversion Hty.
  - match goal with Hn : numeric_value _ |- _ => induction Hn; inversion Hty end.
Qed.

Lemma canonical_all : forall v T,
  value v ->
  has_type [] empty v (Ty_All T) ->
  exists body, v = tm_tabs body.
Proof.
  intros v T Hv Hty. inversion Hv; subst.
  - inversion Hty.
  - exists t. reflexivity.
  - inversion Hty.
  - inversion Hty.
  - match goal with Hn : numeric_value _ |- _ => induction Hn; inversion Hty end.
Qed.

Lemma canonical_nat : forall v,
  value v ->
  has_type [] empty v Ty_Nat ->
  numeric_value v.
Proof.
  intros v Hv Hty. inversion Hv; subst.
  - inversion Hty.
  - inversion Hty.
  - inversion Hty.
  - inversion Hty.
  - assumption.
Qed.

Lemma canonical_bool : forall v,
  value v ->
  has_type [] empty v Ty_Bool ->
  v = tm_true \/ v = tm_false.
Proof.
  intros v Hv Hty. inversion Hv; subst; try solve [inversion Hty].
  - left. reflexivity.
  - right. reflexivity.
  - match goal with Hn : numeric_value _ |- _ => induction Hn; inversion Hty end.
Qed.

Lemma term_beta_typing : forall L T1 body T2 v,
  wf_ty [] T1 ->
  (forall x, ~ In x L ->
    has_type [] (update empty x T1)
      (open_tm body (tm_fvar x)) T2) ->
  has_type [] empty v T1 ->
  has_type [] empty (open_tm body v) T2.
Proof.
  intros L T1 body T2 v HT1 Hbody Hv.
  set (x := fresh (L ++ fv_tm body)).
  assert (Hx : ~ In x (L ++ fv_tm body)).
  { subst x. apply fresh_notin. }
  rewrite in_app_iff in Hx.
  assert (HxL : ~ In x L) by intuition.
  assert (Hxfv : ~ In x (fv_tm body)) by intuition.
  pose proof (Hbody x HxL) as Hopened.
  set (gamma := term_subst_update identity_term_substitution x v).
  assert (Hctx : context_wf [] (update empty x T1)).
  { intros y U Hlookup. unfold update, empty in Hlookup. simpl in Hlookup.
    destruct (Nat.eqb y x) eqn:E; try discriminate.
    inversion Hlookup; subst. exact HT1. }
  assert (Htheta_wf :
    type_substitution_wf [] [] identity_type_substitution).
  { intros X Hin. contradiction. }
  assert (Hgamma_typed : term_substitution_typed
      (update empty x T1) [] empty identity_type_substitution gamma).
  { intros y U Hlookup. unfold update, empty in Hlookup. simpl in Hlookup.
    destruct (Nat.eqb y x) eqn:E; try discriminate.
    apply Nat.eqb_eq in E. subst y. inversion Hlookup; subst U.
    unfold gamma, term_subst_update. rewrite Nat.eqb_refl.
    rewrite instantiate_ty_identity. exact Hv. }
  pose proof (has_type_instantiate _ _ _ _ Hopened Hctx
    [] empty identity_type_substitution gamma
    identity_type_substitution_closed
    (term_subst_update_closed identity_term_substitution x v
      identity_term_substitution_closed (typing_lc _ _ _ _ Hv))
    Htheta_wf Hgamma_typed) as Hinst.
  unfold gamma in Hinst.
  rewrite (instantiate_open_tm body identity_type_substitution
      identity_term_substitution x v Hxfv
      identity_type_substitution_closed identity_term_substitution_closed
      (typing_lc _ _ _ _ Hv)) in Hinst.
  rewrite instantiate_identity, instantiate_ty_identity in Hinst.
  exact Hinst.
Qed.

Lemma type_beta_typing : forall L body T U,
  (forall X, ~ In X L ->
    has_type [X] empty
      (open_tm_ty body (Ty_FVar X))
      (open_ty T (Ty_FVar X))) ->
  wf_ty [] U ->
  has_type [] empty (open_tm_ty body U) (open_ty T U).
Proof.
  intros L body T U Hbody HU.
  set (X := fresh (L ++ ftv_tm body ++ fv_ty T)).
  assert (HX : ~ In X (L ++ ftv_tm body ++ fv_ty T)).
  { subst X. apply fresh_notin. }
  repeat rewrite in_app_iff in HX.
  assert (HXL : ~ In X L) by intuition.
  assert (HXbody : ~ In X (ftv_tm body)) by intuition.
  assert (HXT : ~ In X (fv_ty T)) by intuition.
  pose proof (Hbody X HXL) as Hopened.
  set (theta := type_subst_update identity_type_substitution X U).
  assert (Htheta_closed : type_substitution_closed theta).
  { unfold theta. apply type_subst_update_closed.
    - exact identity_type_substitution_closed.
    - exact (wf_ty_lc [] U HU). }
  assert (Htheta_wf : type_substitution_wf [X] [] theta).
  { intros Y Hin. simpl in Hin. destruct Hin as [E | Hin]; [|contradiction].
    subst Y. unfold theta, type_subst_update. rewrite Nat.eqb_refl. exact HU. }
  assert (Hctx : context_wf [X] empty).
  { intros y V Hlookup. discriminate. }
  assert (Hgamma_typed : term_substitution_typed
      empty [] empty theta identity_term_substitution).
  { intros y V Hlookup. discriminate. }
  pose proof (has_type_instantiate _ _ _ _ Hopened Hctx
    [] empty theta identity_term_substitution
    Htheta_closed identity_term_substitution_closed
    Htheta_wf Hgamma_typed) as Hinst.
  unfold theta in Hinst.
  rewrite (instantiate_open_ty body identity_type_substitution
      identity_term_substitution X U HXbody
      identity_type_substitution_closed identity_term_substitution_closed
      (wf_ty_lc [] U HU)) in Hinst.
  rewrite (instantiate_ty_open_local T identity_type_substitution X U HXT) in Hinst.
  - rewrite instantiate_identity, instantiate_ty_identity in Hinst. exact Hinst.
  - intros Y Hin. apply lc_ty_fvar.
  - exact (wf_ty_lc [] U HU).
Qed.

Theorem core_progress : forall t T,
  has_type [] empty t T ->
  value t \/ exists t', t --> t'.
Proof.
  intros t T Hty.
  remember (@nil atom) as Delta eqn:EDelta.
  remember empty as Gamma eqn:EGamma.
  induction Hty; subst.
  - discriminate H.
  - left. apply v_abs. eapply typing_lc. eapply T_Abs; eauto.
  - right.
    destruct IHHty1 as [Hv1 | [t1' Hs1]]; try reflexivity.
    + destruct IHHty2 as [Hv2 | [t2' Hs2]]; try reflexivity.
      * destruct (canonical_arrow _ _ _ Hv1 Hty1) as [U [body E]].
        subst t1. exists (open_tm body t2). apply ST_AppAbs.
        -- eapply typing_lc. exact Hty1.
        -- exact Hv2.
      * exists (tm_app t1 t2'). apply ST_App2; assumption.
    + exists (tm_app t1' t2). apply ST_App1.
      * exact Hs1.
      * eapply typing_lc. exact Hty2.
  - left. apply v_tabs. eapply typing_lc. eapply T_TAbs; eauto.
  - right.
    destruct IHHty as [Hv | [t' Hs]]; try reflexivity.
    + destruct (canonical_all _ _ Hv Hty) as [body E]. subst t.
      exists (open_tm_ty body U). apply ST_TAppTabs.
      * eapply typing_lc. exact Hty.
      * eapply wf_ty_lc. eassumption.
    + exists (tm_tapp t' U). apply ST_TApp.
      * exact Hs.
      * eapply wf_ty_lc. eassumption.
  - left. apply v_true.
  - left. apply v_false.
  - right. destruct IHHty1 as [Hv | [t1' Hstep]]; try reflexivity.
    + destruct (canonical_bool _ Hv Hty1) as [-> | ->].
      * exists t2. apply ST_IfTrue; eapply typing_lc; eauto.
      * exists t3. apply ST_IfFalse; eapply typing_lc; eauto.
    + exists (tm_if t1' t2 t3). apply ST_If.
      * exact Hstep.
      * eapply typing_lc. exact Hty2.
      * eapply typing_lc. exact Hty3.
  - left. apply v_nat. apply nv_zero.
  - destruct IHHty as [Hv | [n' Hstep]]; try reflexivity.
    + left. apply v_nat. apply nv_succ. eapply canonical_nat; eauto.
    + right. exists (tm_succ n'). apply ST_Succ. exact Hstep.
  - right. destruct IHHty1 as [Hvn | [n' Hnstep]]; try reflexivity.
    + destruct IHHty2 as [Hvb | [b' Hbstep]]; try reflexivity.
      * destruct IHHty3 as [Hvs | [s' Hsstep]]; try reflexivity.
        -- pose proof (canonical_nat _ Hvn Hty1) as Hnumeric.
           inversion Hnumeric; subst.
           ++ exists b. apply ST_RecZero; assumption.
           ++ exists (tm_app (tm_app s n0) (tm_natrec n0 b s)).
              apply ST_RecSucc; assumption.
        -- exists (tm_natrec n b s'). apply ST_RecStep.
           ++ eapply canonical_nat; eauto.
           ++ exact Hvb.
           ++ exact Hsstep.
      * exists (tm_natrec n b' s). apply ST_RecBase.
        -- eapply canonical_nat; eauto.
        -- exact Hbstep.
        -- eapply typing_lc. exact Hty3.
    + exists (tm_natrec n' b s). apply ST_RecArg.
      * exact Hnstep.
      * eapply typing_lc. exact Hty2.
      * eapply typing_lc. exact Hty3.
  - right. exists t1. apply ST_ChoiceLeft;
      eapply typing_lc; eauto.
Qed.

Theorem core_preservation : forall t t' T,
  has_type [] empty t T ->
  t --> t' ->
  has_type [] empty t' T.
Proof.
  intros t t' T Hty Hstep.
  remember (@nil atom) as Delta eqn:EDelta.
  remember empty as Gamma eqn:EGamma.
  generalize dependent t'.
  induction Hty; intros t' Hstep; subst; inversion Hstep; subst.
  - inversion Hty1; subst. eapply term_beta_typing; eauto.
  - eapply T_App; eauto.
  - eapply T_App; eauto.
  - inversion Hty; subst. eapply type_beta_typing; eauto.
  - eapply T_TApp; eauto.
  - exact Hty2.
  - exact Hty3.
  - eapply T_If; eauto.
  - eapply T_Succ; eauto.
  - eapply T_Rec; eauto.
  - eapply T_Rec; eauto.
  - eapply T_Rec; eauto.
  - exact Hty2.
  - inversion Hty1; subst. eapply T_App.
    + eapply T_App; eauto.
    + eapply T_Rec; eauto.
  - exact Hty1.
  - exact Hty2.
Qed.

End CombinedCoreMetatheory.

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.

Module CombinedRefinementTyping.
Import SystemFNormalizationIfNondeterminismRecursionEasyTask.
Import CombinedCoreTyping.
Import ListNotations.

Inductive predicate : Type :=
  | Pred_True : predicate
  | Pred_False : predicate
  | Pred_Eq : tm -> tm -> predicate
  | Pred_And : predicate -> predicate -> predicate.

Inductive predicates : Type :=
  | PEmpty : predicates
  | PCons : predicate -> predicates -> predicates.

Inductive rty : Type :=
  | R_Refine : ty -> predicates -> rty
  | R_Func : rty -> rty -> rty
  | R_Exists : rty -> rty -> rty
  | R_Poly : rty -> rty.

Fixpoint erase (R : rty) : ty :=
  match R with
  | R_Refine T _ => T
  | R_Func R1 R2 => Ty_Arrow (erase R1) (erase R2)
  | R_Exists _ R2 => erase R2
  | R_Poly R => Ty_All (erase R)
  end.

Fixpoint open_pred_tm_rec (k : nat) (u : tm) (p : predicate) : predicate :=
  match p with
  | Pred_True => Pred_True
  | Pred_False => Pred_False
  | Pred_Eq t1 t2 =>
      Pred_Eq (open_tm_rec k u t1) (open_tm_rec k u t2)
  | Pred_And p1 p2 =>
      Pred_And (open_pred_tm_rec k u p1) (open_pred_tm_rec k u p2)
  end.

Fixpoint open_preds_tm_rec (k : nat) (u : tm) (ps : predicates) : predicates :=
  match ps with
  | PEmpty => PEmpty
  | PCons p ps' =>
      PCons (open_pred_tm_rec k u p) (open_preds_tm_rec k u ps')
  end.

Fixpoint open_rty_tm_rec (k : nat) (u : tm) (R : rty) : rty :=
  match R with
  | R_Refine T ps => R_Refine T (open_preds_tm_rec (S k) u ps)
  | R_Func R1 R2 =>
      R_Func (open_rty_tm_rec k u R1) (open_rty_tm_rec (S k) u R2)
  | R_Exists R1 R2 =>
      R_Exists (open_rty_tm_rec k u R1) (open_rty_tm_rec (S k) u R2)
  | R_Poly R1 => R_Poly (open_rty_tm_rec k u R1)
  end.

Definition open_pred_tm (p : predicate) (u : tm) : predicate :=
  open_pred_tm_rec 0 u p.

Definition open_preds_tm (ps : predicates) (u : tm) : predicates :=
  open_preds_tm_rec 0 u ps.

Definition open_rty_tm (R : rty) (u : tm) : rty :=
  open_rty_tm_rec 0 u R.

Fixpoint open_pred_ty_rec (k : nat) (U : ty) (p : predicate) : predicate :=
  match p with
  | Pred_True => Pred_True
  | Pred_False => Pred_False
  | Pred_Eq t1 t2 =>
      Pred_Eq (open_tm_ty_rec k U t1) (open_tm_ty_rec k U t2)
  | Pred_And p1 p2 =>
      Pred_And (open_pred_ty_rec k U p1) (open_pred_ty_rec k U p2)
  end.

Fixpoint open_preds_ty_rec (k : nat) (U : ty) (ps : predicates) : predicates :=
  match ps with
  | PEmpty => PEmpty
  | PCons p ps' =>
      PCons (open_pred_ty_rec k U p) (open_preds_ty_rec k U ps')
  end.

Fixpoint open_rty_ty_rec (k : nat) (U : ty) (R : rty) : rty :=
  match R with
  | R_Refine T ps =>
      R_Refine (open_ty_rec k U T) (open_preds_ty_rec k U ps)
  | R_Func R1 R2 =>
      R_Func (open_rty_ty_rec k U R1) (open_rty_ty_rec k U R2)
  | R_Exists R1 R2 =>
      R_Exists (open_rty_ty_rec k U R1) (open_rty_ty_rec k U R2)
  | R_Poly R1 => R_Poly (open_rty_ty_rec (S k) U R1)
  end.

Definition open_rty_ty (R : rty) (U : ty) : rty :=
  open_rty_ty_rec 0 U R.

Fixpoint pred_subst (x : atom) (s : tm) (p : predicate) : predicate :=
  match p with
  | Pred_True => Pred_True
  | Pred_False => Pred_False
  | Pred_Eq t1 t2 => Pred_Eq (tm_subst x s t1) (tm_subst x s t2)
  | Pred_And p1 p2 => Pred_And (pred_subst x s p1) (pred_subst x s p2)
  end.

Fixpoint preds_subst (x : atom) (s : tm) (ps : predicates) : predicates :=
  match ps with
  | PEmpty => PEmpty
  | PCons p ps' => PCons (pred_subst x s p) (preds_subst x s ps')
  end.

Fixpoint rty_subst (x : atom) (s : tm) (R : rty) : rty :=
  match R with
  | R_Refine T ps => R_Refine T (preds_subst x s ps)
  | R_Func R1 R2 => R_Func (rty_subst x s R1) (rty_subst x s R2)
  | R_Exists R1 R2 => R_Exists (rty_subst x s R1) (rty_subst x s R2)
  | R_Poly R1 => R_Poly (rty_subst x s R1)
  end.

Fixpoint pred_ty_subst (X : atom) (U : ty) (p : predicate) : predicate :=
  match p with
  | Pred_True => Pred_True
  | Pred_False => Pred_False
  | Pred_Eq t1 t2 =>
      Pred_Eq (tm_ty_subst X U t1) (tm_ty_subst X U t2)
  | Pred_And p1 p2 =>
      Pred_And (pred_ty_subst X U p1) (pred_ty_subst X U p2)
  end.

Fixpoint preds_ty_subst (X : atom) (U : ty) (ps : predicates) : predicates :=
  match ps with
  | PEmpty => PEmpty
  | PCons p ps' =>
      PCons (pred_ty_subst X U p) (preds_ty_subst X U ps')
  end.

Fixpoint rty_ty_subst (X : atom) (U : ty) (R : rty) : rty :=
  match R with
  | R_Refine T ps => R_Refine (ty_subst X U T) (preds_ty_subst X U ps)
  | R_Func R1 R2 =>
      R_Func (rty_ty_subst X U R1) (rty_ty_subst X U R2)
  | R_Exists R1 R2 =>
      R_Exists (rty_ty_subst X U R1) (rty_ty_subst X U R2)
  | R_Poly R1 => R_Poly (rty_ty_subst X U R1)
  end.

Inductive lc_pred_at : nat -> nat -> predicate -> Prop :=
  | LCP_True : forall K k, lc_pred_at K k Pred_True
  | LCP_False : forall K k, lc_pred_at K k Pred_False
  | LCP_Eq : forall K k t1 t2,
      lc_tm_at K k t1 ->
      lc_tm_at K k t2 ->
      lc_pred_at K k (Pred_Eq t1 t2)
  | LCP_And : forall K k p1 p2,
      lc_pred_at K k p1 ->
      lc_pred_at K k p2 ->
      lc_pred_at K k (Pred_And p1 p2).

Inductive lc_preds_at : nat -> nat -> predicates -> Prop :=
  | LCPS_Empty : forall K k, lc_preds_at K k PEmpty
  | LCPS_Cons : forall K k p ps,
      lc_pred_at K k p ->
      lc_preds_at K k ps ->
      lc_preds_at K k (PCons p ps).

Inductive lc_rty_at : nat -> nat -> rty -> Prop :=
  | LCR_Refine : forall K k T ps,
      lc_ty_at K T ->
      lc_preds_at K (S k) ps ->
      lc_rty_at K k (R_Refine T ps)
  | LCR_Func : forall K k R1 R2,
      lc_rty_at K k R1 ->
      lc_rty_at K (S k) R2 ->
      lc_rty_at K k (R_Func R1 R2)
  | LCR_Exists : forall K k R1 R2,
      lc_rty_at K k R1 ->
      lc_rty_at K (S k) R2 ->
      lc_rty_at K k (R_Exists R1 R2)
  | LCR_Poly : forall K k R,
      lc_rty_at (S K) k R ->
      lc_rty_at K k (R_Poly R).

Definition locally_closed_rty (R : rty) : Prop := lc_rty_at 0 0 R.

Lemma open_pred_tm_rec_lc_at : forall K k p u,
  lc_pred_at K k p -> open_pred_tm_rec k u p = p.
Proof.
  intros K k p u Hlc. induction Hlc; simpl; try reflexivity.
  - rewrite (open_tm_rec_lc_at t1 K k u H),
      (open_tm_rec_lc_at t2 K k u H0). reflexivity.
  - rewrite IHHlc1, IHHlc2. reflexivity.
Qed.

Lemma open_preds_tm_rec_lc_at : forall K k ps u,
  lc_preds_at K k ps -> open_preds_tm_rec k u ps = ps.
Proof.
  intros K k ps u Hlc. induction Hlc; simpl; try reflexivity.
  rewrite (open_pred_tm_rec_lc_at K k p u H), IHHlc. reflexivity.
Qed.

Lemma open_rty_tm_rec_lc_at : forall K k R u,
  lc_rty_at K k R -> open_rty_tm_rec k u R = R.
Proof.
  intros K k R u Hlc. induction Hlc; simpl.
  - rewrite (open_preds_tm_rec_lc_at K (S k) ps u H0). reflexivity.
  - rewrite IHHlc1, IHHlc2. reflexivity.
  - rewrite IHHlc1, IHHlc2. reflexivity.
  - rewrite IHHlc. reflexivity.
Qed.

Lemma open_rty_tm_lc : forall R u,
  locally_closed_rty R -> open_rty_tm R u = R.
Proof.
  intros R u Hlc. unfold open_rty_tm.
  eapply open_rty_tm_rec_lc_at. exact Hlc.
Qed.

Lemma lc_pred_at_term_monotone : forall K k k' p,
  lc_pred_at K k p -> k <= k' -> lc_pred_at K k' p.
Proof.
  intros K k k' p Hlc Hle. induction Hlc.
  - apply LCP_True.
  - apply LCP_False.
  - apply LCP_Eq; eapply lc_tm_at_monotone; eauto; lia.
  - apply LCP_And; auto.
Qed.

Lemma lc_preds_at_term_monotone : forall K k k' ps,
  lc_preds_at K k ps -> k <= k' -> lc_preds_at K k' ps.
Proof.
  intros K k k' ps Hlc Hle. induction Hlc.
  - apply LCPS_Empty.
  - apply LCPS_Cons.
    + eapply lc_pred_at_term_monotone; eauto.
    + apply IHHlc. exact Hle.
Qed.

Lemma lc_rty_at_term_monotone : forall K k k' R,
  lc_rty_at K k R -> k <= k' -> lc_rty_at K k' R.
Proof.
  intros K k k' R Hlc. generalize dependent k'. induction Hlc; intros k' Hle.
  - apply LCR_Refine; [exact H |].
    eapply lc_preds_at_term_monotone; eauto; lia.
  - apply LCR_Func.
    + apply IHHlc1. exact Hle.
    + apply IHHlc2. lia.
  - apply LCR_Exists.
    + apply IHHlc1. exact Hle.
    + apply IHHlc2. lia.
  - apply LCR_Poly. apply IHHlc. exact Hle.
Qed.

Definition rcontext := list (atom * rty).

Fixpoint lookup_rcontext (x : atom) (RGamma : rcontext) : option rty :=
  match RGamma with
  | [] => None
  | (y, R) :: RGamma' =>
      if Nat.eqb x y then Some R else lookup_rcontext x RGamma'
  end.

Definition empty_rcontext : rcontext := [].
Definition update_rcontext (RGamma : rcontext) (x : atom) (R : rty) : rcontext :=
  (x, R) :: RGamma.

Fixpoint erase_context (RGamma : rcontext) : context :=
  match RGamma with
  | [] => empty
  | (x, R) :: RGamma' => update (erase_context RGamma') x (erase R)
  end.

Inductive predicate_wf : ty_context -> context -> predicate -> Prop :=
  | PWF_True : forall Delta Gamma,
      predicate_wf Delta Gamma Pred_True
  | PWF_False : forall Delta Gamma,
      predicate_wf Delta Gamma Pred_False
  | PWF_Eq : forall Delta Gamma t1 t2 T,
      has_type Delta Gamma t1 T ->
      has_type Delta Gamma t2 T ->
      predicate_wf Delta Gamma (Pred_Eq t1 t2)
  | PWF_And : forall Delta Gamma p1 p2,
      predicate_wf Delta Gamma p1 ->
      predicate_wf Delta Gamma p2 ->
      predicate_wf Delta Gamma (Pred_And p1 p2).

Inductive predicates_wf : ty_context -> context -> predicates -> Prop :=
  | PSWF_Empty : forall Delta Gamma,
      predicates_wf Delta Gamma PEmpty
  | PSWF_Cons : forall Delta Gamma p ps,
      predicate_wf Delta Gamma p ->
      predicates_wf Delta Gamma ps ->
      predicates_wf Delta Gamma (PCons p ps).

Inductive wf_rty : ty_context -> rcontext -> rty -> Prop :=

  | RWF_Refine : forall (L : list atom) Delta RGamma T ps,
      wf_ty Delta T ->
      (forall x, ~ In x L ->
        predicates_wf Delta
          (update (erase_context RGamma) x T)
          (open_preds_tm ps (tm_fvar x))) ->
      wf_rty Delta RGamma (R_Refine T ps)

  | RWF_Func : forall (L : list atom) Delta RGamma R1 R2,
      wf_rty Delta RGamma R1 ->
      (forall x, ~ In x L ->
        wf_rty Delta (update_rcontext RGamma x R1)
          (open_rty_tm R2 (tm_fvar x))) ->
      wf_rty Delta RGamma (R_Func R1 R2)

  | RWF_Exists : forall (L : list atom) Delta RGamma R1 R2,
      wf_rty Delta RGamma R1 ->
      (forall x, ~ In x L ->
        wf_rty Delta (update_rcontext RGamma x R1)
          (open_rty_tm R2 (tm_fvar x))) ->
      wf_rty Delta RGamma (R_Exists R1 R2)
  | RWF_Poly : forall (L : list atom) Delta RGamma R,
      (forall X, ~ In X L ->
        wf_rty (X :: Delta) RGamma (open_rty_ty R (Ty_FVar X))) ->
      wf_rty Delta RGamma (R_Poly R).

Inductive entails : ty_context -> rcontext -> predicates -> predicates -> Prop :=
  | Entails_Refl : forall Delta RGamma ps,
      entails Delta RGamma ps ps
  | Entails_True : forall Delta RGamma ps,
      entails Delta RGamma ps PEmpty
  | Entails_Trans : forall Delta RGamma ps qs rs,
      entails Delta RGamma ps qs ->
      entails Delta RGamma qs rs ->
      entails Delta RGamma ps rs
  | Entails_Head : forall Delta RGamma p ps,
      entails Delta RGamma (PCons p ps) (PCons p PEmpty)
  | Entails_Tail : forall Delta RGamma p ps,
      entails Delta RGamma (PCons p ps) ps
  | Entails_Cons : forall Delta RGamma ps p qs,
      entails Delta RGamma ps (PCons p PEmpty) ->
      entails Delta RGamma ps qs ->
      entails Delta RGamma ps (PCons p qs)

  | Entails_False : forall Delta RGamma ps qs,
      entails Delta RGamma (PCons Pred_False ps) qs.

Inductive predicate_multistep : tm -> tm -> Prop :=
  | PMS_Refl : forall t,
      predicate_multistep t t
  | PMS_Step : forall t1 t2 t3,
      t1 --> t2 ->
      predicate_multistep t2 t3 ->
      predicate_multistep t1 t3.

Inductive predicate_holds : predicate -> Prop :=
  | PH_True : predicate_holds Pred_True
  | PH_Eq : forall t1 t2 v,
      predicate_multistep t1 v ->
      predicate_multistep t2 v ->
      value v ->
      predicate_holds (Pred_Eq t1 t2)
  | PH_And : forall p1 p2,
      predicate_holds p1 ->
      predicate_holds p2 ->
      predicate_holds (Pred_And p1 p2).

Inductive predicates_hold : predicates -> Prop :=
  | PHS_Empty : predicates_hold PEmpty
  | PHS_Cons : forall p ps,
      predicate_holds p ->
      predicates_hold ps ->
      predicates_hold (PCons p ps).

Inductive has_rtype : ty_context -> rcontext -> tm -> rty -> Prop :=
  | RT_Var : forall Delta RGamma x R,
      lookup_rcontext x RGamma = Some R ->
      wf_rty Delta RGamma R ->
      has_rtype Delta RGamma (tm_fvar x) R

  | RT_Abs : forall (L : list atom) Delta RGamma R1 body R2,
      wf_rty Delta RGamma R1 ->
      (forall x, ~ In x L ->
        has_rtype Delta (update_rcontext RGamma x R1)
          (open_tm body (tm_fvar x))
          (open_rty_tm R2 (tm_fvar x))) ->
      has_rtype Delta RGamma (tm_abs (erase R1) body) (R_Func R1 R2)
  | RT_App : forall Delta RGamma t1 t2 R1 R2,
      has_rtype Delta RGamma t1 (R_Func R1 R2) ->
      has_rtype Delta RGamma t2 R1 ->
      has_rtype Delta RGamma (tm_app t1 t2) (R_Exists R1 R2)
  | RT_TAbs : forall (L : list atom) Delta RGamma body R,
      (forall X, ~ In X L ->
        has_rtype (X :: Delta) RGamma
          (open_tm_ty body (Ty_FVar X))
          (open_rty_ty R (Ty_FVar X))) ->
      has_rtype Delta RGamma (tm_tabs body) (R_Poly R)
  | RT_TApp : forall Delta RGamma t R U,
      has_rtype Delta RGamma t (R_Poly R) ->
      wf_ty Delta U ->
      has_rtype Delta RGamma (tm_tapp t U) (open_rty_ty R U)
  | RT_If : forall Delta RGamma t1 t2 t3 R,
      has_rtype Delta RGamma t1 (R_Refine Ty_Bool PEmpty) ->
      has_rtype Delta RGamma t2 R ->
      has_rtype Delta RGamma t3 R ->
      has_rtype Delta RGamma (tm_if t1 t2 t3) R
  | RT_Rec : forall Delta RGamma n b s R,
      locally_closed_rty R ->
      has_rtype Delta RGamma n (R_Refine Ty_Nat PEmpty) ->
      has_rtype Delta RGamma b R ->
      has_rtype Delta RGamma s
        (R_Func (R_Refine Ty_Nat PEmpty) (R_Func R R)) ->
      has_rtype Delta RGamma (tm_natrec n b s) R

  | RT_Choice : forall Delta RGamma t1 t2 R,
      has_rtype Delta RGamma t1 R ->
      has_rtype Delta RGamma t2 R ->
      has_rtype Delta RGamma (tm_choice t1 t2) R
  | RT_Core : forall Delta RGamma t T,
      has_type Delta (erase_context RGamma) t T ->
      has_rtype Delta RGamma t (R_Refine T PEmpty)

  | RT_RefineValue : forall Delta RGamma v T ps,
      has_type Delta (erase_context RGamma) v T ->
      value v ->
      wf_rty Delta RGamma (R_Refine T ps) ->
      predicates_hold (open_preds_tm ps v) ->
      has_rtype Delta RGamma v (R_Refine T ps)

  | RT_Sub : forall Delta RGamma t R S,
      has_rtype Delta RGamma t R ->
      wf_rty Delta RGamma S ->
      subtype Delta RGamma R S ->
      has_rtype Delta RGamma t S

with subtype : ty_context -> rcontext -> rty -> rty -> Prop :=
  | S_Refl : forall Delta RGamma R,
      subtype Delta RGamma R R
  | S_Refine : forall (L : list atom) Delta RGamma T ps qs,
      (forall x, ~ In x L ->
        entails Delta
          (update_rcontext RGamma x (R_Refine T PEmpty))
          (open_preds_tm ps (tm_fvar x))
          (open_preds_tm qs (tm_fvar x))) ->
      subtype Delta RGamma (R_Refine T ps) (R_Refine T qs)
  | S_Func : forall (L : list atom) Delta RGamma R1 R2 S1 S2,
      subtype Delta RGamma S1 R1 ->
      (forall x, ~ In x L ->
        subtype Delta (update_rcontext RGamma x S1)
          (open_rty_tm R2 (tm_fvar x))
          (open_rty_tm S2 (tm_fvar x))) ->
      subtype Delta RGamma (R_Func R1 R2) (R_Func S1 S2)
  | S_Witness : forall Delta RGamma v R1 R2 S,
      value v ->
      has_rtype Delta RGamma v R1 ->
      subtype Delta RGamma S (open_rty_tm R2 v) ->
      subtype Delta RGamma S (R_Exists R1 R2)
  | S_Bind : forall (L : list atom) Delta RGamma R1 R2 S,

      wf_rty Delta RGamma R1 ->
      locally_closed_rty S ->
      (forall x, ~ In x L ->
        subtype Delta (update_rcontext RGamma x R1)
          (open_rty_tm R2 (tm_fvar x)) S) ->
      subtype Delta RGamma (R_Exists R1 R2) S
  | S_Poly : forall (L : list atom) Delta RGamma R S,
      (forall X, ~ In X L ->
        subtype (X :: Delta) RGamma
          (open_rty_ty R (Ty_FVar X))
          (open_rty_ty S (Ty_FVar X))) ->
      subtype Delta RGamma (R_Poly R) (R_Poly S)
  | S_Trans : forall Delta RGamma R S U,
      subtype Delta RGamma R S ->
      subtype Delta RGamma S U ->
      subtype Delta RGamma R U.

Lemma erase_open_rty_tm_rec : forall R k u,
  erase (open_rty_tm_rec k u R) = erase R.
Proof.
  induction R; intros; simpl; try rewrite IHR1; try rewrite IHR2;
    try rewrite IHR; reflexivity.
Qed.

Lemma erase_open_rty_tm : forall R u,
  erase (open_rty_tm R u) = erase R.
Proof.
  intros. apply erase_open_rty_tm_rec.
Qed.

Lemma erase_open_rty_ty_rec : forall R k U,
  erase (open_rty_ty_rec k U R) = open_ty_rec k U (erase R).
Proof.
  induction R; intros; simpl.
  - reflexivity.
  - rewrite IHR1, IHR2. reflexivity.
  - rewrite IHR2. reflexivity.
  - rewrite IHR. reflexivity.
Qed.

Lemma erase_open_rty_ty : forall R U,
  erase (open_rty_ty R U) = open_ty (erase R) U.
Proof.
  intros. unfold open_rty_ty, open_ty. apply erase_open_rty_ty_rec.
Qed.

Lemma lookup_erase_context : forall RGamma x R,
  lookup_rcontext x RGamma = Some R ->
  lookup_context x (erase_context RGamma) = Some (erase R).
Proof.
  induction RGamma as [|[y S] RGamma IH]; intros x R Hlookup; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + inversion Hlookup; subst. reflexivity.
    + apply IH. exact Hlookup.
Qed.

Fixpoint close_ty_rec (k : nat) (X : atom) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar Y => if Nat.eqb X Y then Ty_BVar k else Ty_FVar Y
  | Ty_Arrow T1 T2 =>
      Ty_Arrow (close_ty_rec k X T1) (close_ty_rec k X T2)
  | Ty_All T1 => Ty_All (close_ty_rec (S k) X T1)
  | Ty_Bool => Ty_Bool
  | Ty_Nat => Ty_Nat
  end.

Lemma close_open_ty_rec : forall T k X,
  ~ In X (fv_ty T) ->
  close_ty_rec k X (open_ty_rec k (Ty_FVar X) T) = T.
Proof.
  induction T; intros k X Hfresh; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n.
      change ((if Nat.eqb X X then Ty_BVar k else Ty_FVar X) = Ty_BVar k).
      rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - assert (X <> a) by intuition.
    rewrite (proj2 (Nat.eqb_neq X a)) by assumption. reflexivity.
  - rewrite in_app_iff in Hfresh. rewrite IHT1, IHT2; intuition.
  - rewrite IHT by assumption. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma open_ty_fresh_injective : forall T1 T2 X,
  ~ In X (fv_ty T1) ->
  ~ In X (fv_ty T2) ->
  open_ty T1 (Ty_FVar X) = open_ty T2 (Ty_FVar X) ->
  T1 = T2.
Proof.
  intros T1 T2 X H1 H2 E.
  apply (f_equal (close_ty_rec 0 X)) in E.
  unfold open_ty in E.
  rewrite (close_open_ty_rec T1 0 X H1) in E.
  rewrite (close_open_ty_rec T2 0 X H2) in E.
  exact E.
Qed.

Lemma subtype_erases : forall Delta RGamma R S,
  subtype Delta RGamma R S -> erase R = erase S.
Proof.
  fix IH 5.
  intros Delta RGamma R S Hsub.
  destruct Hsub as
    [Delta RGamma R
    |L Delta RGamma T ps qs Hentails
    |L Delta RGamma R1 R2 S1 S2 Hdom Hcod
    |Delta RGamma v R1 R2 S Hv Htyped Hbody
    |L Delta RGamma R1 R2 S HR1 HS Hbody
    |L Delta RGamma R S Hbody
    |Delta RGamma R S U HRS HSU].
  - reflexivity.
  - reflexivity.
  - simpl. f_equal.
    + symmetry. exact (IH _ _ _ _ Hdom).
    + set (x := fresh L).
      assert (Hfresh : ~ In x L) by (subst x; apply fresh_notin).
      pose proof (IH _ _ _ _ (Hcod x Hfresh)) as E.
      rewrite !erase_open_rty_tm in E. exact E.
  - simpl. pose proof (IH _ _ _ _ Hbody) as E.
    rewrite erase_open_rty_tm in E. exact E.
  - simpl. set (x := fresh L).
    assert (Hfresh : ~ In x L) by (subst x; apply fresh_notin).
    pose proof (IH _ _ _ _ (Hbody x Hfresh)) as E.
    rewrite erase_open_rty_tm in E. exact E.
  - simpl. f_equal.
    set (X := fresh (L ++ fv_ty (erase R) ++ fv_ty (erase S))).
    assert (HX : ~ In X (L ++ fv_ty (erase R) ++ fv_ty (erase S))).
    { subst X. apply fresh_notin. }
    repeat rewrite in_app_iff in HX.
    assert (HXL : ~ In X L) by intuition.
    assert (HXR : ~ In X (fv_ty (erase R))) by intuition.
    assert (HXS : ~ In X (fv_ty (erase S))) by intuition.
    pose proof (IH _ _ _ _ (Hbody X HXL)) as E.
    rewrite !erase_open_rty_ty in E.
    eapply open_ty_fresh_injective; eauto.
  - etransitivity.
    + exact (IH _ _ _ _ HRS).
    + exact (IH _ _ _ _ HSU).
Qed.

Lemma wf_rty_erases : forall Delta RGamma R,
  wf_rty Delta RGamma R -> wf_ty Delta (erase R).
Proof.
  fix IH 4.
  intros Delta RGamma R Hwf.
  destruct Hwf as
    [L Delta RGamma T ps HT Hps
    |L Delta RGamma R1 R2 HR1 HR2
    |L Delta RGamma R1 R2 HR1 HR2
    |L Delta RGamma R HR].
  - exact HT.
  - simpl. apply WF_Arrow.
    + exact (IH _ _ _ HR1).
    + set (x := fresh L).
      rewrite <- (erase_open_rty_tm R2 (tm_fvar x)).
      apply IH with (RGamma := update_rcontext RGamma x R1).
      apply HR2. subst x. apply fresh_notin.
  - simpl. set (x := fresh L).
    rewrite <- (erase_open_rty_tm R2 (tm_fvar x)).
    apply IH with (RGamma := update_rcontext RGamma x R1).
    apply HR2. subst x. apply fresh_notin.
  - simpl. apply WF_All with L. intros X Hfresh.
    rewrite <- erase_open_rty_ty.
    apply IH with (RGamma := RGamma).
    apply HR. exact Hfresh.
Qed.

Theorem refinement_typing_erases : forall Delta RGamma t R,
  has_rtype Delta RGamma t R ->
  has_type Delta (erase_context RGamma) t (erase R).
Proof.
  intros Delta RGamma t R Hty. induction Hty.
  - apply T_Var.
    + eapply lookup_erase_context. exact H.
    + exact (wf_rty_erases Delta RGamma R H0).
  - simpl. apply T_Abs with L.
    + exact (wf_rty_erases Delta RGamma R1 H).
    + intros x Hfresh. simpl.
      rewrite <- (erase_open_rty_tm R2 (tm_fvar x)).
      apply H1. exact Hfresh.
  - simpl. eapply T_App; eauto.
  - simpl. apply T_TAbs with L. intros X Hfresh.
    rewrite <- (erase_open_rty_ty R (Ty_FVar X)). apply H0. exact Hfresh.
  - rewrite (erase_open_rty_ty R U). eapply T_TApp; eauto.
  - eapply T_If; eauto.
  - eapply T_Rec; eauto.
  - eapply T_Choice; eauto.
  - exact H.
  - exact H.
  - match goal with
    | Hsub : subtype _ _ _ _ |- _ =>
        pose proof (subtype_erases _ _ _ _ Hsub) as E
    end.
    rewrite <- E. exact IHHty.
Qed.

End CombinedRefinementTyping.

From Stdlib Require Import Arith.PeanoNat Lists.List Lia Program.Wf.
From Equations Require Import Equations.

Module CombinedRefinementDenotations.
Import SystemFNormalizationIfNondeterminismRecursionEasyTask.
Import CombinedCoreTyping.
Import CombinedCoreMetatheory.
Import CombinedRefinementTyping.
Import ListNotations.

Fixpoint fv_pred (p : predicate) : list atom :=
  match p with
  | Pred_True | Pred_False => []
  | Pred_Eq t1 t2 => fv_tm t1 ++ fv_tm t2
  | Pred_And p1 p2 => fv_pred p1 ++ fv_pred p2
  end.

Fixpoint fv_preds (ps : predicates) : list atom :=
  match ps with
  | PEmpty => []
  | PCons p ps' => fv_pred p ++ fv_preds ps'
  end.

Fixpoint fv_rty (R : rty) : list atom :=
  match R with
  | R_Refine _ ps => fv_preds ps
  | R_Func R1 R2 | R_Exists R1 R2 => fv_rty R1 ++ fv_rty R2
  | R_Poly R1 => fv_rty R1
  end.

Fixpoint ftv_pred (p : predicate) : list atom :=
  match p with
  | Pred_True | Pred_False => []
  | Pred_Eq t1 t2 => ftv_tm t1 ++ ftv_tm t2
  | Pred_And p1 p2 => ftv_pred p1 ++ ftv_pred p2
  end.

Fixpoint ftv_preds (ps : predicates) : list atom :=
  match ps with
  | PEmpty => []
  | PCons p ps' => ftv_pred p ++ ftv_preds ps'
  end.

Fixpoint ftv_rty (R : rty) : list atom :=
  match R with
  | R_Refine T ps => fv_ty T ++ ftv_preds ps
  | R_Func R1 R2 | R_Exists R1 R2 => ftv_rty R1 ++ ftv_rty R2
  | R_Poly R1 => ftv_rty R1
  end.

Fixpoint fv_rcontext (RGamma : rcontext) : list atom :=
  match RGamma with
  | [] => []
  | (_, R) :: RGamma' => fv_rty R ++ fv_rcontext RGamma'
  end.

Fixpoint ftv_rcontext (RGamma : rcontext) : list atom :=
  match RGamma with
  | [] => []
  | (_, R) :: RGamma' => ftv_rty R ++ ftv_rcontext RGamma'
  end.

Fixpoint instantiate_pred
    (theta : type_substitution) (gamma : term_substitution)
    (p : predicate) : predicate :=
  match p with
  | Pred_True => Pred_True
  | Pred_False => Pred_False
  | Pred_Eq t1 t2 =>
      Pred_Eq (instantiate theta gamma t1) (instantiate theta gamma t2)
  | Pred_And p1 p2 =>
      Pred_And (instantiate_pred theta gamma p1)
        (instantiate_pred theta gamma p2)
  end.

Fixpoint instantiate_preds
    (theta : type_substitution) (gamma : term_substitution)
    (ps : predicates) : predicates :=
  match ps with
  | PEmpty => PEmpty
  | PCons p ps' =>
      PCons (instantiate_pred theta gamma p)
        (instantiate_preds theta gamma ps')
  end.

Fixpoint instantiate_rty
    (theta : type_substitution) (gamma : term_substitution)
    (R : rty) : rty :=
  match R with
  | R_Refine T ps =>
      R_Refine (instantiate_ty theta T) (instantiate_preds theta gamma ps)
  | R_Func R1 R2 =>
      R_Func (instantiate_rty theta gamma R1)
        (instantiate_rty theta gamma R2)
  | R_Exists R1 R2 =>
      R_Exists (instantiate_rty theta gamma R1)
        (instantiate_rty theta gamma R2)
  | R_Poly R1 => R_Poly (instantiate_rty theta gamma R1)
  end.

Lemma instantiate_pred_lc_at : forall K k p theta gamma,
  lc_pred_at K k p ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  lc_pred_at K k (instantiate_pred theta gamma p).
Proof.
  intros K k p theta gamma Hlc Htheta Hgamma. induction Hlc; simpl.
  - apply LCP_True.
  - apply LCP_False.
  - apply LCP_Eq; eapply instantiate_lc_at; eauto.
  - apply LCP_And; assumption.
Qed.

Lemma instantiate_preds_lc_at : forall K k ps theta gamma,
  lc_preds_at K k ps ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  lc_preds_at K k (instantiate_preds theta gamma ps).
Proof.
  intros K k ps theta gamma Hlc Htheta Hgamma. induction Hlc; simpl.
  - apply LCPS_Empty.
  - apply LCPS_Cons.
    + eapply instantiate_pred_lc_at; eauto.
    + exact IHHlc.
Qed.

Lemma instantiate_rty_lc_at : forall K k R theta gamma,
  lc_rty_at K k R ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  lc_rty_at K k (instantiate_rty theta gamma R).
Proof.
  intros K k R theta gamma Hlc Htheta Hgamma. induction Hlc; simpl.
  - apply LCR_Refine.
    + eapply instantiate_ty_lc_at; eauto.
    + eapply instantiate_preds_lc_at; eauto.
  - apply LCR_Func; assumption.
  - apply LCR_Exists; assumption.
  - apply LCR_Poly; assumption.
Qed.

Lemma instantiate_rty_closed : forall R theta gamma,
  locally_closed_rty R ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_rty (instantiate_rty theta gamma R).
Proof.
  intros. eapply instantiate_rty_lc_at; eauto.
Qed.

Fixpoint rty_size (R : rty) : nat :=
  match R with
  | R_Refine _ _ => 1
  | R_Func R1 R2 => S (rty_size R1 + rty_size R2)
  | R_Exists R1 R2 => S (rty_size R1 + rty_size R2)
  | R_Poly R1 => S (rty_size R1)
  end.

Lemma rty_size_open_tm_rec : forall R k u,
  rty_size (open_rty_tm_rec k u R) = rty_size R.
Proof.
  induction R; intros; simpl; rewrite ?IHR1, ?IHR2, ?IHR; reflexivity.
Qed.

Lemma rty_size_open_tm : forall R u,
  rty_size (open_rty_tm R u) = rty_size R.
Proof.
  intros. apply rty_size_open_tm_rec.
Qed.

Lemma rty_size_open_ty_rec : forall R k U,
  rty_size (open_rty_ty_rec k U R) = rty_size R.
Proof.
  induction R; intros; simpl; rewrite ?IHR1, ?IHR2, ?IHR; reflexivity.
Qed.

Lemma rty_size_open_ty : forall R U,
  rty_size (open_rty_ty R U) = rty_size R.
Proof.
  intros. apply rty_size_open_ty_rec.
Qed.

Lemma erase_instantiate_rty : forall theta gamma R,
  erase (instantiate_rty theta gamma R) = instantiate_ty theta (erase R).
Proof.
  induction R; intros; simpl; rewrite ?IHR1, ?IHR2, ?IHR; reflexivity.
Qed.

Lemma instantiate_pred_open_tm_rec : forall p k theta gamma x u,
  ~ In x (fv_pred p) ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate_pred theta (term_subst_update gamma x u)
    (open_pred_tm_rec k (tm_fvar x) p) =
  open_pred_tm_rec k u (instantiate_pred theta gamma p).
Proof.
  induction p; intros; simpl in *; try reflexivity.
  - rewrite in_app_iff in H.
    rewrite !instantiate_open_tm_rec; intuition.
  - rewrite in_app_iff in H.
    rewrite IHp1, IHp2; intuition.
Qed.

Lemma instantiate_preds_open_tm_rec : forall ps k theta gamma x u,
  ~ In x (fv_preds ps) ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate_preds theta (term_subst_update gamma x u)
    (open_preds_tm_rec k (tm_fvar x) ps) =
  open_preds_tm_rec k u (instantiate_preds theta gamma ps).
Proof.
  induction ps; intros; simpl in *; try reflexivity.
  rewrite in_app_iff in H.
  rewrite instantiate_pred_open_tm_rec, IHps; intuition.
Qed.

Lemma instantiate_rty_open_tm_rec : forall R k theta gamma x u,
  ~ In x (fv_rty R) ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate_rty theta (term_subst_update gamma x u)
    (open_rty_tm_rec k (tm_fvar x) R) =
  open_rty_tm_rec k u (instantiate_rty theta gamma R).
Proof.
  induction R; intros; simpl in *.
  - f_equal. apply instantiate_preds_open_tm_rec; assumption.
  - rewrite in_app_iff in H.
    rewrite IHR1, IHR2; intuition.
  - rewrite in_app_iff in H.
    rewrite IHR1, IHR2; intuition.
  - f_equal. apply IHR; assumption.
Qed.

Lemma instantiate_rty_open_tm : forall R theta gamma x u,
  ~ In x (fv_rty R) ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate_rty theta (term_subst_update gamma x u)
    (open_rty_tm R (tm_fvar x)) =
  open_rty_tm (instantiate_rty theta gamma R) u.
Proof.
  intros. unfold open_rty_tm.
  apply instantiate_rty_open_tm_rec; assumption.
Qed.

Lemma instantiate_pred_open_ty_rec : forall p k theta gamma X U,
  ~ In X (ftv_pred p) ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_ty U ->
  instantiate_pred (type_subst_update theta X U) gamma
    (open_pred_ty_rec k (Ty_FVar X) p) =
  open_pred_ty_rec k U (instantiate_pred theta gamma p).
Proof.
  induction p; intros; simpl in *; try reflexivity.
  - rewrite in_app_iff in H.
    rewrite !instantiate_open_ty_rec; intuition.
  - rewrite in_app_iff in H.
    rewrite IHp1, IHp2; intuition.
Qed.

Lemma instantiate_preds_open_ty_rec : forall ps k theta gamma X U,
  ~ In X (ftv_preds ps) ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_ty U ->
  instantiate_preds (type_subst_update theta X U) gamma
    (open_preds_ty_rec k (Ty_FVar X) ps) =
  open_preds_ty_rec k U (instantiate_preds theta gamma ps).
Proof.
  induction ps; intros; simpl in *; try reflexivity.
  rewrite in_app_iff in H.
  rewrite instantiate_pred_open_ty_rec, IHps; intuition.
Qed.

Lemma instantiate_rty_open_ty_rec : forall R k theta gamma X U,
  ~ In X (ftv_rty R) ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_ty U ->
  instantiate_rty (type_subst_update theta X U) gamma
    (open_rty_ty_rec k (Ty_FVar X) R) =
  open_rty_ty_rec k U (instantiate_rty theta gamma R).
Proof.
  induction R; intros; simpl in *.
  - rewrite in_app_iff in H.
    f_equal.
    + apply instantiate_ty_open_rec; intuition.
    + apply instantiate_preds_open_ty_rec; intuition.
  - rewrite in_app_iff in H.
    rewrite IHR1, IHR2; intuition.
  - rewrite in_app_iff in H.
    rewrite IHR1, IHR2; intuition.
  - f_equal. apply IHR; assumption.
Qed.

Lemma instantiate_rty_open_ty : forall R theta gamma X U,
  ~ In X (ftv_rty R) ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_ty U ->
  instantiate_rty (type_subst_update theta X U) gamma
    (open_rty_ty R (Ty_FVar X)) =
  open_rty_ty (instantiate_rty theta gamma R) U.
Proof.
  intros. unfold open_rty_ty.
  apply instantiate_rty_open_ty_rec; assumption.
Qed.

Lemma instantiate_term_update_irrelevant : forall t theta gamma x u,
  ~ In x (fv_tm t) ->
  instantiate theta (term_subst_update gamma x u) t =
  instantiate theta gamma t.
Proof.
  induction t; intros; simpl in *; try reflexivity.
  - unfold term_subst_update.
    rewrite (proj2 (Nat.eqb_neq x a)); [reflexivity | intuition].
  - f_equal. apply IHt. exact H.
  - rewrite in_app_iff in H. f_equal; [apply IHt1 | apply IHt2]; intuition.
  - f_equal. apply IHt. exact H.
  - f_equal. apply IHt. exact H.
  - repeat rewrite in_app_iff in H. f_equal.
    + apply IHt1. tauto.
    + apply IHt2. tauto.
    + apply IHt3. tauto.
  - f_equal. apply IHt. exact H.
  - repeat rewrite in_app_iff in H. f_equal.
    + apply IHt1. tauto.
    + apply IHt2. tauto.
    + apply IHt3. tauto.
  - rewrite in_app_iff in H. f_equal; [apply IHt1 | apply IHt2]; intuition.
Qed.

Lemma instantiate_rty_term_update_irrelevant : forall R theta gamma x u,
  ~ In x (fv_rty R) ->
  instantiate_rty theta (term_subst_update gamma x u) R =
  instantiate_rty theta gamma R.
Proof.
  induction R; intros; simpl in *.
  - f_equal. induction p; simpl in *; try reflexivity.
    rewrite in_app_iff in H. f_equal.
    + induction p; simpl in *; try reflexivity.
      * rewrite in_app_iff in H. f_equal;
          apply instantiate_term_update_irrelevant; intuition.
      * rewrite in_app_iff in H. f_equal; [apply IHp1 | apply IHp2]; intuition.
    + apply IHp. intuition.
  - rewrite in_app_iff in H. f_equal; [apply IHR1 | apply IHR2]; intuition.
  - rewrite in_app_iff in H. f_equal; [apply IHR1 | apply IHR2]; intuition.
  - f_equal. apply IHR. exact H.
Qed.

Lemma instantiate_term_type_update_irrelevant : forall t theta gamma X U,
  ~ In X (ftv_tm t) ->
  instantiate (type_subst_update theta X U) gamma t =
  instantiate theta gamma t.
Proof.
  induction t; intros; simpl in *; try reflexivity.
  - rewrite in_app_iff in H. f_equal.
    + apply instantiate_ty_update_irrelevant. tauto.
    + apply IHt. tauto.
  - rewrite in_app_iff in H. f_equal; [apply IHt1 | apply IHt2]; tauto.
  - f_equal. apply IHt. exact H.
  - rewrite in_app_iff in H. f_equal.
    + apply IHt. tauto.
    + apply instantiate_ty_update_irrelevant. tauto.
  - repeat rewrite in_app_iff in H. f_equal.
    + apply IHt1. tauto.
    + apply IHt2. tauto.
    + apply IHt3. tauto.
  - f_equal. apply IHt. exact H.
  - repeat rewrite in_app_iff in H. f_equal.
    + apply IHt1. tauto.
    + apply IHt2. tauto.
    + apply IHt3. tauto.
  - rewrite in_app_iff in H. f_equal; [apply IHt1 | apply IHt2]; intuition.
Qed.

Lemma instantiate_rty_type_update_irrelevant : forall R theta gamma X U,
  ~ In X (ftv_rty R) ->
  instantiate_rty (type_subst_update theta X U) gamma R =
  instantiate_rty theta gamma R.
Proof.
  induction R; intros; simpl in *.
  - rewrite in_app_iff in H. f_equal.
    + apply instantiate_ty_update_irrelevant. intuition.
    + induction p; simpl in *; try reflexivity.
      rewrite in_app_iff in H. f_equal.
      * induction p; simpl in *; try reflexivity.
        -- rewrite in_app_iff in H. f_equal;
             apply instantiate_term_type_update_irrelevant; intuition.
        -- rewrite in_app_iff in H. f_equal; [apply IHp1 | apply IHp2]; intuition.
      * apply IHp. intuition.
  - rewrite in_app_iff in H. f_equal; [apply IHR1 | apply IHR2]; intuition.
  - rewrite in_app_iff in H. f_equal; [apply IHR1 | apply IHR2]; intuition.
  - f_equal. apply IHR. exact H.
Qed.

Lemma instantiate_open_tm_rec_commute : forall t k u theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate theta gamma (open_tm_rec k u t) =
  open_tm_rec k (instantiate theta gamma u) (instantiate theta gamma t).
Proof.
  induction t; intros; simpl; try reflexivity.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. apply open_tm_rec_lc_at with (K := 0).
    eapply lc_tm_at_monotone; [apply H0 | lia | lia].
  - f_equal. apply IHt; assumption.
  - f_equal; [apply IHt1 | apply IHt2]; assumption.
  - f_equal. apply IHt; assumption.
  - f_equal. apply IHt; assumption.
  - f_equal; [apply IHt1 | apply IHt2 | apply IHt3]; assumption.
  - f_equal. apply IHt; assumption.
  - f_equal; [apply IHt1 | apply IHt2 | apply IHt3]; assumption.
  - f_equal; [apply IHt1 | apply IHt2]; assumption.
Qed.

Lemma instantiate_open_tm_commute : forall t u theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate theta gamma (open_tm t u) =
  open_tm (instantiate theta gamma t) (instantiate theta gamma u).
Proof.
  intros. unfold open_tm. apply instantiate_open_tm_rec_commute; assumption.
Qed.

Lemma instantiate_pred_open_tm_commute : forall p k u theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate_pred theta gamma (open_pred_tm_rec k u p) =
  open_pred_tm_rec k (instantiate theta gamma u)
    (instantiate_pred theta gamma p).
Proof.
  induction p; intros; simpl; try reflexivity.
  - rewrite !instantiate_open_tm_rec_commute; try assumption. reflexivity.
  - rewrite IHp1, IHp2; try assumption. reflexivity.
Qed.

Lemma instantiate_preds_open_tm_commute : forall ps k u theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate_preds theta gamma (open_preds_tm_rec k u ps) =
  open_preds_tm_rec k (instantiate theta gamma u)
    (instantiate_preds theta gamma ps).
Proof.
  induction ps; intros; simpl; try reflexivity.
  rewrite instantiate_pred_open_tm_commute, IHps; try assumption. reflexivity.
Qed.

Lemma instantiate_rty_open_tm_commute : forall R k u theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate_rty theta gamma (open_rty_tm_rec k u R) =
  open_rty_tm_rec k (instantiate theta gamma u)
    (instantiate_rty theta gamma R).
Proof.
  induction R; intros; simpl.
  - f_equal. apply instantiate_preds_open_tm_commute; assumption.
  - rewrite IHR1, IHR2; try assumption. reflexivity.
  - rewrite IHR1, IHR2; try assumption. reflexivity.
  - rewrite IHR; try assumption. reflexivity.
Qed.

Lemma instantiate_rty_open_tm_commute_top : forall R u theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate_rty theta gamma (open_rty_tm R u) =
  open_rty_tm (instantiate_rty theta gamma R) (instantiate theta gamma u).
Proof.
  intros. unfold open_rty_tm. apply instantiate_rty_open_tm_commute; assumption.
Qed.

Lemma instantiate_open_ty_tm_rec_commute : forall t k U theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_ty U ->
  instantiate theta gamma (open_tm_ty_rec k U t) =
  open_tm_ty_rec k (instantiate_ty theta U) (instantiate theta gamma t).
Proof.
  induction t; intros; simpl; try reflexivity.
  - symmetry. apply open_tm_ty_rec_lc_at with (k := 0).
    eapply lc_tm_at_monotone; [apply H0 | lia | lia].
  - f_equal.
    + apply instantiate_ty_open_rec_commute. exact H.
    + apply IHt; assumption.
  - f_equal; [apply IHt1 | apply IHt2]; assumption.
  - f_equal. apply IHt; assumption.
  - f_equal.
    + apply IHt; assumption.
    + apply instantiate_ty_open_rec_commute. exact H.
  - f_equal; [apply IHt1 | apply IHt2 | apply IHt3]; assumption.
  - f_equal. apply IHt; assumption.
  - f_equal; [apply IHt1 | apply IHt2 | apply IHt3]; assumption.
  - f_equal; [apply IHt1 | apply IHt2]; assumption.
Qed.

Lemma instantiate_open_ty_tm_commute : forall t U theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_ty U ->
  instantiate theta gamma (open_tm_ty t U) =
  open_tm_ty (instantiate theta gamma t) (instantiate_ty theta U).
Proof.
  intros. unfold open_tm_ty.
  apply instantiate_open_ty_tm_rec_commute; assumption.
Qed.

Lemma instantiate_pred_open_ty_commute : forall p k U theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_ty U ->
  instantiate_pred theta gamma (open_pred_ty_rec k U p) =
  open_pred_ty_rec k (instantiate_ty theta U)
    (instantiate_pred theta gamma p).
Proof.
  induction p; intros; simpl; try reflexivity.
  - rewrite !instantiate_open_ty_tm_rec_commute; try assumption. reflexivity.
  - rewrite IHp1, IHp2; try assumption. reflexivity.
Qed.

Lemma instantiate_preds_open_ty_commute : forall ps k U theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_ty U ->
  instantiate_preds theta gamma (open_preds_ty_rec k U ps) =
  open_preds_ty_rec k (instantiate_ty theta U)
    (instantiate_preds theta gamma ps).
Proof.
  induction ps; intros; simpl; try reflexivity.
  rewrite instantiate_pred_open_ty_commute, IHps; try assumption. reflexivity.
Qed.

Lemma instantiate_rty_open_ty_commute : forall R k U theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_ty U ->
  instantiate_rty theta gamma (open_rty_ty_rec k U R) =
  open_rty_ty_rec k (instantiate_ty theta U)
    (instantiate_rty theta gamma R).
Proof.
  induction R; intros; simpl.
  - rewrite instantiate_ty_open_rec_commute,
      instantiate_preds_open_ty_commute; try assumption. reflexivity.
  - rewrite IHR1, IHR2; try assumption. reflexivity.
  - rewrite IHR1, IHR2; try assumption. reflexivity.
  - rewrite IHR; try assumption. reflexivity.
Qed.

Lemma instantiate_rty_open_ty_commute_top : forall R U theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_ty U ->
  instantiate_rty theta gamma (open_rty_ty R U) =
  open_rty_ty (instantiate_rty theta gamma R) (instantiate_ty theta U).
Proof.
  intros. unfold open_rty_ty. apply instantiate_rty_open_ty_commute; assumption.
Qed.

Lemma instantiate_numeric_value : forall n theta gamma,
  numeric_value n -> numeric_value (instantiate theta gamma n).
Proof.
  intros n theta gamma Hnumeric. induction Hnumeric; simpl.
  - apply nv_zero.
  - apply nv_succ. exact IHHnumeric.
Qed.

Lemma instantiate_value : forall v theta gamma,
  value v ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  value (instantiate theta gamma v).
Proof.
  intros v theta gamma Hv Htheta Hgamma. inversion Hv; subst; simpl.
  - apply v_abs.
    change (locally_closed_tm (instantiate theta gamma (tm_abs T t))).
    apply instantiate_closed; assumption.
  - apply v_tabs.
    change (locally_closed_tm (instantiate theta gamma (tm_tabs t))).
    apply instantiate_closed; assumption.
  - apply v_true.
  - apply v_false.
  - apply v_nat. apply instantiate_numeric_value. assumption.
Qed.

Lemma instantiate_step : forall t t' theta gamma,
  t --> t' ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  instantiate theta gamma t --> instantiate theta gamma t'.
Proof.
  intros t t' theta gamma Hstep Htheta Hgamma. induction Hstep; simpl.
  - rewrite instantiate_open_tm_commute; try assumption.
    + apply ST_AppAbs.
      * change (locally_closed_tm (instantiate theta gamma (tm_abs T t))).
        apply instantiate_closed; assumption.
      * apply instantiate_value; assumption.
    + apply value_regular. exact H0.
  - apply ST_App1.
    + apply IHHstep.
    + apply instantiate_closed; assumption.
  - apply ST_App2.
    + apply instantiate_value; assumption.
    + apply IHHstep.
  - rewrite instantiate_open_ty_tm_commute; try assumption.
    + apply ST_TAppTabs.
      * change (locally_closed_tm (instantiate theta gamma (tm_tabs t))).
        apply instantiate_closed; assumption.
      * apply instantiate_ty_closed; assumption.
  - apply ST_TApp.
    + apply IHHstep.
    + apply instantiate_ty_closed; assumption.
  - apply ST_Succ. exact IHHstep.
  - apply ST_RecArg.
    + exact IHHstep.
    + apply instantiate_closed; assumption.
    + apply instantiate_closed; assumption.
  - apply ST_RecBase.
    + apply instantiate_numeric_value. assumption.
    + exact IHHstep.
    + apply instantiate_closed; assumption.
  - apply ST_RecStep.
    + apply instantiate_numeric_value. assumption.
    + apply instantiate_value; assumption.
    + exact IHHstep.
  - apply ST_RecZero; apply instantiate_value; assumption.
  - apply ST_RecSucc.
    + apply instantiate_numeric_value. assumption.
    + apply instantiate_value; assumption.
    + apply instantiate_value; assumption.
  - apply ST_IfTrue; apply instantiate_closed; assumption.
  - apply ST_IfFalse; apply instantiate_closed; assumption.
  - apply ST_If.
    + apply IHHstep.
    + apply instantiate_closed; assumption.
    + apply instantiate_closed; assumption.
  - apply ST_ChoiceLeft; apply instantiate_closed; assumption.
  - apply ST_ChoiceRight; apply instantiate_closed; assumption.
Qed.

Lemma instantiate_predicate_multistep : forall t t' theta gamma,
  predicate_multistep t t' ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  predicate_multistep (instantiate theta gamma t)
    (instantiate theta gamma t').
Proof.
  intros t t' theta gamma Hmulti Htheta Hgamma. induction Hmulti.
  - apply PMS_Refl.
  - eapply PMS_Step.
    + eapply instantiate_step; eauto.
    + exact IHHmulti.
Qed.

Lemma instantiate_predicate_holds : forall p theta gamma,
  predicate_holds p ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  predicate_holds (instantiate_pred theta gamma p).
Proof.
  intros p theta gamma Hholds Htheta Hgamma. induction Hholds; simpl.
  - apply PH_True.
  - eapply PH_Eq with (v := instantiate theta gamma v).
    + eapply instantiate_predicate_multistep; eauto.
    + eapply instantiate_predicate_multistep; eauto.
    + eapply instantiate_value; eauto.
  - apply PH_And; assumption.
Qed.

Lemma instantiate_predicates_hold : forall ps theta gamma,
  predicates_hold ps ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  predicates_hold (instantiate_preds theta gamma ps).
Proof.
  intros ps theta gamma Hholds Htheta Hgamma. induction Hholds; simpl.
  - apply PHS_Empty.
  - apply PHS_Cons.
    + eapply instantiate_predicate_holds; eauto.
    + exact IHHholds.
Qed.

Lemma instantiate_pred_open_rec_commute : forall p k u theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate_pred theta gamma (open_pred_tm_rec k u p) =
  open_pred_tm_rec k (instantiate theta gamma u)
    (instantiate_pred theta gamma p).
Proof.
  induction p; intros; simpl; try reflexivity.
  - f_equal; apply instantiate_open_tm_rec_commute; assumption.
  - f_equal; [apply IHp1 | apply IHp2]; assumption.
Qed.

Lemma instantiate_preds_open_commute : forall ps u theta gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  locally_closed_tm u ->
  instantiate_preds theta gamma (open_preds_tm ps u) =
  open_preds_tm (instantiate_preds theta gamma ps)
    (instantiate theta gamma u).
Proof.
  induction ps; intros; unfold open_preds_tm in *; simpl in *; try reflexivity.
  f_equal.
  - apply instantiate_pred_open_rec_commute; assumption.
  - apply IHps; assumption.
Qed.

Equations denotes (R : rty) (v : tm) : Prop by wf (rty_size R) lt :=
  denotes (R_Refine T ps) v :=

      value v /\
      has_type [] empty v T /\
      predicates_hold (open_preds_tm ps v);
  denotes (R_Func R1 R2) v :=

      value v /\
      has_type [] empty v (erase (R_Func R1 R2)) /\
      forall arg,
        denotes R1 arg ->
        locally_closed_tm (tm_app v arg) /\
        strongly_normalizing (tm_app v arg) /\
        forall result,
          multi (tm_app v arg) result ->
          value result ->
          denotes (open_rty_tm R2 arg) result;
  denotes (R_Exists R1 R2) v :=
      value v /\
      has_type [] empty v (erase (R_Exists R1 R2)) /\
      exists witness,
        denotes R1 witness /\
        denotes (open_rty_tm R2 witness) v;
  denotes (R_Poly R1) v :=
      value v /\
      has_type [] empty v (erase (R_Poly R1)) /\
      forall U,
        wf_ty [] U ->
        locally_closed_tm (tm_tapp v U) /\
        strongly_normalizing (tm_tapp v U) /\
        forall result,
          multi (tm_tapp v U) result ->
          value result ->
          denotes (open_rty_ty R1 U) result.
Next Obligation.
  simpl. lia.
Qed.
Next Obligation.
  rewrite rty_size_open_tm. simpl. lia.
Qed.
Next Obligation.
  simpl. lia.
Qed.
Next Obligation.
  rewrite rty_size_open_tm. simpl. lia.
Qed.
Next Obligation.
  rewrite rty_size_open_ty. simpl. lia.
Qed.

Definition evals_denotes (R : rty) (t : tm) : Prop :=
  locally_closed_tm t /\
  strongly_normalizing t /\
  forall v,
    multi t v ->
    value v ->
    denotes R v.

End CombinedRefinementDenotations.

Module SystemFRefinementSoundnessIfNondeterminismRecursionMediumTask.
Import ListNotations.
Import SystemFNormalizationIfNondeterminismRecursionEasyTask.
Import CombinedCoreTyping.
Import CombinedCoreMetatheory.
Import CombinedRefinementTyping.
Import CombinedRefinementDenotations.

Theorem refinement_soundness : forall t T ps v,
  has_rtype [] empty_rcontext t (R_Refine T ps) ->
  multi t v ->
  value v ->
  predicates_hold (open_preds_tm ps v).
Proof.

Qed.

End SystemFRefinementSoundnessIfNondeterminismRecursionMediumTask.
