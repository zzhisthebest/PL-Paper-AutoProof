(** System F CBV strong-normalization benchmark, Hard variant.
    Features: if-nondeterminism-recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFNormalizationIfNondeterminismRecursionHardTask.

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

Inductive multi : tm -> tm -> Prop :=
  | multi_refl : forall x, multi x x
  | multi_step : forall x y z, x --> y -> multi y z -> multi x z.
Notation "t '-->*' u" := (multi t u) (at level 40).

Inductive strongly_normalizing : tm -> Prop :=
  | SN_intro : forall t,
      (forall u, t --> u -> strongly_normalizing u) -> strongly_normalizing t.

Hint Constructors lc_ty_at lc_tm_at value : core.

(* Construct the logical relation and supporting proofs here. *)

Lemma lc_tm_open_inv : forall K k t x,
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) -> lc_tm_at K (S k) t.
Proof.
  intros K k t; revert K k. induction t; intros K k x Hlc; simpl in Hlc.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst. constructor. lia.
    + inversion Hlc; subst. constructor. apply Nat.eqb_neq in E. lia.
  - constructor.
  - inversion Hlc; subst. econstructor; eauto.
  - inversion Hlc; subst. econstructor; eauto.
  - inversion Hlc; subst. econstructor; eauto.
  - inversion Hlc; subst. econstructor; eauto.
  - constructor.
  - constructor.
  - inversion Hlc; subst. econstructor; eauto.
  - constructor.
  - inversion Hlc; subst. econstructor; eauto.
  - inversion Hlc; subst. econstructor; eauto.
  - inversion Hlc; subst. econstructor; eauto.
Qed.

Lemma lc_ty_open_inv : forall k T X,
  lc_ty_at k (open_ty_rec k (Ty_FVar X) T) -> lc_ty_at (S k) T.
Proof.
  intros k T; revert k; induction T; intros k X Hlc; simpl in Hlc.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst. constructor. lia.
    + inversion Hlc; subst. constructor. apply Nat.eqb_neq in E. lia.
  - constructor.
  - inversion Hlc; subst. econstructor; eauto.
  - inversion Hlc; subst. econstructor. eapply IHT; eauto.
  - constructor.
  - constructor.
Qed.

Lemma lc_tm_ty_open_inv : forall K k t X,
  lc_tm_at K k (open_tm_ty_rec K (Ty_FVar X) t) -> lc_tm_at (S K) k t.
Proof.
  intros K k t; revert K k; induction t; intros K k X Hlc; simpl in Hlc.
  - destruct (Nat.eqb k n); inversion Hlc; subst; constructor; assumption.
  - inversion Hlc; subst. constructor.
  - inversion Hlc; subst. econstructor.
    + eapply lc_ty_open_inv; eauto.
    + eapply IHt; eauto.
  - inversion Hlc; subst. econstructor; eauto.
  - inversion Hlc; subst. econstructor. eapply IHt; eauto.
  - inversion Hlc; subst. econstructor.
    + eapply IHt; eauto.
    + eapply lc_ty_open_inv; eauto.
  - inversion Hlc; subst. constructor.
  - inversion Hlc; subst. constructor.
  - inversion Hlc; subst. econstructor; eauto.
  - inversion Hlc; subst. constructor.
  - inversion Hlc; subst. econstructor; eauto.
  - inversion Hlc; subst. econstructor; eauto.
  - inversion Hlc; subst. econstructor; eauto.
Qed.

Fixpoint max_atom_list (L : list atom) : atom :=
  match L with [] => 0 | x :: L' => Nat.max x (max_atom_list L') end.

Lemma max_atom_list_bound : forall (L : list atom) (x : atom),
  In x L -> x <= max_atom_list L.
Proof.
  induction L as [|a L IH]; intros x Hin; simpl in *.
  - contradiction.
  - destruct Hin as [->|Hin].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [eapply IH; eauto|apply Nat.le_max_r].
Qed.

Lemma fresh_atom_list : forall (L : list atom), exists x, ~ In x L.
Proof.
  intros L. exists (S (max_atom_list L)). intro Hin.
  pose proof (max_atom_list_bound L _ Hin). lia.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> lc_ty_at 0 T.
Proof.
  intros Delta T Hwf; induction Hwf.
  - constructor.
  - econstructor; eauto.
  - constructor. destruct (fresh_atom_list L) as [X HX].
    specialize (H0 X HX). eapply lc_ty_open_inv; eauto.
  - constructor.
  - constructor.
Qed.

Lemma has_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T Hty; induction Hty; unfold locally_closed_tm.
  - constructor.
  - econstructor.
    + eapply wf_ty_lc; eauto.
    + destruct (fresh_atom_list L) as [x Hx].
      specialize (H1 x Hx). eapply lc_tm_open_inv; eauto.
  - econstructor; eauto.
  - econstructor.
    destruct (fresh_atom_list L) as [X HX].
    specialize (H0 X HX). eapply lc_tm_ty_open_inv; eauto.
  - econstructor; eauto using wf_ty_lc.
  - constructor.
  - constructor.
  - econstructor; eauto.
  - constructor.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
Qed.

Lemma sn_of_step : forall t u,
  strongly_normalizing t -> t --> u -> strongly_normalizing u.
Proof. intros t u H; inversion H; auto. Qed.

Lemma sn_of_multistep : forall t u,
  strongly_normalizing t -> t -->* u -> strongly_normalizing u.
Proof.
  intros t u Hred Hmulti. induction Hmulti; auto.
  eapply IHHmulti. eapply sn_of_step; eauto.
Qed.

Lemma numeric_value_no_step : forall n,
  numeric_value n -> forall u, ~ n --> u.
Proof.
  intros n Hn. induction Hn; intros u Hs.
  - inversion Hs.
  - inversion Hs; subst. eapply IHHn; eauto.
Qed.

Lemma sn_value : forall v, value v -> strongly_normalizing v.
Proof.
  intros v Hv. induction Hv; constructor; intros u Hstep;
    try solve [inversion Hstep];
    try solve [exfalso; eapply numeric_value_no_step; eauto].
Qed.

(* A reducibility candidate for Nat needs to support primitive recursion:
   the recursive call is smaller in its numeric argument, but its result is
   itself fed to the step function. *)
Definition reducible (T : ty) (t : tm) : Prop :=
  strongly_normalizing t.

Definition term_environment := list (atom * tm).

(* Erase type annotations from the computational syntax.  This makes the
   irrelevance of type substitution explicit in the type-abstraction case. *)
Fixpoint erase_types (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs _ b => tm_abs Ty_Bool (erase_types b)
  | tm_app a b => tm_app (erase_types a) (erase_types b)
  | tm_tabs b => tm_tabs (erase_types b)
  | tm_tapp a _ => tm_tapp (erase_types a) Ty_Bool
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if a b c => tm_if (erase_types a) (erase_types b) (erase_types c)
  | tm_zero => tm_zero
  | tm_succ a => tm_succ (erase_types a)
  | tm_natrec n b s => tm_natrec (erase_types n) (erase_types b) (erase_types s)
  | tm_choice a b => tm_choice (erase_types a) (erase_types b)
  end.

Lemma erase_types_idem : forall t, erase_types (erase_types t) = erase_types t.
Proof. induction t; simpl; f_equal; auto. Qed.

Lemma erase_types_ty_subst : forall X U t,
  erase_types (tm_ty_subst X U t) = erase_types t.
Proof. induction t; simpl; f_equal; auto. Qed.

Lemma erase_types_open_tm_ty_rec : forall t k U,
  erase_types (open_tm_ty_rec k U t) = erase_types t.
Proof.
  induction t; intros k U; simpl; try rewrite IHt; try rewrite IHt1;
    try rewrite IHt2; try rewrite IHt3; reflexivity.
Qed.

Lemma erase_types_open_ty : forall t U,
  erase_types (open_tm_ty t U) = erase_types t.
Proof. intros; apply erase_types_open_tm_ty_rec. Qed.

Lemma open_tm_ty_erased_fixed_rec : forall t k U,
  open_tm_ty_rec k U (erase_types t) = erase_types t.
Proof.
  induction t; intros k U; simpl; try rewrite IHt; try rewrite IHt1;
    try rewrite IHt2; try rewrite IHt3; reflexivity.
Qed.

Lemma open_tm_ty_erased_fixed : forall t U,
  open_tm_ty (erase_types t) U = erase_types t.
Proof. intros; apply open_tm_ty_erased_fixed_rec. Qed.

Lemma erase_types_open_tm_rec : forall t k u,
  erase_types (open_tm_rec k u t) =
  open_tm_rec k (erase_types u) (erase_types t).
Proof.
  induction t; intros k u; simpl; try rewrite IHt; try rewrite IHt1;
    try rewrite IHt2; try rewrite IHt3; try (destruct (Nat.eqb k n)); reflexivity.
Qed.

Lemma erase_types_open_tm : forall t u,
  erase_types (open_tm t u) = open_tm (erase_types t) (erase_types u).
Proof. intros; apply erase_types_open_tm_rec. Qed.

Lemma lc_erase : forall K k t, lc_tm_at K k t -> lc_tm_at K k (erase_types t).
Proof. intros K k t H; induction H; simpl; eauto using lc_tm_at. Qed.

Lemma locally_closed_erase : forall t,
  locally_closed_tm t -> locally_closed_tm (erase_types t).
Proof. intros t H; unfold locally_closed_tm in *; eapply lc_erase; eauto. Qed.

Lemma nv_erase : forall n, numeric_value n -> numeric_value (erase_types n).
Proof. intros n H; induction H; simpl; eauto using numeric_value. Qed.

Lemma value_erase : forall v, value v -> value (erase_types v).
Proof.
  intros v H; induction H.
  - simpl. apply v_abs. unfold locally_closed_tm in *.
    change (lc_tm_at 0 0 (erase_types (tm_abs T t))). apply lc_erase. exact H.
  - simpl. apply v_tabs. unfold locally_closed_tm in *.
    change (lc_tm_at 0 0 (erase_types (tm_tabs t))). apply lc_erase. exact H.
  - simpl. constructor.
  - simpl. constructor.
  - simpl. apply v_nat. now apply nv_erase.
Qed.

Lemma step_erases : forall t u, t --> u -> erase_types t --> erase_types u.
Proof.
  intros t u H; induction H; simpl.
  - rewrite erase_types_open_tm. apply ST_AppAbs.
    + change (locally_closed_tm (erase_types (tm_abs T t))).
      apply locally_closed_erase; assumption.
    + apply value_erase; assumption.
  - apply ST_App1; eauto using locally_closed_erase.
  - apply ST_App2; eauto using value_erase.
  - rewrite erase_types_open_ty.
    replace (erase_types t) with (open_tm_ty (erase_types t) Ty_Bool) at 2.
    2: exact (open_tm_ty_erased_fixed t Ty_Bool).
    apply ST_TAppTabs.
    + change (locally_closed_tm (erase_types (tm_tabs t))).
      apply locally_closed_erase; assumption.
    + constructor.
  - apply ST_TApp; [assumption|constructor].
  - apply ST_Succ; assumption.
  - apply ST_RecArg; eauto using locally_closed_erase.
  - apply ST_RecBase; eauto using nv_erase, locally_closed_erase.
  - apply ST_RecStep; eauto using nv_erase, value_erase.
  - apply ST_RecZero; eauto using value_erase.
  - apply ST_RecSucc; eauto using nv_erase, value_erase.
  - apply ST_IfTrue; eauto using locally_closed_erase.
  - apply ST_IfFalse; eauto using locally_closed_erase.
  - apply ST_If; eauto using locally_closed_erase.
  - apply ST_ChoiceLeft; eauto using locally_closed_erase.
  - apply ST_ChoiceRight; eauto using locally_closed_erase.
Qed.

Lemma sn_from_erasure : forall t,
  strongly_normalizing (erase_types t) -> strongly_normalizing t.
Proof.
  intros t H.
  remember (erase_types t) as e eqn:E.
  revert t E.
  induction H as [e Hnext IH]; intros t E.
  constructor. intros u Hu.
  eapply (IH (erase_types u)).
  - rewrite E. now apply step_erases.
  - reflexivity.
Qed.

Record reducibility_candidate : Type := {
  candidate_raw_rel : tm -> Prop;
  candidate_raw_sn : forall t, candidate_raw_rel t -> strongly_normalizing t;
  candidate_raw_reduce : forall t, candidate_raw_rel (erase_types t) ->
    forall u, erase_types t --> u -> candidate_raw_rel (erase_types u);
  candidate_raw_expand : forall t,
    ~ value (erase_types t) ->
    (forall u, erase_types t --> u -> candidate_raw_rel (erase_types u)) ->
    candidate_raw_rel (erase_types t)
}.

Definition candidate_rel (C : reducibility_candidate) (t : tm) : Prop :=
  candidate_raw_rel C (erase_types t).

Lemma candidate_rel_erasure : forall C t,
  candidate_rel C (erase_types t) <-> candidate_rel C t.
Proof. intros; unfold candidate_rel; rewrite erase_types_idem; tauto. Qed.

Definition candidate_sn (C : reducibility_candidate) (t : tm)
    (H : candidate_rel C t) : strongly_normalizing (erase_types t) :=
  candidate_raw_sn C (erase_types t) H.

Definition candidate_expand (C : reducibility_candidate) (t : tm)
    (Hnv : ~ value (erase_types t))
    (Hnext : forall u, erase_types t --> u -> candidate_rel C u)
    : candidate_rel C t :=
  candidate_raw_expand C t Hnv Hnext.

Definition candidate_reduce (C : reducibility_candidate) (t : tm)
    (H : candidate_rel C t) (u : tm) (Hs : t --> u)
    : candidate_rel C u.
Proof.
  unfold candidate_rel in *. rewrite <- (erase_types_idem u).
  eapply candidate_raw_reduce with (t := t) (u := erase_types u).
  - exact H.
  - apply step_erases. exact Hs.
Defined.

Lemma candidate_rel_same_erasure : forall C t u,
  erase_types t = erase_types u -> candidate_rel C t -> candidate_rel C u.
Proof. intros C t u E H; unfold candidate_rel in *; now rewrite E in H. Qed.

Definition type_environment := list (atom * reducibility_candidate).

Definition good_term (t : tm) : Prop :=
  strongly_normalizing t.

Definition base_candidate : reducibility_candidate.
Proof.
  refine {| candidate_raw_rel := good_term |}.
  - intros t Hsn; exact Hsn.
  - intros t Hsn u Hstep. eapply sn_of_step with (t := erase_types t).
    + exact Hsn.
    + rewrite <- (erase_types_idem t). apply step_erases. exact Hstep.
  - intros t Hnv Hnext. constructor. intros u Hu.
    eapply sn_from_erasure. exact (Hnext u Hu).
Defined.

Definition bool_shape (t : tm) : Prop := t = tm_true \/ t = tm_false.
Definition nat_shape (t : tm) : Prop := numeric_value t.

Lemma multi_erases : forall t u, t -->* u -> erase_types t -->* erase_types u.
Proof.
  intros t u H; induction H as [t|x y z Hxy Hyz IH].
  - constructor.
  - eapply multi_step; [apply step_erases; eauto|exact IH].
Qed.

Lemma bool_shape_erase_inv : forall t,
  value t -> bool_shape (erase_types t) -> bool_shape t.
Proof.
  intros t Hv [H|H]; destruct t; simpl in H; try discriminate;
    try (left; reflexivity); try (right; reflexivity).
Qed.

Lemma nat_shape_erase_inv : forall t,
  value t -> nat_shape (erase_types t) -> nat_shape t.
Proof.
  intros t Hv Hn. inversion Hv; subst; simpl in Hn.
  - inversion Hn.
  - inversion Hn.
  - inversion Hn.
  - inversion Hn.
  - assumption.
Qed.

Definition bool_candidate : reducibility_candidate.
Proof.
  refine {| candidate_raw_rel := fun t =>
    strongly_normalizing t /\ forall u, multi t u -> value u -> bool_shape u |}.
  - intros t [Hsn _]; exact Hsn.
  - intros t [Hsn Hshape] u Hstep. split.
    + assert (Hs : erase_types t --> erase_types u).
      { pose proof (@step_erases (erase_types t) u Hstep) as Hs.
        rewrite erase_types_idem in Hs. exact Hs. }
      exact (sn_of_step (erase_types t) (erase_types u) Hsn Hs).
    + intros v Hmulti Hv.
      assert (Hs : erase_types t --> erase_types u).
      { pose proof (@step_erases (erase_types t) u Hstep) as Hs.
        rewrite erase_types_idem in Hs. exact Hs. }
      assert (Htail : erase_types u -->* erase_types v).
      { pose proof (multi_erases (erase_types u) v Hmulti) as Htail.
        rewrite erase_types_idem in Htail. exact Htail. }
      apply bool_shape_erase_inv; [exact Hv|].
      exact (Hshape (erase_types v)
        (@multi_step (erase_types t) (erase_types u) (erase_types v) Hs Htail)
        (value_erase v Hv)).
  - intros t Hnv Hnext. split.
    + constructor. intros u Hu. destruct (Hnext u Hu) as [Hsn _].
      eapply sn_from_erasure. exact Hsn.
    + intros v Hmulti Hv. inversion Hmulti; subst.
      * exfalso. apply Hnv. exact Hv.
      * destruct (Hnext y H) as [_ Hshape].
        apply bool_shape_erase_inv; [exact Hv|].
        eapply Hshape; [apply multi_erases; eauto|apply value_erase; exact Hv].
Defined.

Definition nat_candidate : reducibility_candidate.
Proof.
  refine {| candidate_raw_rel := fun t =>
    strongly_normalizing t /\ forall u, multi t u -> value u -> nat_shape u |}.
  - intros t [Hsn _]; exact Hsn.
  - intros t [Hsn Hshape] u Hstep. split.
    + assert (Hs : erase_types t --> erase_types u).
      { pose proof (@step_erases (erase_types t) u Hstep) as Hs.
        rewrite erase_types_idem in Hs. exact Hs. }
      exact (sn_of_step (erase_types t) (erase_types u) Hsn Hs).
    + intros v Hmulti Hv.
      assert (Hs : erase_types t --> erase_types u).
      { pose proof (@step_erases (erase_types t) u Hstep) as Hs.
        rewrite erase_types_idem in Hs. exact Hs. }
      assert (Htail : erase_types u -->* erase_types v).
      { pose proof (multi_erases (erase_types u) v Hmulti) as Htail.
        rewrite erase_types_idem in Htail. exact Htail. }
      apply nat_shape_erase_inv; [exact Hv|].
      exact (Hshape (erase_types v)
        (@multi_step (erase_types t) (erase_types u) (erase_types v) Hs Htail)
        (value_erase v Hv)).
  - intros t Hnv Hnext. split.
    + constructor. intros u Hu. destruct (Hnext u Hu) as [Hsn _].
      eapply sn_from_erasure. exact Hsn.
    + intros v Hmulti Hv. inversion Hmulti; subst.
      * exfalso. apply Hnv. exact Hv.
      * destruct (Hnext y H) as [_ Hshape].
        apply nat_shape_erase_inv; [exact Hv|].
        eapply Hshape; [apply multi_erases; eauto|apply value_erase; exact Hv].
Defined.

Lemma bool_value_related : forall b,
  (b = tm_true \/ b = tm_false) -> candidate_rel bool_candidate b.
Proof.
  intros b Hb. destruct Hb as [Hb|Hb]; subst b; unfold candidate_rel; simpl.
  - split; [constructor; intros u H; inversion H|].
    intros u Hmulti Hv. inversion Hmulti; subst; [left; reflexivity|inversion H].
  - split; [constructor; intros u H; inversion H|].
    intros u Hmulti Hv. inversion Hmulti; subst; [right; reflexivity|inversion H].
Qed.

Lemma nat_value_related : forall n,
  numeric_value n -> candidate_rel nat_candidate n.
Proof.
  intros n Hn. pose proof (nv_erase n Hn) as Hne.
  unfold candidate_rel; simpl. split.
  - apply sn_value. constructor. exact Hne.
  - intros u Hmulti Hu. inversion Hmulti; subst.
    + exact Hne.
    + exfalso. eapply numeric_value_no_step; eauto.
Qed.

Lemma not_value_if : forall c t u, ~ value (tm_if c t u).
Proof. intros c t u H; inversion H; subst; inversion H0. Qed.

Lemma if_candidate : forall C c b1 b2,
  candidate_rel bool_candidate c -> candidate_rel C b1 -> candidate_rel C b2 ->
  locally_closed_tm (erase_types b1) -> locally_closed_tm (erase_types b2) ->
  candidate_rel C (tm_if c b1 b2).
Proof.
  intros C c b1 b2 Hc Hb1 Hb2 Hlc1 Hlc2.
  eapply candidate_rel_same_erasure with
    (t := tm_if (erase_types c) (erase_types b1) (erase_types b2)).
  - simpl. rewrite !erase_types_idem. reflexivity.
  -
  pose proof (candidate_sn bool_candidate c Hc) as Hsn.
  remember (erase_types c) as c0 eqn:E0.
  revert c b1 b2 Hc Hb1 Hb2 Hlc1 Hlc2 E0.
  induction Hsn as [c0 Hnext IH]; intros c b1 b2 Hc Hb1 Hb2 Hlc1 Hlc2 E0.
  subst c0.
  eapply candidate_expand with (C := C) (t := tm_if (erase_types c) (erase_types b1) (erase_types b2)).
  + apply not_value_if.
  + intros u Hu. inversion Hu; subst.
    * apply candidate_rel_same_erasure with (t := b1); [simpl; repeat rewrite erase_types_idem; reflexivity|exact Hb1].
    * apply candidate_rel_same_erasure with (t := b2); [simpl; repeat rewrite erase_types_idem; reflexivity|exact Hb2].
    * rewrite erase_types_idem in H2.
      assert (Hcr : candidate_rel bool_candidate t1').
      { unfold candidate_rel in *. eapply candidate_raw_reduce; eauto. }
      assert (H1E : erase_types c --> erase_types t1').
      { pose proof (@step_erases (erase_types c) t1' H2) as Hs.
        rewrite erase_types_idem in Hs. exact Hs. }
      pose proof (IH (erase_types t1') H1E t1' b1 b2 Hcr Hb1 Hb2 Hlc1 Hlc2 eq_refl) as Hif.
      eapply candidate_rel_same_erasure; [simpl; repeat rewrite erase_types_idem; reflexivity|exact Hif].
Qed.

Fixpoint lookup_term_environment (x : atom) (rho : term_environment) : option tm :=
  match rho with
  | [] => None
  | (y,v)::rho' => if Nat.eqb x y then Some v else lookup_term_environment x rho'
  end.

Fixpoint apply_term_environment (rho : term_environment) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x =>
      match lookup_term_environment x rho with
      | Some v => erase_types v
      | None => tm_fvar x
      end
  | tm_abs T b => tm_abs T (apply_term_environment rho b)
  | tm_app a b => tm_app (apply_term_environment rho a) (apply_term_environment rho b)
  | tm_tabs b => tm_tabs (apply_term_environment rho b)
  | tm_tapp a T => tm_tapp (apply_term_environment rho a) T
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if a b c => tm_if (apply_term_environment rho a)
      (apply_term_environment rho b) (apply_term_environment rho c)
  | tm_zero => tm_zero
  | tm_succ a => tm_succ (apply_term_environment rho a)
  | tm_natrec n b s => tm_natrec (apply_term_environment rho n)
      (apply_term_environment rho b) (apply_term_environment rho s)
  | tm_choice a b => tm_choice (apply_term_environment rho a) (apply_term_environment rho b)
  end.

Fixpoint fv_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs _ b => fv_tm b
  | tm_app a b => fv_tm a ++ fv_tm b
  | tm_tabs b => fv_tm b
  | tm_tapp a _ => fv_tm a
  | tm_true | tm_false | tm_zero => []
  | tm_if a b c => fv_tm a ++ fv_tm b ++ fv_tm c
  | tm_succ a => fv_tm a
  | tm_natrec n b s => fv_tm n ++ fv_tm b ++ fv_tm s
  | tm_choice a b => fv_tm a ++ fv_tm b
  end.

Lemma open_tm_rec_lc : forall K j t,
  lc_tm_at K j t -> forall k u, j <= k -> open_tm_rec k u t = t.
Proof.
  intros K j t Hlc. induction Hlc; intros k' u Hle; simpl.
  - destruct (Nat.eqb k' i) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + reflexivity.
  - reflexivity.
  - f_equal. apply IHHlc. lia.
  - rewrite IHHlc1 by lia. rewrite IHHlc2 by lia. reflexivity.
  - f_equal. apply IHHlc. exact Hle.
  - rewrite IHHlc by lia. reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHHlc1 by lia. rewrite IHHlc2 by lia. rewrite IHHlc3 by lia. reflexivity.
  - reflexivity.
  - f_equal. apply IHHlc. lia.
  - rewrite IHHlc1 by lia. rewrite IHHlc2 by lia. rewrite IHHlc3 by lia. reflexivity.
  - rewrite IHHlc1 by lia. rewrite IHHlc2 by lia. reflexivity.
Qed.

Lemma apply_env_open_rec : forall rho x v t k,
  lookup_term_environment x rho = None ->
  (forall y s, lookup_term_environment y rho = Some s ->
    locally_closed_tm (erase_types s)) ->
  ~ In x (fv_tm t) ->
  apply_term_environment ((x,v)::rho) (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k (erase_types v) (apply_term_environment rho t).
Proof.
  intros rho x v t; revert rho x v; induction t; intros rho x v k Hlookup Henvlc Hfresh;
    simpl in *.
  - destruct (Nat.eqb k n); simpl; try rewrite Nat.eqb_refl; reflexivity.
  - simpl in Hfresh. assert (E : Nat.eqb a x = false).
    { apply Nat.eqb_neq. intro Heq. subst. apply Hfresh. now left. }
    simpl. rewrite E.
    destruct (lookup_term_environment a rho) as [s|] eqn:Es.
    + assert (Hopen : open_tm_rec k (erase_types v) (erase_types s) = erase_types s).
      { eapply open_tm_rec_lc with (K := 0) (j := 0).
        - unfold locally_closed_tm. apply Henvlc with a. exact Es.
        - lia. }
      now rewrite Hopen.
    + reflexivity.
  - f_equal. eapply IHt; eauto.
  - assert (Hf1 : ~ In x (fv_tm t1)).
    { intro Hin. apply Hfresh. apply in_or_app. now left. }
    assert (Hf2 : ~ In x (fv_tm t2)).
    { intro Hin. apply Hfresh. apply in_or_app. now right. }
    rewrite (IHt1 rho x v k Hlookup Henvlc Hf1).
    rewrite (IHt2 rho x v k Hlookup Henvlc Hf2). reflexivity.
  - f_equal. eapply IHt; eauto.
  - f_equal. eapply IHt; eauto.
  - reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2, IHt3; try assumption; repeat rewrite in_app_iff in *; tauto.
  - reflexivity.
  - f_equal. eapply IHt; eauto.
  - rewrite IHt1, IHt2, IHt3; try assumption; repeat rewrite in_app_iff in *; tauto.
  - rewrite IHt1, IHt2; try assumption; repeat rewrite in_app_iff in *; tauto.
Qed.

Lemma apply_env_open : forall rho x v t,
  lookup_term_environment x rho = None ->
  (forall y s, lookup_term_environment y rho = Some s ->
    locally_closed_tm (erase_types s)) ->
  ~ In x (fv_tm t) ->
  apply_term_environment ((x,v)::rho) (open_tm t (tm_fvar x)) =
  open_tm (apply_term_environment rho t) (erase_types v).
Proof. intros; eapply apply_env_open_rec; eauto. Qed.

Fixpoint lookup_type_environment (X : atom) (eta : type_environment)
  : option reducibility_candidate :=
  match eta with
  | [] => None
  | (Y,R)::eta' => if Nat.eqb X Y then Some R else lookup_type_environment X eta'
  end.

Lemma not_value_app : forall t u, ~ value (tm_app t u).
Proof. intros t u H; inversion H; subst; try solve [inversion H0]. Qed.

Lemma not_value_tapp : forall t T, ~ value (tm_tapp t T).
Proof. intros t T H; inversion H; subst; try solve [inversion H0]. Qed.

Definition arrow_candidate (CA CB : reducibility_candidate) : reducibility_candidate.
Proof.
  refine {| candidate_raw_rel := fun t =>
    good_term t /\ forall u, locally_closed_tm u ->
      candidate_rel CA (erase_types u) -> candidate_rel CB (tm_app t u) |}.
  - intros t H; exact (proj1 H).
  - intros t H u Hstep. destruct H as [Hsn Hfun]. split.
    + eapply sn_of_step; [exact Hsn|].
      rewrite <- (erase_types_idem t). apply step_erases. exact Hstep.
    + intros a Hla Ha.
      pose proof (Hfun a Hla Ha) as Hcb.
      unfold candidate_rel in Hcb. simpl in Hcb.
      rewrite erase_types_idem in Hcb.
      pose proof (candidate_raw_reduce CB
        (tm_app t a) Hcb
        (tm_app u (erase_types a))
        (ST_App1 _ _ _ Hstep (locally_closed_erase a Hla))) as Hout.
      replace (erase_types (tm_app u (erase_types a))) with
        (tm_app (erase_types u) (erase_types a)) in Hout
        by (simpl; rewrite erase_types_idem; reflexivity).
      unfold candidate_rel. simpl. rewrite erase_types_idem. exact Hout.
  - intros t Hnv Hnext. split.
    + constructor. intros u Hu.
      pose proof (Hnext u Hu) as Hred. destruct Hred as [Hsn _].
      eapply sn_from_erasure; exact Hsn.
    + intros a Hla Ha.
      eapply candidate_expand with (C := CB)
        (t := tm_app (erase_types t) a).
      * apply not_value_app.
      * intros r Hr. inversion Hr; subst.
        -- exfalso. apply Hnv. rewrite <- (erase_types_idem t).
           rewrite <- H. eapply v_abs; eauto.
        -- rewrite erase_types_idem in H1.
           pose proof (Hnext t1' H1) as Hfun.
           unfold candidate_rel in Hfun. simpl in Hfun.
           destruct Hfun as [_ Hfun].
           specialize (Hfun a Hla Ha) as Hout.
           unfold candidate_rel in *. simpl in *.
           rewrite erase_types_idem in Hout. rewrite erase_types_idem. exact Hout.
        -- exfalso. apply Hnv. rewrite <- (erase_types_idem t). exact H1.
Defined.

Definition all_candidate (body : reducibility_candidate -> reducibility_candidate)
  : reducibility_candidate.
Proof.
  refine {| candidate_raw_rel := fun t => good_term t /\
    forall R U, locally_closed_ty U ->
      candidate_rel (body R) (tm_tapp t U) |}.
  - intros t H; exact (proj1 H).
  - intros t H u Hstep. destruct H as [Hsn Hall]. split.
    + eapply sn_of_step; [exact Hsn|].
      rewrite <- (erase_types_idem t). apply step_erases. exact Hstep.
    + intros R U HU.
      pose proof (Hall R U HU) as Hbody.
      unfold candidate_rel in Hbody |- *. simpl in Hbody |- *.
      assert (Hs : tm_tapp (erase_types t) Ty_Bool --> tm_tapp u Ty_Bool).
      { apply ST_TApp; [exact Hstep|constructor]. }
      pose proof (candidate_raw_reduce (body R)
        (tm_tapp t U) ltac:(rewrite !erase_types_idem in Hbody; exact Hbody)
        (tm_tapp u Ty_Bool) Hs) as Hred.
      rewrite erase_types_idem. exact Hred.
  - intros t Hnv Hnext. split.
    + constructor. intros u Hu.
      pose proof (Hnext u Hu) as Hred. destruct Hred as [Hsn _].
      eapply sn_from_erasure; exact Hsn.
    + intros R U HU.
      eapply candidate_expand with (C := body R)
        (t := tm_tapp (erase_types t) U).
      * apply not_value_tapp.
      * intros r Hr. inversion Hr; subst.
        -- exfalso. apply Hnv. rewrite <- (erase_types_idem t).
           rewrite <- H. eapply v_tabs; eauto.
        -- rewrite erase_types_idem in H1.
           pose proof (Hnext t' H1) as Hall'.
           unfold candidate_rel in Hall'. simpl in Hall'.
           destruct Hall' as [_ Hall']. specialize (Hall' R U HU).
           unfold candidate_rel in *. simpl in *.
           rewrite erase_types_idem in Hall'. exact Hall'.
Defined.

Fixpoint interp_type (eta : type_environment)
    (xi : list reducibility_candidate) (T : ty) : reducibility_candidate :=
  match T with
  | Ty_BVar i =>
      match nth_error xi i with Some R => R | None => base_candidate end
  | Ty_FVar X =>
      match lookup_type_environment X eta with Some R => R | None => base_candidate end
  | Ty_Arrow A B => arrow_candidate (interp_type eta xi A) (interp_type eta xi B)
  | Ty_All A => all_candidate (fun R => interp_type eta (R :: xi) A)
  | Ty_Bool => bool_candidate
  | Ty_Nat => nat_candidate
  end.

Definition candidate_equiv (C D : reducibility_candidate) : Prop :=
  forall t, candidate_rel C t <-> candidate_rel D t.

Lemma arrow_candidate_equiv : forall A A' B B',
  candidate_equiv A A' -> candidate_equiv B B' ->
  candidate_equiv (arrow_candidate A B) (arrow_candidate A' B').
Proof.
  intros A A' B B' HA HB t. unfold candidate_rel; simpl.
  split; intros [Hsn Hfun]; split; try assumption; intros u Hlu Harg.
  - apply HB. apply Hfun; [exact Hlu|apply HA; exact Harg].
  - apply HB. apply Hfun; [exact Hlu|apply HA; exact Harg].
Qed.

Lemma all_candidate_equiv : forall F G,
  (forall R, candidate_equiv (F R) (G R)) ->
  candidate_equiv (all_candidate F) (all_candidate G).
Proof.
  intros F G HFG t. unfold candidate_rel; simpl.
  split; intros [Hsn Hall]; split; try assumption; intros R U HU.
  - apply HFG. apply Hall; exact HU.
  - apply HFG. apply Hall; exact HU.
Qed.

Fixpoint insert_candidate (k : nat) (R : reducibility_candidate)
    (xi : list reducibility_candidate) : list reducibility_candidate :=
  match k with
  | 0 => R :: xi
  | S k' => match xi with
      | [] => base_candidate :: insert_candidate k' R []
      | Q :: xi' => Q :: insert_candidate k' R xi'
      end
  end.

Definition lookup_candidate (xi : list reducibility_candidate) (i : nat)
    : reducibility_candidate :=
  match nth_error xi i with Some R => R | None => base_candidate end.

Lemma lookup_insert_lt : forall k R xi i,
  i < k -> lookup_candidate (insert_candidate k R xi) i = lookup_candidate xi i.
Proof.
  induction k as [|k IH]; intros R xi i Hi; [lia|].
  destruct xi as [|Q xi].
  - destruct i as [|i].
    + reflexivity.
    + change (lookup_candidate (insert_candidate k R []) i = lookup_candidate [] (S i)).
      rewrite IH by lia. unfold lookup_candidate. destruct i; reflexivity.
  - destruct i as [|i].
    + reflexivity.
    + change (lookup_candidate (insert_candidate k R xi) i =
        lookup_candidate (Q :: xi) (S i)).
      simpl. rewrite IH by lia. reflexivity.
Qed.

Lemma lookup_insert_eq : forall k R xi,
  lookup_candidate (insert_candidate k R xi) k = R.
Proof.
  induction k; intros R xi; simpl.
  - reflexivity.
  - destruct xi as [|Q xi]; simpl; apply IHk.
Qed.

Definition candidate_equiv_refl (C : reducibility_candidate) : candidate_equiv C C :=
  fun _ => iff_refl _.

Lemma candidate_equiv_trans : forall A B C,
  candidate_equiv A B -> candidate_equiv B C -> candidate_equiv A C.
Proof. intros A B C HAB HBC t; specialize (HAB t); specialize (HBC t); tauto. Qed.

Definition prefix_equiv (k : nat) (xi xi' : list reducibility_candidate) : Prop :=
  forall i, i < k -> nth_error xi i = nth_error xi' i.

Lemma prefix_equiv_cons : forall k Q xi xi',
  prefix_equiv k xi xi' -> prefix_equiv (S k) (Q::xi) (Q::xi').
Proof.
  intros k Q xi xi' H i Hi. destruct i; simpl; [reflexivity|].
  apply H. lia.
Qed.

Lemma interp_prefix_equiv : forall eta k xi xi' T,
  lc_ty_at k T -> prefix_equiv k xi xi' ->
  candidate_equiv (interp_type eta xi T) (interp_type eta xi' T).
Proof.
  intros eta k xi xi' T Hlc Hpre. revert eta k xi xi' Hlc Hpre.
  induction T; intros eta k xi xi' Hlc Hpre; simpl in *.
  - inversion Hlc; subst. unfold candidate_equiv. intros t.
    unfold lookup_candidate. rewrite (Hpre n H1). tauto.
  - apply candidate_equiv_refl.
  - inversion Hlc; subst. apply arrow_candidate_equiv.
    + eapply IHT1; eauto.
    + eapply IHT2; eauto.
  - inversion Hlc; subst. apply all_candidate_equiv. intro R.
    eapply IHT; eauto. apply prefix_equiv_cons. exact Hpre.
  - apply candidate_equiv_refl.
  - apply candidate_equiv_refl.
Qed.

Lemma interp_closed_prefix : forall eta xi xi' T,
  locally_closed_ty T -> candidate_equiv (interp_type eta xi T) (interp_type eta xi' T).
Proof.
  intros eta xi xi' T Hlc.
  eapply (interp_prefix_equiv eta 0 xi xi' T); [exact Hlc|].
  intros i Hi; lia.
Qed.

Lemma interp_open_ty_rec : forall eta xi k R U T,
  lc_ty_at (S k) T -> locally_closed_ty U ->
  candidate_equiv R (interp_type eta xi U) ->
  candidate_equiv (interp_type eta (insert_candidate k R xi) T)
    (interp_type eta xi (open_ty_rec k U T)).
Proof.
  intros eta xi k R U T Hlc Hlu Hru.
  revert eta xi k R U Hlc Hlu Hru.
  induction T; intros eta xi k R U Hlc Hlu Hru; simpl in *.
  - inversion Hlc as [| | | | |]; subst.
    destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n.
      change (candidate_equiv (lookup_candidate (insert_candidate k R xi) k)
        (interp_type eta xi U)).
      unfold candidate_equiv. intros t. rewrite lookup_insert_eq. apply Hru.
    + apply Nat.eqb_neq in E. assert (Hik : n < k) by lia.
      change (candidate_equiv (lookup_candidate (insert_candidate k R xi) n)
        (lookup_candidate xi n)).
      unfold candidate_equiv. intros t. rewrite lookup_insert_lt by exact Hik.
      tauto.
  - apply candidate_equiv_refl.
  - inversion Hlc; subst. simpl. apply arrow_candidate_equiv.
    + eapply IHT1; eauto.
    + eapply IHT2; eauto.
  - inversion Hlc; subst. simpl. apply all_candidate_equiv. intro Q.
    assert (HruQ : candidate_equiv R (interp_type eta (Q::xi) U)).
    { eapply candidate_equiv_trans; [exact Hru|].
      apply interp_closed_prefix. exact Hlu. }
    eapply IHT with (eta := eta) (xi := Q::xi) (k := S k) (R := R) (U := U).
    + exact H1.
    + exact Hlu.
    + exact HruQ.
  - apply candidate_equiv_refl.
  - apply candidate_equiv_refl.
Qed.

Lemma interp_open_ty : forall eta T U,
  lc_ty_at 1 T -> locally_closed_ty U ->
  candidate_equiv (interp_type eta [interp_type eta [] U] T)
    (interp_type eta [] (open_ty T U)).
Proof.
  intros eta T U Ht Hu. unfold open_ty.
  eapply interp_open_ty_rec with (k := 0) (R := interp_type eta [] U); eauto.
  apply candidate_equiv_refl.
Qed.

Definition environment_interprets (Delta : ty_context) (eta : type_environment) : Prop :=
  forall X, In X Delta -> exists R, lookup_type_environment X eta = Some R.

Fixpoint fv_ty (T : ty) : list atom :=
  match T with
  | Ty_BVar _ | Ty_Bool | Ty_Nat => []
  | Ty_FVar X => [X]
  | Ty_Arrow A B => fv_ty A ++ fv_ty B
  | Ty_All A => fv_ty A
  end.

Fixpoint fv_context_types (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (_,T)::Gamma' => fv_ty T ++ fv_context_types Gamma'
  end.

Lemma lookup_type_environment_neq : forall X Y R eta,
  X <> Y ->
  lookup_type_environment X ((Y,R)::eta) = lookup_type_environment X eta.
Proof.
  intros X Y R eta Hneq. simpl.
  assert (Nat.eqb X Y = false) by (apply Nat.eqb_neq; exact Hneq).
  now rewrite H.
Qed.

Lemma environment_interprets_extend : forall Delta eta X R,
  environment_interprets Delta eta -> ~ In X Delta ->
  environment_interprets (X::Delta) ((X,R)::eta).
Proof.
  intros Delta eta X R Henv Hfresh Y Hin. simpl in Hin.
  destruct Hin as [->|Hin].
  - exists R. simpl. rewrite Nat.eqb_refl. reflexivity.
  - destruct (Henv Y Hin) as [S HS]. exists S.
    rewrite lookup_type_environment_neq; [exact HS|].
    intro Heq; subst. apply Hfresh. exact Hin.
Qed.

Lemma interp_type_extend : forall eta X R xi T,
  ~ In X (fv_ty T) ->
  candidate_equiv (interp_type eta xi T) (interp_type ((X,R)::eta) xi T).
Proof.
  intros eta X R xi T. revert xi. induction T; intros xi Hfresh.
  - cbn [interp_type]. apply candidate_equiv_refl.
  - simpl in Hfresh. assert (X <> a) by (intro; subst; apply Hfresh; now left).
    unfold candidate_equiv. intros t. cbn [interp_type].
    rewrite lookup_type_environment_neq by congruence.
    tauto.
  - cbn [interp_type]. apply arrow_candidate_equiv.
    + apply IHT1. intro Hin. apply Hfresh. apply in_or_app. now left.
    + apply IHT2. intro Hin. apply Hfresh. apply in_or_app. now right.
  - cbn [interp_type]. apply all_candidate_equiv. intro Q. apply IHT. exact Hfresh.
  - cbn [interp_type]. apply candidate_equiv_refl.
  - cbn [interp_type]. apply candidate_equiv_refl.
Qed.

Definition term_environment_interprets (Gamma : context)
    (eta : type_environment) (rho : term_environment) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    exists v, lookup_term_environment x rho = Some v /\
      candidate_rel (interp_type eta [] T) v /\
      locally_closed_tm (erase_types v).

Lemma term_environment_interprets_extend_type : forall Gamma eta rho X R,
  term_environment_interprets Gamma eta rho ->
  (forall T, (exists x, lookup_context x Gamma = Some T) ->
    ~ In X (fv_ty T)) ->
  term_environment_interprets Gamma ((X,R)::eta) rho.
Proof.
  intros Gamma eta rho X R Hinter Hfresh x T Hlookup.
  destruct (Hinter x T Hlookup) as [v [Hv [Hrel Hlc]]].
  exists v; split; [exact Hv|]. split; [|exact Hlc].
  apply (proj1 (interp_type_extend eta X R [] T (Hfresh T (ex_intro _ x Hlookup)) v)).
  exact Hrel.
Qed.

Definition term_environment_covered (Gamma : context) (rho : term_environment) : Prop :=
  forall x v, lookup_term_environment x rho = Some v ->
    exists T, lookup_context x Gamma = Some T.

Lemma term_environment_interprets_lc : forall Gamma eta rho,
  term_environment_interprets Gamma eta rho ->
  term_environment_covered Gamma rho ->
  forall x v, lookup_term_environment x rho = Some v ->
    locally_closed_tm (erase_types v).
Proof.
  intros Gamma eta rho Hinter Hcovered x v Hlookup.
  destruct (Hcovered x v Hlookup) as [T HT].
  destruct (Hinter x T HT) as [v' [Hv [Hred Hlc]]].
  rewrite Hlookup in Hv. inversion Hv; subst.
  exact Hlc.
Qed.

Lemma lc_ty_weaken : forall K T, lc_ty_at K T -> forall K',
  lc_ty_at (K + K') T.
Proof.
  intros K T H; induction H; intros K'; simpl.
  - constructor. lia.
  - constructor.
  - constructor; eauto.
  - replace (S k + K') with (S (k + K')) by lia. constructor; eauto.
  - constructor.
  - constructor.
Qed.

Lemma lc_tm_weaken : forall K k t, lc_tm_at K k t -> forall K' k',
  lc_tm_at (K + K') (k + k') t.
Proof.
  intros K k t H; induction H; intros K' k'; simpl.
  - constructor. lia.
  - constructor.
  - econstructor.
    + eapply lc_ty_weaken; eauto.
    + replace (S k + k') with (S (k + k')) by lia. eauto.
  - econstructor; eauto.
  - replace (S K + K') with (S (K + K')) by lia. econstructor; eauto.
  - econstructor; eauto using lc_ty_weaken.
  - constructor.
  - constructor.
  - econstructor; eauto.
  - constructor.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
Qed.

Lemma apply_environment_preserves_lc : forall K k t,
  lc_tm_at K k t -> forall rho,
  (forall x v, lookup_term_environment x rho = Some v ->
    locally_closed_tm (erase_types v)) ->
  lc_tm_at K k (apply_term_environment rho t).
Proof.
  intros K k t Hlc. induction Hlc; intros rho Henv; simpl.
  - constructor. assumption.
  - destruct (lookup_term_environment x rho) as [v|] eqn:E.
    + pose proof (Henv x v E) as Hcl. unfold locally_closed_tm in Hcl.
      exact (@lc_tm_weaken 0 0 (erase_types v) Hcl K k).
    + constructor.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
  - constructor.
  - constructor.
  - econstructor; eauto.
  - constructor.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
Qed.

Lemma apply_environment_lc : forall rho t,
  locally_closed_tm t ->
  (forall x v, lookup_term_environment x rho = Some v ->
    locally_closed_tm (erase_types v)) ->
  locally_closed_tm (apply_term_environment rho t).
Proof. intros; eapply apply_environment_preserves_lc; eauto. Qed.

Lemma numeric_value_lc : forall n, numeric_value n -> locally_closed_tm n.
Proof. intros n Hn; induction Hn; unfold locally_closed_tm; eauto using lc_tm_at. Qed.

Lemma value_locally_closed : forall v, value v -> locally_closed_tm v.
Proof.
  intros v Hv; inversion Hv; subst.
  - assumption.
  - assumption.
  - unfold locally_closed_tm; constructor.
  - unfold locally_closed_tm; constructor.
  - apply numeric_value_lc. assumption.
Qed.

Lemma lc_ty_open_rec : forall K U T,
  lc_ty_at (S K) T -> lc_ty_at K U ->
  lc_ty_at K (open_ty_rec K U T).
Proof.
  intros K U T Hlc HU. revert K U Hlc HU.
  induction T; intros K' U Hlc HU; inversion Hlc; subst; simpl.
  - destruct (Nat.eqb K' n) eqn:E.
    + apply Nat.eqb_eq in E; subst. exact HU.
    + constructor. apply Nat.eqb_neq in E. lia.
  - constructor.
  - constructor.
    + eapply IHT1; eauto.
    + eapply IHT2; eauto.
  - constructor.
    apply IHT with (K := S K'); [exact H1|].
    replace (S K') with (K' + 1) by lia. eapply lc_ty_weaken; exact HU.
  - constructor.
  - constructor.
Qed.

Lemma lc_tm_open_rec_preserves : forall K k t,
  lc_tm_at K (S k) t -> forall v,
  lc_tm_at K k v -> lc_tm_at K k (open_tm_rec k v t).
Proof.
  intros K k t Hlc. revert K k Hlc. induction t; intros K' k' Hlc v Hv; inversion Hlc; subst; simpl.
  - destruct (Nat.eqb k' n) eqn:E.
    + apply Nat.eqb_eq in E; subst. exact Hv.
    + constructor. apply Nat.eqb_neq in E. lia.
  - constructor.
  - econstructor.
    + assumption.
    + apply IHt with (K := K') (k := S k'); [exact H4|].
      replace (S k') with (k' + 1) by lia.
      pose proof (@lc_tm_weaken K' k' v Hv 0 1) as Hvw.
      replace (K' + 0) with K' in Hvw by lia. exact Hvw.
  - econstructor; eauto.
  - econstructor. apply IHt with (K := S K') (k := k'); [exact H2|].
    pose proof (@lc_tm_weaken K' k' v Hv 1 0) as Hvw.
    replace (K' + 1) with (S K') in Hvw by lia.
    replace (k' + 0) with k' in Hvw by lia. exact Hvw.
  - econstructor; eauto.
  - constructor.
  - constructor.
  - econstructor; eauto.
  - constructor.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
Qed.

Lemma lc_tm_ty_open_rec_preserves : forall K j t,
  lc_tm_at (S K) j t -> forall U,
  lc_ty_at K U -> lc_tm_at K j (open_tm_ty_rec K U t).
Proof.
  intros K j t Hlc. revert K j Hlc. induction t; intros K' j' Hlc U HU; inversion Hlc; subst; simpl.
  - constructor. assumption.
  - constructor.
  - econstructor.
    + eapply lc_ty_open_rec; eauto.
    + eapply IHt; eauto.
  - econstructor; eauto.
  - eapply lc_tm_tabs.
    eapply IHt with (K := S K'); [exact H2|].
    replace (S K') with (K' + 1) by lia. eapply lc_ty_weaken; exact HU.
  - econstructor; eauto using lc_ty_open_rec.
  - constructor.
  - constructor.
  - econstructor; eauto.
  - constructor.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
Qed.

Lemma locally_closed_step : forall t u,
  locally_closed_tm t -> t --> u -> locally_closed_tm u.
Proof.
  intros t u Hlc Hstep. revert Hlc.
  induction Hstep; intros Hlc; inversion Hlc; subst.
  - inversion H5; subst. eapply lc_tm_open_rec_preserves; eauto using value_locally_closed.
  - econstructor.
    + apply IHHstep. exact H4.
    + exact H5.
  - econstructor.
    + exact H4.
    + apply IHHstep. exact H5.
  - inversion H5; subst. eapply lc_tm_ty_open_rec_preserves; eauto.
  - econstructor; [apply IHHstep; exact H4|exact H5].
  - apply lc_tm_succ. apply IHHstep. exact H2.
  - apply lc_tm_rec; [apply IHHstep; exact H6|exact H7|exact H8].
  - apply lc_tm_rec; [exact H6|apply IHHstep; exact H7|exact H8].
  - apply lc_tm_rec; [exact H6|exact H7|apply IHHstep; exact H8].
  - exact H7.
  - apply lc_tm_app.
    + apply lc_tm_app; [exact H9|apply numeric_value_lc; exact H].
    + apply lc_tm_rec; [apply numeric_value_lc; exact H|exact H8|exact H9].
  - assumption.
  - assumption.
  - apply lc_tm_if; [apply IHHstep; exact H6|exact H7|exact H8].
  - assumption.
  - assumption.
Qed.

Lemma lookup_context_update_eq : forall Gamma x T,
  lookup_context x (update Gamma x T) = Some T.
Proof. intros; simpl. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma lookup_context_update_neq : forall Gamma x y T,
  x <> y -> lookup_context x (update Gamma y T) = lookup_context x Gamma.
Proof.
  intros; simpl. assert (Nat.eqb x y = false) by (apply Nat.eqb_neq; congruence).
  now rewrite H0.
Qed.

Lemma term_environment_interprets_update : forall Gamma eta rho x T v,
  term_environment_interprets Gamma eta rho ->
  candidate_rel (interp_type eta [] T) v ->
  locally_closed_tm (erase_types v) ->
  term_environment_interprets (update Gamma x T) eta ((x,v)::rho).
Proof.
  intros Gamma eta rho x T v Hinter Hv Hvlc y S Hlookup.
  simpl in Hlookup. destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y. inversion Hlookup; subst S.
    exists v. split; [simpl; rewrite Nat.eqb_refl; reflexivity|].
    split; assumption.
  - destruct (Hinter y S Hlookup) as [v0 [Hv0 [HR Hlc]]]. exists v0; split.
    + simpl. rewrite E. exact Hv0.
    + split; assumption.
Qed.

Lemma term_environment_covered_update : forall Gamma rho x v T,
  term_environment_covered Gamma rho ->
  term_environment_covered (update Gamma x T) ((x,v)::rho).
Proof.
  intros Gamma rho x v T Hcov y w Hlookup.
  simpl in Hlookup. destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y. inversion Hlookup; subst.
    exists T. apply lookup_context_update_eq.
  - destruct (Hcov y w Hlookup) as [S HS]. exists S.
    simpl. rewrite E. exact HS.
Qed.

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  (* Complete the proof of normalization. *)
Qed.

End SystemFNormalizationIfNondeterminismRecursionHardTask.
