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

Lemma sn_step : forall t u, strongly_normalizing t -> t --> u ->
  strongly_normalizing u.
Proof. intros t u H; inversion H; auto. Qed.

Lemma sn_from_successors : forall t,
  (forall u, t --> u -> strongly_normalizing u) -> strongly_normalizing t.
Proof. intros; constructor; auto. Qed.

Definition candidate (R : tm -> Prop) : Prop :=
  (forall t, R t -> locally_closed_tm t /\ strongly_normalizing t) /\
  (forall t, locally_closed_tm t -> strongly_normalizing t -> ~ value t ->
    (forall u, t --> u -> R u) -> R t).

Definition basic (t : tm) :=
  locally_closed_tm t /\ strongly_normalizing t.

Lemma basic_candidate : candidate basic.
Proof.
  split; [intros t H; exact H|].
  intros t Hlc Hsn _ _; exact (conj Hlc Hsn).
Qed.

Fixpoint interp_core (T : ty) (rho : atom -> tm -> Prop)
    (sigma : list (tm -> Prop)) (t : tm) {struct T} : Prop :=
  forall v, t -->* v -> value v ->
  match T with
  | Ty_BVar i => nth i sigma basic v
  | Ty_FVar X => rho X v
  | Ty_Bool => v = tm_true \/ v = tm_false
  | Ty_Nat => numeric_value v
  | Ty_Arrow A B =>
      forall w, basic w /\ interp_core A rho sigma w ->
        basic (tm_app v w) /\ interp_core B rho sigma (tm_app v w)
  | Ty_All A =>
      forall U R, locally_closed_ty U -> candidate R ->
        basic (tm_tapp v U) /\ interp_core A rho (R :: sigma) (tm_tapp v U)
  end.

Definition interp T rho sigma t :=
  basic t /\ interp_core T rho sigma t.

Lemma interp_basic : forall T rho sigma t,
  interp T rho sigma t -> basic t.
Proof. intros T rho sigma t H; exact (proj1 H). Qed.

Lemma numeric_no_step : forall n u, numeric_value n -> ~ n --> u.
Proof.
  intros n u Hn; revert u; induction Hn; intros u Hs; inversion Hs; subst.
  eapply IHHn; eauto.
Qed.

Lemma value_no_step : forall v u, value v -> ~ v --> u.
Proof.
  intros v u Hv Hs; inversion Hv; subst; try solve [inversion Hs].
  eapply numeric_no_step; eauto.
Qed.

Lemma multi_value : forall v w, value v -> v -->* w -> v = w.
Proof.
  intros v w Hv H; inversion H; subst; auto.
  exfalso; eapply value_no_step; eauto.
Qed.

Lemma lc_ty_weaken : forall T K k,
  lc_ty_at K T -> lc_ty_at (K + k) T.
Proof.
  intros T K k H; induction H; simpl; constructor; auto; try lia.
Qed.

Lemma lc_tm_weaken : forall t K k m n,
  lc_tm_at K k t -> lc_tm_at (K + m) (k + n) t.
Proof.
  intros t K k m n H; induction H; simpl; constructor; eauto;
    try (eapply lc_ty_weaken; eauto); try lia.
Qed.

Lemma lc_ty_open_rec : forall T K,
  lc_ty_at (S K) T -> forall U, locally_closed_ty U ->
  lc_ty_at K (open_ty_rec K U T).
Proof.
  intros T K H; remember (S K) as depth eqn:Heq;
    revert K Heq; induction H; intros depth Hdepth U HU; subst; simpl;
    try solve [constructor; eauto].
  - destruct (Nat.eqb_spec depth i); subst.
    + replace i with (0 + i) by lia.
      eapply lc_ty_weaken; eauto.
    + constructor; lia.
Qed.

Lemma lc_tm_open_rec : forall t K k,
  lc_tm_at K (S k) t -> forall u, lc_tm_at K 0 u ->
  lc_tm_at K k (open_tm_rec k u t).
Proof.
  intros t K k H; remember (S k) as depth eqn:Heq;
    revert k Heq; induction H; intros depth Hdepth u HU; subst; simpl;
    try solve [constructor; eauto].
  - destruct (Nat.eqb_spec depth i); subst.
    + replace i with (0 + i) by lia.
      replace K with (K + 0) by lia.
      eapply lc_tm_weaken; eauto.
    + constructor; lia.
  - constructor; eauto. eapply IHlc_tm_at; eauto.
    replace (S K) with (K + 1) by lia.
    replace 0 with (0 + 0) by lia.
    eapply lc_tm_weaken; eauto.
Qed.

Lemma lc_tm_open_ty_rec : forall t K k,
  lc_tm_at (S K) k t -> forall U, locally_closed_ty U ->
  lc_tm_at K k (open_tm_ty_rec K U t).
Proof.
  intros t K k H; remember (S K) as depth eqn:Heq;
    revert K Heq; induction H; intros depth Hdepth U HU; subst; simpl;
    try solve [constructor; eauto].
  - constructor.
    + eapply lc_ty_open_rec; eauto.
    + eapply IHlc_tm_at; eauto.
  - constructor. eapply IHlc_tm_at; eauto.
    eapply lc_ty_open_rec; eauto.
Qed.

Lemma numeric_lc : forall n, numeric_value n -> locally_closed_tm n.
Proof.
  intros n H; induction H; unfold locally_closed_tm in *; constructor; auto.
Qed.

Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof.
  intros v Hv; inversion Hv; subst; eauto using numeric_lc with core;
    unfold locally_closed_tm; constructor.
Qed.

Lemma step_lc : forall t u, locally_closed_tm t -> t --> u ->
  locally_closed_tm u.
Proof.
  intros t u Hlc Hs; revert Hlc; induction Hs; intro Hlc;
    unfold locally_closed_tm in *; inversion Hlc; subst;
    eauto 6 using lc_tm_open_rec, lc_tm_open_ty_rec, value_lc,
      numeric_lc with core.
  - unfold open_tm. eapply lc_tm_open_rec; eauto using value_lc.
    inversion H; subst; assumption.
  - unfold open_tm_ty. eapply lc_tm_open_ty_rec; eauto.
    inversion H; subst; assumption.
  - apply lc_tm_app.
    + apply lc_tm_app; [assumption | apply numeric_lc; assumption].
    + apply lc_tm_rec; [apply numeric_lc; assumption | assumption | assumption].
Qed.

Lemma interp_step : forall T rho sigma t u,
  interp T rho sigma t -> t --> u -> interp T rho sigma u.
Proof.
  intros T rho sigma t u [[Hlc Hsn] Hvalue] Hstep.
  split; [split|].
  - eapply step_lc; eauto.
  - eapply sn_step; eauto.
  - destruct T; simpl in *; intros v Hmulti Hv;
      eapply Hvalue; eauto using multi_step.
Qed.

Lemma interp_neutral : forall T rho sigma t,
  locally_closed_tm t -> strongly_normalizing t -> ~ value t ->
  (forall u, t --> u -> interp T rho sigma u) -> interp T rho sigma t.
Proof.
  intros T rho sigma t Hlc Hsn Hneutral Hnext.
  split; [exact (conj Hlc Hsn)|].
  destruct T; simpl in *; intros v Hmulti Hv; inversion Hmulti; subst;
    try contradiction;
    match goal with
    | H : t --> ?u, Hm : ?u -->* v |- _ =>
        destruct (Hnext u H) as [_ Hvalues];
        exact (Hvalues v Hm Hv)
    end.
Qed.

Lemma interp_value_intro : forall T rho sigma v,
  basic v -> value v ->
  (match T with
  | Ty_BVar i => nth i sigma basic v
  | Ty_FVar X => rho X v
  | Ty_Bool => v = tm_true \/ v = tm_false
  | Ty_Nat => numeric_value v
  | Ty_Arrow A B => forall w, interp A rho sigma w ->
      interp B rho sigma (tm_app v w)
  | Ty_All A => forall U R, locally_closed_ty U -> candidate R ->
      interp A rho (R :: sigma) (tm_tapp v U)
  end) -> interp T rho sigma v.
Proof.
  intros T rho sigma v Hbasic Hv Hcore; split; auto.
  destruct T; simpl in *; intros w Hmulti Hvw;
    pose proof (multi_value v w Hv Hmulti) as Heq; subst; exact Hcore.
Qed.

Lemma interp_app : forall A B rho sigma f a,
  interp (Ty_Arrow A B) rho sigma f ->
  interp A rho sigma a -> interp B rho sigma (tm_app f a).
Proof.
  intros A B rho sigma f a Hf Ha.
  pose proof (proj2 (proj1 Hf)) as Hsnf.
  pose proof (proj2 (proj1 Ha)) as Hsna.
  revert a Ha Hsna; induction Hsnf as [f Hsnf IHf];
    intros a Ha Hsna; induction Hsna as [a Hsna IHa].
  assert (Hnext : forall u, tm_app f a --> u -> interp B rho sigma u).
  { intros u Hstep; inversion Hstep; subst.
    - destruct Hf as [_ Hcore]. simpl in Hcore.
      eapply interp_step; [eapply Hcore; eauto using multi_refl, v_abs|exact Hstep].
    - eapply IHf; eauto using interp_step.
      exact (proj2 (proj1 Ha)).
    - eapply IHa; eauto using interp_step.
  }
  eapply interp_neutral.
  - unfold locally_closed_tm in *; constructor;
      [exact (proj1 (proj1 Hf)) | exact (proj1 (proj1 Ha))].
  - apply sn_from_successors; intros u Hstep.
    exact (proj2 (interp_basic _ _ _ _ (Hnext u Hstep))).
  - intros H; inversion H; subst; try discriminate; inversion H0.
  - exact Hnext.
Qed.

Lemma interp_tapp : forall A rho sigma f U R,
  interp (Ty_All A) rho sigma f -> locally_closed_ty U ->
  candidate R -> interp A rho (R :: sigma) (tm_tapp f U).
Proof.
  intros A rho sigma f U R Hf HU HR.
  pose proof (proj2 (proj1 Hf)) as Hsnf.
  induction Hsnf as [f Hsnf IHf].
  assert (Hnext : forall u, tm_tapp f U --> u ->
    interp A rho (R :: sigma) u).
  { intros u Hstep; inversion Hstep; subst.
    - destruct Hf as [_ Hcore]. simpl in Hcore.
      eapply interp_step; [eapply Hcore; eauto using multi_refl, v_tabs|exact Hstep].
    - eapply IHf; eauto using interp_step.
  }
  eapply interp_neutral.
  - unfold locally_closed_tm in *; constructor;
      [exact (proj1 (proj1 Hf)) | exact HU].
  - apply sn_from_successors; intros u Hstep.
    exact (proj2 (interp_basic _ _ _ _ (Hnext u Hstep))).
  - intros H; inversion H; subst; try discriminate; inversion H0.
  - exact Hnext.
Qed.

Lemma interp_choice : forall T rho sigma a b,
  interp T rho sigma a -> interp T rho sigma b ->
  interp T rho sigma (tm_choice a b).
Proof.
  intros T rho sigma a b Ha Hb.
  assert (Hnext : forall u, tm_choice a b --> u -> interp T rho sigma u).
  { intros u Hstep; inversion Hstep; subst; assumption. }
  eapply interp_neutral.
  - unfold locally_closed_tm in *; constructor;
      [exact (proj1 (proj1 Ha)) | exact (proj1 (proj1 Hb))].
  - apply sn_from_successors; intros u Hstep.
    exact (proj2 (interp_basic _ _ _ _ (Hnext u Hstep))).
  - intros H; inversion H; subst; try discriminate; inversion H0.
  - exact Hnext.
Qed.

Lemma interp_if : forall T rho sigma c a b,
  interp Ty_Bool rho sigma c ->
  interp T rho sigma a -> interp T rho sigma b ->
  interp T rho sigma (tm_if c a b).
Proof.
  intros T rho sigma c a b Hc Ha Hb.
  pose proof (proj2 (proj1 Hc)) as Hsnc.
  induction Hsnc as [c Hsnc IHc].
  assert (Hnext : forall u, tm_if c a b --> u -> interp T rho sigma u).
  { intros u Hstep; inversion Hstep; subst; eauto.
    eapply IHc; eauto using interp_step.
  }
  eapply interp_neutral.
  - unfold locally_closed_tm in *; constructor;
      [exact (proj1 (proj1 Hc)) | exact (proj1 (proj1 Ha)) | exact (proj1 (proj1 Hb))].
  - apply sn_from_successors; intros u Hstep.
    exact (proj2 (interp_basic _ _ _ _ (Hnext u Hstep))).
  - intros H; inversion H; subst; try discriminate; inversion H0.
  - exact Hnext.
Qed.

Lemma interp_numeric : forall rho sigma n,
  numeric_value n -> interp Ty_Nat rho sigma n.
Proof.
  intros rho sigma n Hn.
  eapply interp_value_intro; eauto using v_nat.
  split; [eauto using numeric_lc|].
  apply sn_from_successors; intros u Hstep.
  exfalso; eapply numeric_no_step; eauto.
Qed.

Lemma interp_succ : forall rho sigma n,
  interp Ty_Nat rho sigma n -> interp Ty_Nat rho sigma (tm_succ n).
Proof.
  intros rho sigma n Hn.
  pose proof (proj2 (proj1 Hn)) as Hsn.
  induction Hsn as [n Hsn IHn].
  assert (Hnext : forall u, tm_succ n --> u -> interp Ty_Nat rho sigma u).
  { intros u Hstep; inversion Hstep; subst.
    eapply IHn; [eassumption | eapply interp_step; eauto].
  }
  split; [|simpl].
  - unfold basic, locally_closed_tm in *; split.
    + constructor. exact (proj1 (proj1 Hn)).
    + apply sn_from_successors; intros u Hstep.
      exact (proj2 (interp_basic _ _ _ _ (Hnext u Hstep))).
  - intros v Hmulti Hv. inversion Hmulti; subst.
    + inversion Hv; subst; try discriminate.
      inversion H; subst; assumption.
    + match goal with
      | H : tm_succ n --> ?u, Hm : ?u -->* v |- _ =>
          destruct (Hnext u H) as [_ Hcore];
          exact (Hcore v Hm Hv)
      end.
Qed.

Lemma numeric_dec : forall t, {numeric_value t} + {~ numeric_value t}.
Proof.
  induction t; try solve [right; intro H; inversion H].
  - left; constructor.
  - destruct IHt as [H | H].
    + left; constructor; assumption.
    + right; intro Hnv; inversion Hnv; contradiction.
Qed.

Lemma interp_rec_num : forall T rho sigma n,
  numeric_value n -> forall b s,
  interp T rho sigma b ->
  interp (Ty_Arrow Ty_Nat (Ty_Arrow T T)) rho sigma s ->
  interp T rho sigma (tm_natrec n b s).
Proof.
  intros T rho sigma n Hnum; induction Hnum.
  all: intros b s Hb Hs;
    pose proof (proj2 (proj1 Hb)) as Hsnb;
    revert s Hs Hb;
    induction Hsnb as [b Hsnb IHb]; intros s Hs Hb;
    pose proof (proj2 (proj1 Hs)) as Hsns;
    revert Hs; induction Hsns as [s Hsns IHs]; intro Hs.
  - assert (Hnext : forall u, tm_natrec tm_zero b s --> u ->
      interp T rho sigma u).
    { intros u Hstep; inversion Hstep; subst.
      + inversion H2.
      + eapply IHb; eauto using interp_step.
      + eapply IHs; eauto using interp_step.
      + exact Hb.
    }
    eapply interp_neutral.
    + unfold locally_closed_tm in *; constructor;
        [constructor|exact (proj1 (proj1 Hb))|exact (proj1 (proj1 Hs))].
    + apply sn_from_successors; intros u Hstep.
      exact (proj2 (interp_basic _ _ _ _ (Hnext u Hstep))).
    + intros Hval; inversion Hval; subst; try discriminate;
        match goal with
        | Hbad : numeric_value (tm_natrec _ _ _) |- _ => inversion Hbad
        end.
    + exact Hnext.
  - assert (Hnext : forall u, tm_natrec (tm_succ n) b s --> u ->
      interp T rho sigma u).
    { intros u Hstep; inversion Hstep; subst.
      + exfalso; eapply numeric_no_step; [constructor; exact Hnum | exact H2].
      + eapply IHb; eauto using interp_step.
      + eapply IHs; eauto using interp_step.
      + eapply interp_app.
        * eapply interp_app; [exact Hs | eapply interp_numeric; eauto].
        * eapply IHHnum; eauto.
    }
    eapply interp_neutral.
    + unfold locally_closed_tm in *; constructor;
        [constructor; apply numeric_lc; exact Hnum|
         exact (proj1 (proj1 Hb))|exact (proj1 (proj1 Hs))].
    + apply sn_from_successors; intros u Hstep.
      exact (proj2 (interp_basic _ _ _ _ (Hnext u Hstep))).
    + intros Hval; inversion Hval; subst; try discriminate;
        match goal with
        | Hbad : numeric_value (tm_natrec _ _ _) |- _ => inversion Hbad
        end.
    + exact Hnext.
Qed.

Lemma interp_rec : forall T rho sigma n b s,
  interp Ty_Nat rho sigma n -> interp T rho sigma b ->
  interp (Ty_Arrow Ty_Nat (Ty_Arrow T T)) rho sigma s ->
  interp T rho sigma (tm_natrec n b s).
Proof.
  intros T rho sigma n b s Hn Hb Hs.
  pose proof (proj2 (proj1 Hn)) as Hsnn.
  induction Hsnn as [n Hsnn IHn].
  destruct (numeric_dec n) as [Hnum | Hnot].
  - eapply interp_rec_num; eauto.
  - assert (Hnext : forall u, tm_natrec n b s --> u ->
      interp T rho sigma u).
    { intros u Hstep; inversion Hstep; subst.
      + eapply IHn; eauto using interp_step.
      + contradiction.
      + contradiction.
      + exfalso; apply Hnot; constructor.
      + exfalso; apply Hnot; constructor; assumption.
    }
    eapply interp_neutral.
    + unfold locally_closed_tm in *; constructor;
        [exact (proj1 (proj1 Hn))|
         exact (proj1 (proj1 Hb))|exact (proj1 (proj1 Hs))].
    + apply sn_from_successors; intros u Hstep.
      exact (proj2 (interp_basic _ _ _ _ (Hnext u Hstep))).
    + intros Hval; inversion Hval; subst; try discriminate;
        match goal with
        | Hbad : numeric_value (tm_natrec _ _ _) |- _ => inversion Hbad
        end.
    + exact Hnext.
Qed.

Lemma interp_candidate : forall T rho sigma,
  candidate (interp T rho sigma).
Proof.
  intros T rho sigma; split.
  - intros t H; exact (interp_basic _ _ _ _ H).
  - intros t Hlc Hsn Hnv Hnext.
    eapply interp_neutral; eauto.
Qed.

Fixpoint map_ty (theta : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => theta X
  | Ty_Arrow A B => Ty_Arrow (map_ty theta A) (map_ty theta B)
  | Ty_All A => Ty_All (map_ty theta A)
  | Ty_Bool => Ty_Bool
  | Ty_Nat => Ty_Nat
  end.

Fixpoint map_tm_ty (theta : atom -> ty) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T b => tm_abs (map_ty theta T) (map_tm_ty theta b)
  | tm_app a b => tm_app (map_tm_ty theta a) (map_tm_ty theta b)
  | tm_tabs b => tm_tabs (map_tm_ty theta b)
  | tm_tapp a T => tm_tapp (map_tm_ty theta a) (map_ty theta T)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if c a b => tm_if (map_tm_ty theta c) (map_tm_ty theta a) (map_tm_ty theta b)
  | tm_zero => tm_zero
  | tm_succ a => tm_succ (map_tm_ty theta a)
  | tm_natrec n b s => tm_natrec (map_tm_ty theta n) (map_tm_ty theta b) (map_tm_ty theta s)
  | tm_choice a b => tm_choice (map_tm_ty theta a) (map_tm_ty theta b)
  end.

Fixpoint map_tm (gamma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => gamma x
  | tm_abs T b => tm_abs T (map_tm gamma b)
  | tm_app a b => tm_app (map_tm gamma a) (map_tm gamma b)
  | tm_tabs b => tm_tabs (map_tm gamma b)
  | tm_tapp a T => tm_tapp (map_tm gamma a) T
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if c a b => tm_if (map_tm gamma c) (map_tm gamma a) (map_tm gamma b)
  | tm_zero => tm_zero
  | tm_succ a => tm_succ (map_tm gamma a)
  | tm_natrec n b s => tm_natrec (map_tm gamma n) (map_tm gamma b) (map_tm gamma s)
  | tm_choice a b => tm_choice (map_tm gamma a) (map_tm gamma b)
  end.

Definition sem_tm theta gamma t := map_tm gamma (map_tm_ty theta t).

Definition tupdate (theta : atom -> ty) (X : atom) (U : ty) : atom -> ty :=
  fun Y => if Nat.eqb X Y then U else theta Y.

Definition vupdate (gamma : atom -> tm) (x : atom) (v : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then v else gamma y.

Definition rupdate (rho : atom -> tm -> Prop) (X : atom) (R : tm -> Prop) :
    atom -> tm -> Prop :=
  fun Y => if Nat.eqb X Y then R else rho Y.

Fixpoint ty_fvs (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow A B => ty_fvs A ++ ty_fvs B
  | Ty_All A => ty_fvs A
  | Ty_Bool | Ty_Nat => []
  end.

Fixpoint tm_fvs (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs _ b | tm_tabs b | tm_succ b | tm_tapp b _ => tm_fvs b
  | tm_app a b | tm_choice a b => tm_fvs a ++ tm_fvs b
  | tm_if c a b | tm_natrec c a b => tm_fvs c ++ tm_fvs a ++ tm_fvs b
  | tm_true | tm_false | tm_zero => []
  end.

Fixpoint tm_ty_fvs (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_fvar _ | tm_true | tm_false | tm_zero => []
  | tm_abs T b => ty_fvs T ++ tm_ty_fvs b
  | tm_app a b | tm_choice a b => tm_ty_fvs a ++ tm_ty_fvs b
  | tm_tabs b | tm_succ b => tm_ty_fvs b
  | tm_tapp a T => tm_ty_fvs a ++ ty_fvs T
  | tm_if c a b | tm_natrec c a b =>
      tm_ty_fvs c ++ tm_ty_fvs a ++ tm_ty_fvs b
  end.

Lemma max_list_bound : forall xs x,
  In x xs -> x <= fold_right Nat.max 0 xs.
Proof.
  induction xs as [|y xs IH]; intros x H; simpl in *.
  - contradiction.
  - destruct H as [<-|H]; [lia| specialize (IH _ H); lia].
Qed.

Definition fresh (xs : list atom) := S (fold_right Nat.max 0 xs).

Lemma fresh_notin : forall xs, ~ In (fresh xs) xs.
Proof.
  intros xs H; pose proof (max_list_bound xs _ H); unfold fresh in *; lia.
Qed.

Lemma open_ty_rec_id : forall T K,
  lc_ty_at K T -> forall k U, K <= k -> open_ty_rec k U T = T.
Proof.
  intros T K H; induction H; intros depth U Hle; simpl;
    try (f_equal; eauto with arith); try reflexivity.
  - destruct (Nat.eqb depth i) eqn:Heq; [apply Nat.eqb_eq in Heq; lia|reflexivity].
Qed.

Lemma open_tm_rec_id : forall t K k,
  lc_tm_at K k t -> forall depth u, k <= depth ->
    open_tm_rec depth u t = t.
Proof.
  intros t K k H; induction H; intros depth u Hle; simpl;
    try (f_equal; eauto with arith); try reflexivity.
  - destruct (Nat.eqb depth i) eqn:Heq; [apply Nat.eqb_eq in Heq; lia|reflexivity].
Qed.

Lemma open_tm_ty_rec_id : forall t K k,
  lc_tm_at K k t -> forall depth U, K <= depth ->
    open_tm_ty_rec depth U t = t.
Proof.
  intros t K k H; induction H; intros depth U Hle; simpl;
    try (f_equal; eauto using open_ty_rec_id with arith); try reflexivity.
Qed.

Lemma map_tm_ty_open_tm : forall t theta k x,
  map_tm_ty theta (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k (tm_fvar x) (map_tm_ty theta t).
Proof.
  induction t; intros theta k x; simpl; try (f_equal; eauto); try reflexivity.
  destruct (Nat.eqb k n); reflexivity.
Qed.

Lemma map_tm_open : forall t gamma x v k,
  ~ In x (tm_fvs t) ->
  (forall y, locally_closed_tm (gamma y)) ->
  map_tm (vupdate gamma x v) (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k v (map_tm gamma t).
Proof.
  induction t; intros gamma x v k Hfresh Hgamma; simpl in *;
    try solve [f_equal; eauto 8]; try reflexivity.
  - destruct (Nat.eqb k n); simpl; [unfold vupdate; rewrite Nat.eqb_refl|]; reflexivity.
  - unfold vupdate.
    assert (x <> a) by (intro Heq; apply Hfresh; subst; left; reflexivity).
    apply Nat.eqb_neq in H as Heq; rewrite Heq.
    symmetry. eapply open_tm_rec_id with (K := 0) (k := 0);
      [apply Hgamma|lia].
  - repeat rewrite in_app_iff in Hfresh.
    f_equal; [apply IHt1|apply IHt2]; tauto.
  - repeat rewrite in_app_iff in Hfresh.
    f_equal; [apply IHt1|apply IHt2|apply IHt3]; tauto.
  - repeat rewrite in_app_iff in Hfresh.
    f_equal; [apply IHt1|apply IHt2|apply IHt3]; tauto.
  - repeat rewrite in_app_iff in Hfresh.
    f_equal; [apply IHt1|apply IHt2]; tauto.
Qed.

Lemma map_tm_open_tm_ty : forall t gamma k U,
  (forall y, locally_closed_tm (gamma y)) ->
  map_tm gamma (open_tm_ty_rec k U t) =
  open_tm_ty_rec k U (map_tm gamma t).
Proof.
  induction t; intros gamma k U Hgamma; simpl;
    try (f_equal; eauto); try reflexivity.
  symmetry. eapply open_tm_ty_rec_id with (K := 0) (k := 0);
    [apply Hgamma|lia].
Qed.

Lemma map_ty_open : forall T theta X U k,
  ~ In X (ty_fvs T) ->
  (forall Y, locally_closed_ty (theta Y)) ->
  map_ty (tupdate theta X U) (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k U (map_ty theta T).
Proof.
  induction T; intros theta X U k Hfresh Htheta; simpl in *;
    try solve [f_equal; eauto]; try reflexivity.
  - destruct (Nat.eqb k n); simpl; [unfold tupdate; rewrite Nat.eqb_refl|]; reflexivity.
  - unfold tupdate.
    assert (X <> a) by (intro Heq; apply Hfresh; subst; left; reflexivity).
    apply Nat.eqb_neq in H as Heq; rewrite Heq.
    symmetry. eapply open_ty_rec_id with (K := 0);
      [apply Htheta|lia].
  - repeat rewrite in_app_iff in Hfresh.
    f_equal; [apply IHT1|apply IHT2]; tauto.
Qed.

Lemma map_tm_ty_open_ty : forall t theta X U k,
  ~ In X (tm_ty_fvs t) ->
  (forall Y, locally_closed_ty (theta Y)) ->
  map_tm_ty (tupdate theta X U) (open_tm_ty_rec k (Ty_FVar X) t) =
  open_tm_ty_rec k U (map_tm_ty theta t).
Proof.
  induction t; intros theta X U k Hfresh Htheta; simpl in *;
    try solve [f_equal; eauto using map_ty_open]; try reflexivity.
  - rewrite in_app_iff in Hfresh.
    f_equal; [eapply map_ty_open|eapply IHt]; eauto; tauto.
  - rewrite in_app_iff in Hfresh.
    f_equal; [eapply IHt1|eapply IHt2]; eauto; tauto.
  - rewrite in_app_iff in Hfresh.
    f_equal; [eapply IHt|eapply map_ty_open]; eauto; tauto.
  - repeat rewrite in_app_iff in Hfresh.
    f_equal; [eapply IHt1|eapply IHt2|eapply IHt3]; eauto; tauto.
  - repeat rewrite in_app_iff in Hfresh.
    f_equal; [eapply IHt1|eapply IHt2|eapply IHt3]; eauto; tauto.
  - rewrite in_app_iff in Hfresh.
    f_equal; [eapply IHt1|eapply IHt2]; eauto; tauto.
Qed.

Lemma lc_ty_close_rec : forall T K X,
  lc_ty_at K (open_ty_rec K (Ty_FVar X) T) ->
  lc_ty_at (S K) T.
Proof.
  induction T; intros K X Hlc; simpl in Hlc;
    try solve [constructor; eauto].
  - destruct (Nat.eqb K n) eqn:Heq.
    + apply Nat.eqb_eq in Heq; subst; constructor; lia.
    + inversion Hlc; subst; constructor; lia.
  - inversion Hlc; subst; constructor; [eapply IHT1|eapply IHT2]; eauto.
  - inversion Hlc; subst; constructor; eapply IHT; eauto.
Qed.

Lemma lc_tm_close_rec : forall t K k x,
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) ->
  lc_tm_at K (S k) t.
Proof.
  induction t; intros K k x Hlc; simpl in Hlc;
    try solve [inversion Hlc; subst; constructor; eauto].
  - destruct (Nat.eqb k n) eqn:Heq.
    + apply Nat.eqb_eq in Heq; subst; constructor; lia.
    + inversion Hlc; subst; constructor; lia.
Qed.

Lemma lc_tm_ty_close_rec : forall t K k X,
  lc_tm_at K k (open_tm_ty_rec K (Ty_FVar X) t) ->
  lc_tm_at (S K) k t.
Proof.
  induction t; intros K k X Hlc; simpl in Hlc;
    try (inversion Hlc; subst; constructor; eauto using lc_ty_close_rec).
Qed.

Lemma wf_lc : forall Delta T,
  wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T Hwf; induction Hwf; unfold locally_closed_ty in *;
    eauto with core.
  - constructor. specialize (H0 (fresh L) (fresh_notin L)).
    unfold open_ty in H0.
    eapply lc_ty_close_rec; eauto.
Qed.

Lemma lc_map_ty : forall T K theta,
  lc_ty_at K T -> (forall X, locally_closed_ty (theta X)) ->
  lc_ty_at K (map_ty theta T).
Proof.
  intros T K theta H; induction H; intro Htheta; simpl;
    try (constructor; eauto).
  replace k with (0 + k) by lia.
  eapply lc_ty_weaken. apply Htheta.
Qed.

Lemma lc_map_tm_ty : forall t K k theta,
  lc_tm_at K k t -> (forall X, locally_closed_ty (theta X)) ->
  lc_tm_at K k (map_tm_ty theta t).
Proof.
  intros t K k theta H; induction H; intro Htheta; simpl;
    try (constructor; eauto using lc_map_ty).
Qed.

Lemma lc_map_tm : forall t K k gamma,
  lc_tm_at K k t -> (forall x, locally_closed_tm (gamma x)) ->
  lc_tm_at K k (map_tm gamma t).
Proof.
  intros t K k gamma H; induction H; intro Hgamma; simpl;
    try (constructor; eauto).
  replace K with (0 + K) by lia.
  replace k with (0 + k) by lia.
  eapply lc_tm_weaken. apply Hgamma.
Qed.

Lemma typed_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T Htyping; induction Htyping;
    unfold locally_closed_tm in *; eauto with core.
  - constructor.
    + eapply wf_lc; eauto.
    + specialize (H0 (fresh L) (fresh_notin L)).
      specialize (H1 (fresh L) (fresh_notin L)).
      unfold open_tm in H1.
      eapply lc_tm_close_rec; eauto.
  - constructor.
    specialize (H0 (fresh L) (fresh_notin L)).
    unfold open_tm_ty in H0.
    eapply lc_tm_ty_close_rec; eauto.
  - constructor; [exact IHHtyping|].
    change (locally_closed_ty U). eapply wf_lc; eauto.
Qed.

Lemma interp_ext : forall T k,
  lc_ty_at k T -> forall rho1 rho2 sigma1 sigma2,
  (forall X, In X (ty_fvs T) -> forall t,
      rho1 X t <-> rho2 X t) ->
  (forall i, i < k -> forall t,
      nth i sigma1 basic t <-> nth i sigma2 basic t) ->
  forall t, interp T rho1 sigma1 t <-> interp T rho2 sigma2 t.
Proof.
  intros T k Hlc; induction Hlc; intros rho1 rho2 sigma1 sigma2 Hr Hs t;
    unfold interp; simpl; split; intros [Hb Hcore]; split; auto;
    intros v Hmulti Hv; specialize (Hcore v Hmulti Hv).
  - apply (proj1 (Hs i H v)); exact Hcore.
  - apply (proj2 (Hs i H v)); exact Hcore.
  - apply (proj1 (Hr X (or_introl eq_refl) v)); exact Hcore.
  - apply (proj2 (Hr X (or_introl eq_refl) v)); exact Hcore.
  - assert (Hr1 : forall X, In X (ty_fvs T1) -> forall u,
        rho1 X u <-> rho2 X u).
    { intros X Hin; apply Hr; simpl; apply in_or_app; auto. }
    assert (Hr2 : forall X, In X (ty_fvs T2) -> forall u,
        rho1 X u <-> rho2 X u).
    { intros X Hin; apply Hr; simpl; apply in_or_app; auto. }
    intros w Hw. apply (proj1 (IHHlc2 _ _ _ _ Hr2 Hs _)).
    apply Hcore. apply (proj2 (IHHlc1 _ _ _ _ Hr1 Hs _)); exact Hw.
  - assert (Hr1 : forall X, In X (ty_fvs T1) -> forall u,
        rho1 X u <-> rho2 X u).
    { intros X Hin; apply Hr; simpl; apply in_or_app; auto. }
    assert (Hr2 : forall X, In X (ty_fvs T2) -> forall u,
        rho1 X u <-> rho2 X u).
    { intros X Hin; apply Hr; simpl; apply in_or_app; auto. }
    intros w Hw. apply (proj2 (IHHlc2 _ _ _ _ Hr2 Hs _)).
    apply Hcore. apply (proj1 (IHHlc1 _ _ _ _ Hr1 Hs _)); exact Hw.
  - intros U R HU HR.
    assert (Hs' : forall i, i < S k -> forall w,
      nth i (R :: sigma1) basic w <-> nth i (R :: sigma2) basic w).
    { intros [|i] Hi w; simpl; [tauto|apply Hs; lia]. }
    apply (proj1 (IHHlc rho1 rho2 (R :: sigma1) (R :: sigma2)
      Hr Hs' (tm_tapp v U))). apply Hcore; assumption.
  - intros U R HU HR.
    assert (Hs' : forall i, i < S k -> forall w,
      nth i (R :: sigma1) basic w <-> nth i (R :: sigma2) basic w).
    { intros [|i] Hi w; simpl; [tauto|apply Hs; lia]. }
    apply (proj2 (IHHlc rho1 rho2 (R :: sigma1) (R :: sigma2)
      Hr Hs' (tm_tapp v U))). apply Hcore; assumption.
Qed.

Lemma interp_abs : forall A B rho sigma U body,
  value (tm_abs U body) ->
  (forall v, value v -> interp A rho sigma v ->
    interp B rho sigma (open_tm body v)) ->
  interp (Ty_Arrow A B) rho sigma (tm_abs U body).
Proof.
  intros A B rho sigma U body Hval Hbody.
  eapply interp_value_intro; eauto.
  - split; [eapply value_lc; eauto|].
    apply sn_from_successors; intros u Hstep.
    exfalso; eapply value_no_step; eauto.
  - intros w Hw.
    pose proof (proj2 (proj1 Hw)) as Hsnw.
    induction Hsnw as [w Hsnw IHw].
    assert (Hnext : forall u, tm_app (tm_abs U body) w --> u ->
        interp B rho sigma u).
    { intros u Hstep; inversion Hstep; subst.
      + eapply Hbody; eauto.
      + exfalso; eapply value_no_step; eauto.
      + eapply IHw; eauto using interp_step.
    }
    eapply interp_neutral.
    + unfold locally_closed_tm in *; constructor;
        [eapply value_lc; eauto|exact (proj1 (proj1 Hw))].
    + apply sn_from_successors; intros u Hstep.
      exact (proj2 (interp_basic _ _ _ _ (Hnext u Hstep))).
    + intros H; inversion H; subst; try discriminate; inversion H0.
    + exact Hnext.
Qed.

Lemma interp_tabs : forall T rho sigma body,
  value (tm_tabs body) ->
  (forall U R, locally_closed_ty U -> candidate R ->
    interp T rho (R :: sigma) (open_tm_ty body U)) ->
  interp (Ty_All T) rho sigma (tm_tabs body).
Proof.
  intros T rho sigma body Hval Hbody.
  eapply interp_value_intro; eauto.
  - split; [eapply value_lc; eauto|].
    apply sn_from_successors; intros u Hstep.
    exfalso; eapply value_no_step; eauto.
  - intros U R HU HR.
    assert (Hnext : forall u, tm_tapp (tm_tabs body) U --> u ->
        interp T rho (R :: sigma) u).
    { intros u Hstep; inversion Hstep; subst.
      + apply Hbody; assumption.
      + exfalso; eapply value_no_step; eauto.
    }
    eapply interp_neutral.
    + unfold locally_closed_tm in *; constructor;
        [eapply value_lc; eauto|exact HU].
    + apply sn_from_successors; intros u Hstep.
      exact (proj2 (interp_basic _ _ _ _ (Hnext u Hstep))).
    + intros H; inversion H; subst; try discriminate; inversion H0.
    + exact Hnext.
Qed.

Lemma interp_multi : forall T rho sigma t u,
  interp T rho sigma t -> t -->* u -> interp T rho sigma u.
Proof.
  intros T rho sigma t u Hrel Hmulti; induction Hmulti; eauto using interp_step.
Qed.

Lemma interp_closed_sigma : forall U rho sigma1 sigma2 t,
  locally_closed_ty U ->
  interp U rho sigma1 t <-> interp U rho sigma2 t.
Proof.
  intros U rho sigma1 sigma2 t HU.
  eapply interp_ext with (k := 0); eauto; intros; try lia; tauto.
Qed.

Lemma interp_self : forall U rho sigma t,
  locally_closed_ty U ->
  (interp U rho sigma t <->
    basic t /\ forall v, t -->* v -> value v -> interp U rho [] v).
Proof.
  intros U rho sigma t HU; split.
  - intros Hrel; split; [exact (proj1 Hrel)|].
    intros v Hmulti Hv.
    apply (proj1 (interp_closed_sigma U rho sigma [] v HU)).
    eapply interp_multi; eauto.
  - intros [Hb Hval]. split; [exact Hb|].
    destruct U; simpl in *; intros v Hmulti Hv;
      pose proof (proj2 (interp_closed_sigma _ rho sigma [] v HU)
        (Hval v Hmulti Hv)) as Hrel;
      destruct Hrel as [_ Hcore]; eapply Hcore; eauto using multi_refl.
Qed.

Lemma interp_open_bound : forall T k rho prefix sigma U t,
  lc_ty_at (S k) T -> length prefix = k -> locally_closed_ty U ->
  interp (open_ty_rec k U T) rho (prefix ++ sigma) t <->
  interp T rho (prefix ++ interp U rho [] :: sigma) t.
Proof.
  induction T; intros k rho prefix sigma U t Hlc Hlen HU;
    simpl in *.
  - inversion Hlc; clear Hlc.
    destruct (Nat.eqb k n) eqn:Heq.
    + apply Nat.eqb_eq in Heq; subst n; rewrite <- Heq in *.
      unfold interp at 2; simpl.
      replace (nth k (prefix ++ interp U rho [] :: sigma) basic)
        with (interp U rho []).
      * apply interp_self; exact HU.
      * rewrite app_nth2 by lia.
        rewrite Hlen. replace (k - k) with 0 by lia. reflexivity.
    + apply Nat.eqb_neq in Heq.
      assert (n < k) by lia.
      unfold interp; simpl.
      rewrite !app_nth1 by lia. tauto.
  - unfold interp; simpl; tauto.
  - inversion Hlc; clear Hlc.
    split; intros [Hb Hcore]; split; auto;
      intros v Hmulti Hv; specialize (Hcore v Hmulti Hv).
    + intros w Hw.
      apply (proj1 (IHT2 k rho prefix sigma U (tm_app v w) H3 Hlen HU)).
      apply Hcore.
      apply (proj2 (IHT1 k rho prefix sigma U w H2 Hlen HU)); exact Hw.
    + intros w Hw.
      apply (proj2 (IHT2 k rho prefix sigma U (tm_app v w) H3 Hlen HU)).
      apply Hcore.
      apply (proj1 (IHT1 k rho prefix sigma U w H2 Hlen HU)); exact Hw.
  - inversion Hlc; clear Hlc.
    split; intros [Hb Hcore]; split; auto;
      intros v Hmulti Hv; specialize (Hcore v Hmulti Hv);
      intros V R HV HR.
    + apply (proj1 (IHT (S k) rho (R :: prefix) sigma U
        (tm_tapp v V) H1 ltac:(simpl; lia) HU)); apply Hcore; assumption.
    + apply (proj2 (IHT (S k) rho (R :: prefix) sigma U
        (tm_tapp v V) H1 ltac:(simpl; lia) HU)); apply Hcore; assumption.
  - unfold interp; simpl; tauto.
  - unfold interp; simpl; tauto.
Qed.

Lemma interp_open_fvar : forall T k X rho R prefix sigma t,
  lc_ty_at (S k) T -> ~ In X (ty_fvs T) -> length prefix = k ->
  interp (open_ty_rec k (Ty_FVar X) T) (rupdate rho X R)
    (prefix ++ sigma) t <->
  interp T rho (prefix ++ R :: sigma) t.
Proof.
  induction T; intros k X rho R prefix sigma t Hlc Hfresh Hlen;
    simpl in *.
  - inversion Hlc; clear Hlc.
    destruct (Nat.eqb k n) eqn:Heq.
    + apply Nat.eqb_eq in Heq; subst n; rewrite <- Heq in *.
      unfold interp; simpl; unfold rupdate; rewrite Nat.eqb_refl.
      rewrite app_nth2 by lia. rewrite Hlen.
      replace (k - k) with 0 by lia. tauto.
    + apply Nat.eqb_neq in Heq; assert (n < k) by lia.
      unfold interp; simpl. rewrite !app_nth1 by lia; tauto.
  - assert (X <> a) by (intro Heq; apply Hfresh; subst; auto).
    unfold interp; simpl; unfold rupdate.
    apply Nat.eqb_neq in H as Heq; rewrite Heq; tauto.
  - inversion Hlc; clear Hlc.
    rewrite in_app_iff in Hfresh.
    split; intros [Hb Hcore]; split; auto;
      intros v Hmulti Hv; specialize (Hcore v Hmulti Hv).
    + intros w Hw.
      apply (proj1 (IHT2 k X rho R prefix sigma (tm_app v w)
        H3 ltac:(tauto) Hlen)).
      apply Hcore. apply (proj2 (IHT1 k X rho R prefix sigma w
        H2 ltac:(tauto) Hlen)); exact Hw.
    + intros w Hw.
      apply (proj2 (IHT2 k X rho R prefix sigma (tm_app v w)
        H3 ltac:(tauto) Hlen)).
      apply Hcore. apply (proj1 (IHT1 k X rho R prefix sigma w
        H2 ltac:(tauto) Hlen)); exact Hw.
  - inversion Hlc; clear Hlc.
    split; intros [Hb Hcore]; split; auto;
      intros v Hmulti Hv; specialize (Hcore v Hmulti Hv);
      intros U R' HU HR.
    + apply (proj1 (IHT (S k) X rho R (R' :: prefix) sigma
        (tm_tapp v U) H1 Hfresh ltac:(simpl; lia)));
        apply Hcore; assumption.
    + apply (proj2 (IHT (S k) X rho R (R' :: prefix) sigma
        (tm_tapp v U) H1 Hfresh ltac:(simpl; lia)));
        apply Hcore; assumption.
  - unfold interp; simpl; tauto.
  - unfold interp; simpl; tauto.
Qed.

Lemma typed_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_ty T.
Proof.
  intros Delta Gamma t T Htyping; induction Htyping;
    unfold locally_closed_ty in *; eauto using wf_lc with core.
  - change (locally_closed_ty T). eapply wf_lc; eauto.
  - constructor; [eapply wf_lc; eauto|].
    apply (H1 (fresh L) (fresh_notin L)).
  - inversion IHHtyping1; subst; assumption.
  - constructor.
    specialize (H0 (fresh L) (fresh_notin L)).
    unfold open_ty in H0.
    eapply lc_ty_close_rec; eauto.
  - inversion IHHtyping; subst.
    unfold open_ty. eapply lc_ty_open_rec; eauto using wf_lc.
Qed.

Fixpoint context_fvs (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (_, T) :: rest => ty_fvs T ++ context_fvs rest
  end.

Lemma lookup_context_fvs : forall Gamma x T X,
  lookup_context x Gamma = Some T -> In X (ty_fvs T) ->
  In X (context_fvs Gamma).
Proof.
  induction Gamma as [|[y V] rest IH]; intros x T X Hlookup Hin;
    simpl in *; try discriminate.
  destruct (Nat.eqb x y) eqn:Heq.
  - inversion Hlookup; subst. apply in_or_app; auto.
  - apply in_or_app; right; eapply IH; eauto.
Qed.

Lemma tm_fvs_map_tm_ty : forall t theta,
  tm_fvs (map_tm_ty theta t) = tm_fvs t.
Proof.
  induction t; intros theta; simpl;
    try rewrite (IHt theta); try rewrite (IHt1 theta);
    try rewrite (IHt2 theta); try rewrite (IHt3 theta); reflexivity.
Qed.

Lemma sem_tm_open_tm : forall t theta gamma x v,
  ~ In x (tm_fvs t) ->
  (forall y, locally_closed_tm (gamma y)) ->
  sem_tm theta (vupdate gamma x v) (open_tm t (tm_fvar x)) =
  open_tm (sem_tm theta gamma t) v.
Proof.
  intros t theta gamma x v Hfresh Hgamma.
  unfold sem_tm, open_tm.
  rewrite map_tm_ty_open_tm.
  apply map_tm_open; eauto. rewrite tm_fvs_map_tm_ty; assumption.
Qed.

Lemma sem_tm_open_ty : forall t theta gamma X U,
  ~ In X (tm_ty_fvs t) ->
  (forall Y, locally_closed_ty (theta Y)) ->
  (forall y, locally_closed_tm (gamma y)) ->
  sem_tm (tupdate theta X U) gamma (open_tm_ty t (Ty_FVar X)) =
  open_tm_ty (sem_tm theta gamma t) U.
Proof.
  intros t theta gamma X U Hfresh Htheta Hgamma.
  unfold sem_tm, open_tm_ty.
  rewrite map_tm_ty_open_ty by assumption.
  apply map_tm_open_tm_ty; assumption.
Qed.

Lemma sem_tm_lc : forall t theta gamma,
  locally_closed_tm t ->
  (forall X, locally_closed_ty (theta X)) ->
  (forall x, locally_closed_tm (gamma x)) ->
  locally_closed_tm (sem_tm theta gamma t).
Proof.
  intros t theta gamma Hlc Htheta Hgamma.
  unfold sem_tm.
  eapply lc_map_tm; eauto.
  eapply lc_map_tm_ty; eauto.
Qed.

Definition context_lc (Gamma : context) :=
  forall x T, lookup_context x Gamma = Some T -> locally_closed_ty T.

Definition env_ok (Gamma : context) (rho : atom -> tm -> Prop)
    (gamma : atom -> tm) :=
  forall x T, lookup_context x Gamma = Some T ->
    value (gamma x) /\ interp T rho [] (gamma x).

Lemma context_lc_update : forall Gamma x T,
  context_lc Gamma -> locally_closed_ty T ->
  context_lc (update Gamma x T).
Proof.
  intros Gamma x T Hctx HT y V Hlookup.
  simpl in Hlookup. unfold update in Hlookup; simpl in Hlookup.
  destruct (Nat.eqb y x); [inversion Hlookup; subst; assumption|].
  eapply Hctx; eauto.
Qed.

Lemma env_ok_update : forall Gamma rho gamma x T v,
  env_ok Gamma rho gamma -> value v -> interp T rho [] v ->
  env_ok (update Gamma x T) rho (vupdate gamma x v).
Proof.
  intros Gamma rho gamma x T v Henv Hv Hrel y V Hlookup.
  unfold update in Hlookup; simpl in Hlookup.
  unfold vupdate. destruct (Nat.eqb x y) eqn:Heq.
  - apply Nat.eqb_eq in Heq; subst.
    rewrite Nat.eqb_refl in Hlookup. inversion Hlookup; subst.
    auto.
  - apply Nat.eqb_neq in Heq.
    assert (Nat.eqb y x = false) by (apply Nat.eqb_neq; lia).
    rewrite H in Hlookup.
    eapply Henv; eauto.
Qed.

Lemma env_ok_fresh_type : forall Gamma rho gamma X R,
  context_lc Gamma -> env_ok Gamma rho gamma ->
  ~ In X (context_fvs Gamma) ->
  env_ok Gamma (rupdate rho X R) gamma.
Proof.
  intros Gamma rho gamma X R Hctx Henv Hfresh y V Hlookup.
  destruct (Henv y V Hlookup) as [Hv Hrel]; split; [exact Hv|].
  assert (Hr : forall Y, In Y (ty_fvs V) -> forall w,
    rho Y w <-> rupdate rho X R Y w).
  { intros Y HY w. unfold rupdate.
    assert (Y <> X).
    { intro Heq; subst.
      apply Hfresh. eapply lookup_context_fvs; eauto. }
    assert (Nat.eqb X Y = false) by (apply Nat.eqb_neq; lia).
    rewrite H0; tauto. }
  apply (proj1 (interp_ext V 0 (Hctx y V Hlookup) rho
    (rupdate rho X R) [] [] Hr ltac:(intros i Hi; lia) (gamma y)));
    exact Hrel.
Qed.

Theorem fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall theta rho gamma,
  context_lc Gamma ->
  (forall X, locally_closed_ty (theta X)) ->
  (forall x, locally_closed_tm (gamma x)) ->
  env_ok Gamma rho gamma ->
  interp T rho [] (sem_tm theta gamma t).
Proof.
  intros Delta Gamma t T Htyping; induction Htyping;
    intros theta rho gamma Hctx Htheta Hgamma Henv;
    unfold sem_tm at 1; simpl; fold (sem_tm theta gamma).
  - exact (proj2 (Henv x T H)).
  - eapply interp_abs.
    + constructor.
      change (locally_closed_tm (sem_tm theta gamma (tm_abs T1 t2))).
      eapply sem_tm_lc; eauto.
      eapply typed_lc. eapply T_Abs with (L := L); eauto.
    + intros v Hv Hrel.
      set (x := fresh (L ++ tm_fvs t2)).
      assert (Hfresh : ~ In x (L ++ tm_fvs t2)) by
        (unfold x; apply fresh_notin).
      rewrite in_app_iff in Hfresh.
      pose proof (H1 x ltac:(tauto) theta rho
        (vupdate gamma x v)
        (context_lc_update _ _ _ Hctx (wf_lc _ _ H))
        Htheta
        ltac:(intros y; unfold vupdate;
          destruct (Nat.eqb x y); eauto using value_lc)
        (env_ok_update _ _ _ _ _ _ Henv Hv Hrel)) as Hbody.
      rewrite sem_tm_open_tm in Hbody by (tauto || assumption).
      exact Hbody.
  - eapply interp_app; [eapply IHHtyping1|eapply IHHtyping2]; eauto.
  - eapply interp_tabs.
    + constructor.
      change (locally_closed_tm (sem_tm theta gamma (tm_tabs t))).
      eapply sem_tm_lc; eauto.
      eapply typed_lc. eapply T_TAbs with (L := L); eauto.
    + intros U R HU HR.
      set (X := fresh (L ++ tm_ty_fvs t ++ ty_fvs T ++ context_fvs Gamma)).
      assert (Hfresh : ~ In X
        (L ++ tm_ty_fvs t ++ ty_fvs T ++ context_fvs Gamma)) by
        (unfold X; apply fresh_notin).
      repeat rewrite in_app_iff in Hfresh.
      assert (Htheta' : forall Y, locally_closed_ty (tupdate theta X U Y)).
      { intros Y; unfold tupdate; destruct (Nat.eqb X Y); auto. }
      pose proof (H0 X ltac:(tauto) (tupdate theta X U)
        (rupdate rho X R) gamma Hctx Htheta' Hgamma
        (env_ok_fresh_type _ _ _ X R Hctx Henv ltac:(tauto))) as Hbody.
      rewrite sem_tm_open_ty in Hbody by (tauto || assumption).
      assert (Hclosed : locally_closed_ty (open_ty T (Ty_FVar X))).
      { eapply typed_type_lc. apply H. tauto. }
      unfold open_ty in Hclosed.
      apply (proj1 (interp_open_fvar T 0 X rho R [] []
        (open_tm_ty (sem_tm theta gamma t) U)
        (lc_ty_close_rec _ _ _ Hclosed) ltac:(tauto) eq_refl)) in Hbody.
      exact Hbody.
  - assert (HU : locally_closed_ty U) by (eapply wf_lc; eauto).
    assert (Hmapped : locally_closed_ty (map_ty theta U)).
    { eapply lc_map_ty; eauto. }
    assert (Hall : lc_ty_at 1 T).
    { pose proof (typed_type_lc _ _ _ _ Htyping) as Hclosed.
      inversion Hclosed; subst; assumption. }
    apply (proj2 (interp_open_bound T 0 rho [] [] U
      (tm_tapp (sem_tm theta gamma t) (map_ty theta U))
      Hall eq_refl HU)).
    eapply interp_tapp; eauto using interp_candidate.
  - eapply interp_value_intro; simpl; eauto using v_true.
    split; [unfold locally_closed_tm; constructor|].
    constructor; intros u Hstep; exfalso; eapply value_no_step; eauto using v_true.
  - eapply interp_value_intro; simpl; eauto using v_false.
    split; [unfold locally_closed_tm; constructor|].
    constructor; intros u Hstep; exfalso; eapply value_no_step; eauto using v_false.
  - eapply interp_if; eauto.
  - eapply interp_numeric; constructor.
  - eapply interp_succ; eauto.
  - eapply interp_rec; eauto.
  - eapply interp_choice; eauto.
Qed.

Lemma map_ty_identity : forall T,
  map_ty Ty_FVar T = T.
Proof.
  induction T; simpl; congruence.
Qed.

Lemma sem_tm_identity : forall t,
  sem_tm Ty_FVar tm_fvar t = t.
Proof.
  intros t; unfold sem_tm.
  induction t; simpl; try rewrite map_ty_identity;
    try rewrite IHt; try rewrite IHt1;
    try rewrite IHt2; try rewrite IHt3; reflexivity.
Qed.

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  intros t T Htyping.
  pose proof (fundamental [] empty t T Htyping Ty_FVar
    (fun _ => basic) tm_fvar) as Hrel.
  assert (Hctx : context_lc empty).
  { intros x U Hlookup; discriminate. }
  assert (Htheta : forall X, locally_closed_ty (Ty_FVar X)).
  { intros X; constructor. }
  assert (Hgamma : forall x, locally_closed_tm (tm_fvar x)).
  { intros x; unfold locally_closed_tm; constructor. }
  assert (Henv : env_ok empty (fun _ => basic) tm_fvar).
  { intros x U Hlookup; discriminate. }
  specialize (Hrel Hctx Htheta Hgamma Henv).
  rewrite sem_tm_identity in Hrel.
  exact (proj2 (proj1 Hrel)).
Qed.

End SystemFNormalizationIfNondeterminismRecursionHardTask.
