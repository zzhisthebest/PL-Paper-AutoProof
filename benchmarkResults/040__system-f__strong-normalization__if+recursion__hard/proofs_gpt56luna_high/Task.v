(** System F CBV strong-normalization benchmark, Hard variant.
    Features: if-recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
From Stdlib Require Import Program.Equality.
Import ListNotations.

Module SystemFNormalizationIfRecursionHardTask.

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

Inductive multi : tm -> tm -> Prop :=
  | multi_refl : forall x, multi x x
  | multi_step : forall x y z, x --> y -> multi y z -> multi x z.
Notation "t '-->*' u" := (multi t u) (at level 40).

Inductive strongly_normalizing : tm -> Prop :=
  | SN_intro : forall t,
      (forall u, t --> u -> strongly_normalizing u) -> strongly_normalizing t.

Hint Constructors lc_ty_at lc_tm_at value : core.

(* Construct the logical relation and supporting proofs here. *)

(* We use a type-erased copy of the operational language.  This is useful
   here because type substitution must not have any computational effect. *)
Inductive utm : Type :=
  | ubvar : nat -> utm
  | ufvar : atom -> utm
  | uabs : utm -> utm
  | uapp : utm -> utm -> utm
  | utabs : utm -> utm
  | utapp : utm -> utm
  | utrue : utm
  | ufalse : utm
  | uif : utm -> utm -> utm -> utm
  | uzero : utm
  | usucc : utm -> utm
  | urec : utm -> utm -> utm -> utm.

Fixpoint erase (t : tm) : utm :=
  match t with
  | tm_bvar i => ubvar i
  | tm_fvar x => ufvar x
  | tm_abs _ t1 => uabs (erase t1)
  | tm_app t1 t2 => uapp (erase t1) (erase t2)
  | tm_tabs t1 => utabs (erase t1)
  | tm_tapp t1 _ => utapp (erase t1)
  | tm_true => utrue
  | tm_false => ufalse
  | tm_if t1 t2 t3 => uif (erase t1) (erase t2) (erase t3)
  | tm_zero => uzero
  | tm_succ t1 => usucc (erase t1)
  | tm_natrec n b s => urec (erase n) (erase b) (erase s)
  end.

Fixpoint uopen_rec (k : nat) (u t : utm) : utm :=
  match t with
  | ubvar i => if Nat.eqb k i then u else ubvar i
  | ufvar x => ufvar x
  | uabs t1 => uabs (uopen_rec (S k) u t1)
  | uapp t1 t2 => uapp (uopen_rec k u t1) (uopen_rec k u t2)
  | utabs t1 => utabs (uopen_rec k u t1)
  | utapp t1 => utapp (uopen_rec k u t1)
  | utrue => utrue
  | ufalse => ufalse
  | uif t1 t2 t3 => uif (uopen_rec k u t1) (uopen_rec k u t2) (uopen_rec k u t3)
  | uzero => uzero
  | usucc t1 => usucc (uopen_rec k u t1)
  | urec n b s => urec (uopen_rec k u n) (uopen_rec k u b) (uopen_rec k u s)
  end.

Definition uopen (t u : utm) := uopen_rec 0 u t.

Lemma erase_open_rec : forall k t u,
  erase (open_tm_rec k u t) = uopen_rec k (erase u) (erase t).
Proof.
  intros k t u; revert k; induction t; intros k; simpl; try rewrite IHt; try rewrite IHt1;
    try rewrite IHt2; try rewrite IHt3; try destruct (Nat.eqb k n); reflexivity.
Qed.

Lemma erase_open : forall t u,
  erase (open_tm t u) = uopen (erase t) (erase u).
Proof. intros; apply erase_open_rec. Qed.

Lemma erase_open_ty_rec : forall k t U,
  erase (open_tm_ty_rec k U t) = erase t.
Proof.
  intros k t U; revert k; induction t; intros k; simpl; try rewrite IHt;
    try rewrite IHt1; try rewrite IHt2; try rewrite IHt3; reflexivity.
Qed.

Lemma erase_open_ty : forall t U, erase (open_tm_ty t U) = erase t.
Proof. intros; apply erase_open_ty_rec. Qed.

Inductive unumeric : utm -> Prop :=
  | unv_zero : unumeric uzero
  | unv_succ : forall n, unumeric n -> unumeric (usucc n).

Inductive uvalue : utm -> Prop :=
  | uv_abs : forall t, uvalue (uabs t)
  | uv_tabs : forall t, uvalue (utabs t)
  | uv_true : uvalue utrue
  | uv_false : uvalue ufalse
  | uv_nat : forall n, unumeric n -> uvalue n.

Reserved Notation "t1 '-->u' t2" (at level 40).

Inductive ustep : utm -> utm -> Prop :=
  | U_AppAbs : forall t v, uvalue v -> ustep (uapp (uabs t) v) (uopen t v)
  | U_App1 : forall t t' u, ustep t t' -> ustep (uapp t u) (uapp t' u)
  | U_App2 : forall v u u', uvalue v -> ustep u u' -> ustep (uapp v u) (uapp v u')
  | U_TAppTabs : forall t, ustep (utapp (utabs t)) t
  | U_TApp : forall t t', ustep t t' -> ustep (utapp t) (utapp t')
  | U_Succ : forall t t', ustep t t' -> ustep (usucc t) (usucc t')
  | U_RecArg : forall n n' b s, ustep n n' -> ustep (urec n b s) (urec n' b s)
  | U_RecBase : forall n b b' s, unumeric n -> ustep b b' -> ustep (urec n b s) (urec n b' s)
  | U_RecStep : forall n b s s', unumeric n -> uvalue b -> ustep s s' ->
      ustep (urec n b s) (urec n b s')
  | U_RecZero : forall b s, uvalue b -> uvalue s -> ustep (urec uzero b s) b
  | U_RecSucc : forall n b s, unumeric n -> uvalue b -> uvalue s ->
      ustep (urec (usucc n) b s) (uapp (uapp s n) (urec n b s))
  | U_IfTrue : forall t1 t2, ustep (uif utrue t1 t2) t1
  | U_IfFalse : forall t1 t2, ustep (uif ufalse t1 t2) t2
  | U_If : forall t1 t1' t2 t3, ustep t1 t1' -> ustep (uif t1 t2 t3) (uif t1' t2 t3).

Notation "t1 '-->u' t2" := (ustep t1 t2) (at level 40).

Lemma erase_unumeric : forall t, numeric_value t -> unumeric (erase t).
Proof.
  intros t H; induction H as [| n H IH]; simpl.
  - constructor.
  - constructor; exact IH.
Qed.

Lemma erase_value : forall t, value t -> uvalue (erase t).
Proof.
  intros t H; destruct H; simpl.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor; apply erase_unumeric; assumption.
Qed.

Lemma erase_step : forall t u, t --> u -> erase t -->u erase u.
Proof.
  intros t u H; induction H.
  - simpl. rewrite erase_open. constructor; apply erase_value; assumption.
  - simpl. constructor; assumption.
  - simpl. constructor; [apply erase_value; assumption | assumption].
  - simpl. rewrite erase_open_ty. constructor.
  - simpl. constructor; assumption.
  - simpl. constructor; assumption.
  - simpl. constructor; assumption.
  - simpl. constructor; [apply erase_unumeric; assumption | assumption].
  - simpl. constructor; [apply erase_unumeric; assumption | apply erase_value; assumption | assumption].
  - simpl. constructor; [apply erase_value; assumption | apply erase_value; assumption].
  - simpl. constructor; [apply erase_unumeric; assumption | apply erase_value; assumption | apply erase_value; assumption].
  - simpl. constructor; assumption.
  - simpl. constructor; assumption.
  - simpl. constructor; assumption.
Qed.

Inductive umulti : utm -> utm -> Prop :=
  | um_refl : forall t, umulti t t
  | um_step : forall t u v, t -->u u -> umulti u v -> umulti t v.

Inductive usn : utm -> Prop :=
  | usn_intro : forall t, (forall u, t -->u u -> usn u) -> usn t.

Lemma sn_erased : forall q t, erase t = q -> usn q -> strongly_normalizing t.
Proof.
  intros q t Et H; revert t Et; induction H as [q Hsteps IH]; intros t Et.
  constructor; intros u Hu.
  apply erase_step in Hu. rewrite Et in Hu.
  specialize (IH (erase u) Hu).
  eapply IH; reflexivity.
Qed.

Lemma unumeric_no_step : forall v u, unumeric v -> ~ v -->u u.
Proof.
  intros v u Hv; revert u; induction Hv as [| n Hv IHn]; intros u H.
  - inversion H.
  - inversion H; eapply IHn; eassumption.
Qed.

Lemma uvalue_no_step : forall v u, uvalue v -> ~ v -->u u.
Proof.
  intros v u Hv H; destruct Hv as [t | t | | | n Hn].
  - inversion H.
  - inversion H.
  - inversion H.
  - inversion H.
  - exfalso; eapply (unumeric_no_step _ _ Hn); exact H.
Qed.

Lemma ustep_deterministic : forall t u v, t -->u u -> t -->u v -> u = v.
Proof.
  intros t u v H; revert v; induction H; intros v' Hv; dependent destruction Hv;
    try reflexivity; try contradiction; try congruence;
    try (subst; eauto using uvalue_no_step);
    try solve [exfalso; eapply uvalue_no_step; eassumption];
    try solve [exfalso; eapply unumeric_no_step; eassumption];
    try solve [f_equal; eauto];
    eauto using uvalue_no_step.
  all: try solve [exfalso; eapply uvalue_no_step; eauto].
  all: try solve [exfalso; eapply unumeric_no_step; eauto].
  all: try match goal with
    Hx : uvalue ?x, Hy : ustep ?x ?y |- _ =>
      exfalso; exact (uvalue_no_step _ _ Hx Hy)
  end.
  all: try match goal with
    Hx : unumeric ?x, Hy : ustep ?x ?y |- _ =>
      exfalso; exact (unumeric_no_step _ _ Hx Hy)
  end.
  all: try match goal with
    Hy : ustep (uabs ?x) ?y |- _ =>
      exfalso; exact (uvalue_no_step _ _ (uv_abs _) Hy)
  end.
  all: try match goal with
    Hy : ustep (utabs ?x) ?y |- _ =>
      exfalso; exact (uvalue_no_step _ _ (uv_tabs _) Hy)
  end.
  all: try match goal with
    Hy : ustep utrue ?y |- _ =>
      exfalso; exact (uvalue_no_step _ _ uv_true Hy)
  end.
  all: try match goal with
    Hy : ustep ufalse ?y |- _ =>
      exfalso; exact (uvalue_no_step _ _ uv_false Hy)
  end.
  all: try match goal with
    Hy : ustep uzero ?y |- _ =>
      exfalso; exact (unumeric_no_step _ _ unv_zero Hy)
  end.
  all: try match goal with
    Hn : unumeric ?x, Hy : ustep (usucc ?x) ?y |- _ =>
      exfalso; exact (unumeric_no_step _ _ (unv_succ _ Hn) Hy)
  end.
  all: try solve [f_equal; eauto].
  all: eauto.
Qed.

Lemma usn_expand : forall t u, t -->u u -> usn u -> usn t.
Proof.
  intros t u H Hu; constructor; intros v Hv.
  pose proof (ustep_deterministic _ _ _ H Hv) as E; subst; exact Hu.
Qed.

Definition terminal_bool (t : utm) : Prop :=
  forall v, uvalue v -> umulti t v -> v = utrue \/ v = ufalse.
Definition terminal_nat (t : utm) : Prop :=
  forall v, uvalue v -> umulti t v -> unumeric v.

Definition candidate (P : utm -> Prop) : Prop :=
  (forall t, P t -> usn t) /\
  (forall t u, t -->u u -> P u -> P t) /\
  (forall t, ~ uvalue t -> (forall u, t -->u u -> P u) -> P t).

Fixpoint interp (T : ty) (V : atom -> utm -> Prop)
         (E : list (utm -> Prop)) (t : utm) : Prop :=
  match T with
  | Ty_BVar i => match nth_error E i with Some P => P t | None => usn t end
  | Ty_FVar X => V X t
  | Ty_Arrow A B =>
      usn t /\ (forall u, interp A V E u -> interp B V E (uapp t u))
  | Ty_All T1 =>
      usn t /\ (forall P, candidate P -> interp T1 V (P :: E) (utapp t))
  | Ty_Bool => usn t /\ terminal_bool t
  | Ty_Nat => usn t /\ terminal_nat t
  end.

Definition vgood (V : atom -> utm -> Prop) : Prop :=
  forall X, candidate (V X).
Definition egood (E : list (utm -> Prop)) : Prop :=
  forall i P, nth_error E i = Some P -> candidate P.

Lemma egood_cons : forall P E, candidate P -> egood E -> egood (P :: E).
Proof.
  intros P E HP HE i Q H; destruct i; simpl in H.
  - injection H as <-; exact HP.
  - exact (HE i Q H).
Qed.

Lemma terminal_expand_bool : forall q q', q -->u q' ->
  terminal_bool q' -> terminal_bool q.
Proof.
  intros q q' H Hq v Hv Hm; inversion Hm as [| x y z Hxy Hyz].
  - subst v; exfalso; eapply (uvalue_no_step q q' Hv); exact H.
  - pose proof (ustep_deterministic _ _ _ H Hxy) as E; subst.
    apply Hq; assumption.
Qed.

Lemma terminal_expand_nat : forall q q', q -->u q' ->
  terminal_nat q' -> terminal_nat q.
Proof.
  intros q q' H Hq v Hv Hm; inversion Hm as [| x y z Hxy Hyz].
  - subst v; exfalso; eapply (uvalue_no_step q q' Hv); exact H.
  - pose proof (ustep_deterministic _ _ _ H Hxy) as E; subst.
    apply Hq; assumption.
Qed.

Fixpoint interp_reduct (T : ty) (V : atom -> utm -> Prop)
  (E : list (utm -> Prop)) (HG : vgood V) (HE : egood E)
  (q q' : utm) (H : q -->u q') : interp T V E q' -> interp T V E q.
Proof.
  destruct T as [i|X|A B|T| | ]; simpl.
  - destruct (nth_error E i) as [P|] eqn:Hi; intros HP.
    + destruct (HE i P Hi) as [_ [HC _]]. apply HC with (u := q'); assumption.
    + apply usn_expand with (u := q'); assumption.
  - intros HP; destruct (HG X) as [_ [HC _]]. apply HC with (u := q'); assumption.
  - intros HP; split.
    + exact (usn_expand q q' H (proj1 HP)).
    + intros u Hu.
      apply (interp_reduct B V E HG HE (uapp q u) (uapp q' u)).
      * constructor; exact H.
      * apply (proj2 HP); exact Hu.
  - intros HP; split.
    + exact (usn_expand q q' H (proj1 HP)).
    + intros P HPc.
      apply (interp_reduct T V (P :: E) HG (egood_cons P E HPc HE)
               (utapp q) (utapp q')).
      * constructor; exact H.
      * apply (proj2 HP); exact HPc.
  - intros HP; split.
    + exact (usn_expand q q' H (proj1 HP)).
    + exact (terminal_expand_bool q q' H (proj2 HP)).
  - intros HP; split.
    + exact (usn_expand q q' H (proj1 HP)).
    + exact (terminal_expand_nat q q' H (proj2 HP)).
Qed.

Lemma usn_app_neutral : forall q u,
  ~ uvalue q -> (forall q', q -->u q' -> usn (uapp q' u)) -> usn (uapp q u).
Proof.
  intros q u Hnv Hq; constructor; intros w Hw; dependent destruction Hw.
  - exfalso; apply Hnv; constructor.
  - apply Hq; assumption.
  - exfalso; apply Hnv; assumption.
Qed.

Lemma usn_tapp_neutral : forall q,
  ~ uvalue q -> (forall q', q -->u q' -> usn (utapp q')) -> usn (utapp q).
Proof.
  intros q Hnv Hq; constructor; intros w Hw; dependent destruction Hw.
  - exfalso; apply Hnv; constructor.
  - apply Hq; assumption.
Qed.

Lemma no_uvalue_app : forall q u, ~ uvalue (uapp q u).
Proof.
  intros q u H; inversion H; subst; try discriminate.
  all: try solve [inversion H0].
Qed.

Lemma no_uvalue_tapp : forall q, ~ uvalue (utapp q).
Proof.
  intros q H; inversion H; subst; try discriminate.
  all: try solve [inversion H0].
Qed.

Fixpoint interp_neutral (T : ty) (V : atom -> utm -> Prop)
  (E : list (utm -> Prop)) (HG : vgood V) (HE : egood E)
  (q : utm) (Hnv : ~ uvalue q)
  (Hq : forall q', q -->u q' -> interp T V E q') : interp T V E q.
Proof.
  destruct T as [i|X|A B|T| | ]; simpl.
  - destruct (nth_error E i) as [P|] eqn:Hi.
    + destruct (HE i P Hi) as [_ [_ HN]].
      assert (HqP : forall u, q -->u u -> P u).
      { intros u Hu; specialize (Hq u Hu).
        change (match nth_error E i with Some Q => Q u | None => usn u end) in Hq.
        rewrite Hi in Hq; exact Hq. }
      apply HN; [exact Hnv | exact HqP].
    + constructor; intros q' Hst; specialize (Hq q' Hst);
      change (match nth_error E i with Some Q => Q q' | None => usn q' end) in Hq;
      rewrite Hi in Hq; exact Hq.
  - destruct (HG X) as [_ [_ HN]]. apply HN; [exact Hnv | exact Hq].
  - split.
    + constructor; intros q' Hst; exact (proj1 (Hq q' Hst)).
    + intros u Hu.
      assert (Happ : ~ uvalue (uapp q u)) by apply no_uvalue_app.
      refine (interp_neutral B V E HG HE (uapp q u) Happ _).
      intros q' Hstep; dependent destruction Hstep.
      all: try solve [exfalso; apply Hnv; constructor].
      all: try solve [exfalso; apply Hnv; assumption].
      all: exact ((proj2 (Hq _ Hstep)) _ Hu).
  - split.
    + constructor; intros q' H; exact (proj1 (Hq q' H)).
    + intros P HP.
      apply (interp_neutral T V (P :: E) HG (egood_cons P E HP HE)
               (utapp q)).
      * apply no_uvalue_tapp.
      * intros q' Hstep; dependent destruction Hstep.
        all: try solve [exfalso; apply Hnv; constructor].
        all: exact ((proj2 (Hq _ Hstep)) _ HP).
  - split.
    + constructor; intros q' H; exact (proj1 (Hq q' H)).
    + intros v Hv Hm; inversion Hm as [| x y z Hxy Hyz].
      * subst v; exfalso; apply Hnv; exact Hv.
      * exact ((proj2 (Hq _ Hxy)) _ Hv Hyz).
  - split.
    + constructor; intros q' H; exact (proj1 (Hq q' H)).
    + intros v Hv Hm; inversion Hm as [| x y z Hxy Hyz].
      * subst v; exfalso; apply Hnv; exact Hv.
      * exact ((proj2 (Hq _ Hxy)) _ Hv Hyz).
Qed.

Lemma interp_candidate : forall T V E, vgood V -> egood E ->
  candidate (interp T V E).
Proof.
  induction T as [i|X|A IHA B IHB|T IHT| | ]; intros V E HG HE.
  - destruct (nth_error E i) as [P|] eqn:Hi.
    + unfold candidate; split.
      * intros q Hq;
        change (match nth_error E i with Some Q => Q q | None => usn q end) in Hq;
        rewrite Hi in Hq; exact (proj1 (HE i P Hi) q Hq).
      * split.
        -- intros q q' H Hq; apply interp_reduct with (q' := q'); assumption.
        -- intros q Hnv Hq; apply interp_neutral with (q := q); assumption.
    + unfold candidate; split.
      * intros q Hq;
        change (match nth_error E i with Some Q => Q q | None => usn q end) in Hq;
        rewrite Hi in Hq; exact Hq.
      * split.
        -- intros q q' H Hq; apply interp_reduct with (q' := q'); assumption.
        -- intros q Hnv Hq; apply interp_neutral with (q := q); assumption.
  - exact (HG X).
  - unfold candidate; split.
    + intros q Hq; exact (proj1 Hq).
    + split.
      * intros q q' H Hq; apply interp_reduct with (q' := q'); assumption.
      * intros q Hnv Hq; apply interp_neutral with (q := q); assumption.
  - unfold candidate; split.
    + intros q Hq; exact (proj1 Hq).
    + split.
      * intros q q' H Hq; apply interp_reduct with (q' := q'); assumption.
      * intros q Hnv Hq; apply interp_neutral with (q := q); assumption.
  - unfold candidate; split.
    + intros q Hq; exact (proj1 Hq).
    + split.
      * intros q q' H Hq; apply interp_reduct with (q' := q'); assumption.
      * intros q Hnv Hq; apply interp_neutral with (q := q); assumption.
  - unfold candidate; split.
    + intros q Hq; exact (proj1 Hq).
    + split.
      * intros q q' H Hq; apply interp_reduct with (q' := q'); assumption.
      * intros q Hnv Hq; apply interp_neutral with (q := q); assumption.
Qed.

Fixpoint ubclosed (t : utm) : Prop :=
  match t with
  | ubvar _ => False | ufvar _ => True
  | uabs t1 | utabs t1 | utapp t1 | usucc t1 => ubclosed t1
  | uapp t1 t2 => ubclosed t1 /\ ubclosed t2
  | uif t1 t2 t3 => ubclosed t1 /\ ubclosed t2 /\ ubclosed t3
  | utrue | ufalse | uzero => True
  | urec n b s => ubclosed n /\ ubclosed b /\ ubclosed s
  end.

Lemma ubclosed_open_id : forall k u t, ubclosed t ->
  uopen_rec k u t = t.
Proof.
  intros k u t; revert k; induction t; simpl; intros k H; try contradiction;
    try reflexivity; try rewrite IHt; try rewrite IHt1; try rewrite IHt2;
    try rewrite IHt3; tauto.
Qed.

Fixpoint ufv (t : utm) : list atom :=
  match t with
  | ubvar _ => [] | ufvar x => [x]
  | uabs t1 | utabs t1 | utapp t1 | usucc t1 => ufv t1
  | uapp t1 t2 => ufv t1 ++ ufv t2
  | uif t1 t2 t3 => ufv t1 ++ ufv t2 ++ ufv t3
  | uzero | utrue | ufalse => []
  | urec n b s => ufv n ++ ufv b ++ ufv s
  end.

Fixpoint usub (x : atom) (s t : utm) : utm :=
  match t with
  | ubvar i => ubvar i | ufvar y => if Nat.eqb x y then s else ufvar y
  | uabs t1 => uabs (usub x s t1)
  | uapp t1 t2 => uapp (usub x s t1) (usub x s t2)
  | utabs t1 => utabs (usub x s t1)
  | utapp t1 => utapp (usub x s t1)
  | utrue => utrue | ufalse => ufalse
  | uif t1 t2 t3 => uif (usub x s t1) (usub x s t2) (usub x s t3)
  | uzero => uzero | usucc t1 => usucc (usub x s t1)
  | urec n b f => urec (usub x s n) (usub x s b) (usub x s f)
  end.

Fixpoint usub_env (sigma : atom -> utm) (t : utm) : utm :=
  match t with
  | ubvar i => ubvar i | ufvar x => sigma x
  | uabs t1 => uabs (usub_env sigma t1)
  | uapp t1 t2 => uapp (usub_env sigma t1) (usub_env sigma t2)
  | utabs t1 => utabs (usub_env sigma t1)
  | utapp t1 => utapp (usub_env sigma t1)
  | utrue => utrue | ufalse => ufalse
  | uif t1 t2 t3 => uif (usub_env sigma t1) (usub_env sigma t2) (usub_env sigma t3)
  | uzero => uzero | usucc t1 => usucc (usub_env sigma t1)
  | urec n b f => urec (usub_env sigma n) (usub_env sigma b) (usub_env sigma f)
  end.

Fixpoint tm_subst_env (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i | tm_fvar x => sigma x
  | tm_abs T t1 => tm_abs T (tm_subst_env sigma t1)
  | tm_app t1 t2 => tm_app (tm_subst_env sigma t1) (tm_subst_env sigma t2)
  | tm_tabs t1 => tm_tabs (tm_subst_env sigma t1)
  | tm_tapp t1 T => tm_tapp (tm_subst_env sigma t1) T
  | tm_true => tm_true | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (tm_subst_env sigma t1) (tm_subst_env sigma t2) (tm_subst_env sigma t3)
  | tm_zero => tm_zero | tm_succ t1 => tm_succ (tm_subst_env sigma t1)
  | tm_natrec n b f => tm_natrec (tm_subst_env sigma n) (tm_subst_env sigma b) (tm_subst_env sigma f)
  end.

Lemma erase_tm_subst_env : forall sigma t,
  erase (tm_subst_env sigma t) = usub_env (fun x => erase (sigma x)) (erase t).
Proof. induction t; simpl; intros; try rewrite IHt; try rewrite IHt1; try rewrite IHt2; try rewrite IHt3; reflexivity. Qed.

Lemma usub_open_fresh : forall k t x sigma,
  ~ In x (ufv t) ->
  (forall a, ubclosed (sigma a)) ->
  usub_env sigma (uopen_rec k (ufvar x) t) =
  uopen_rec k (sigma x) (usub_env sigma t).
Proof.
  intros k t; revert k; induction t; intros k x sigma Hfresh Hclosed; simpl in *;
    try (destruct (Nat.eqb k n)); try reflexivity;
    try rewrite IHt; try rewrite IHt1; try rewrite IHt2; try rewrite IHt3;
    try reflexivity.
  all: simpl in Hfresh; repeat rewrite in_app_iff in Hfresh; try tauto.
  all: try (destruct (Nat.eqb x a) eqn:Ex;
    [apply Nat.eqb_eq in Ex; exfalso; apply Hfresh; subst; simpl; auto |
     rewrite (ubclosed_open_id k (sigma a) (sigma a)); reflexivity]).
  destruct (Nat.eqb x a) eqn:Ex.
  - apply Nat.eqb_eq in Ex; exfalso; apply Hfresh; subst; simpl; auto.
  - assert (Ex0 : Nat.eqb x a = false).
    { exact Ex. }
    symmetry; apply ubclosed_open_id; apply Hclosed.
Qed.

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  (* Complete the proof of normalization. *)
Qed.

End SystemFNormalizationIfRecursionHardTask.
