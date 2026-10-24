(** System F CBV strong-normalization benchmark, Hard variant.
    Features: recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFNormalizationRecursionHardTask.

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

Inductive multi : tm -> tm -> Prop :=
  | multi_refl : forall x, multi x x
  | multi_step : forall x y z, x --> y -> multi y z -> multi x z.
Notation "t '-->*' u" := (multi t u) (at level 40).

Inductive strongly_normalizing : tm -> Prop :=
  | SN_intro : forall t,
      (forall u, t --> u -> strongly_normalizing u) -> strongly_normalizing t.

Hint Constructors lc_ty_at lc_tm_at value : core.

(* ============================================================ *)
(* Part 1: type-erased terms and their reduction                 *)
(* ============================================================ *)

Inductive utm : Type :=
  | ut_bvar : nat -> utm
  | ut_fvar : atom -> utm
  | ut_abs : utm -> utm
  | ut_app : utm -> utm -> utm
  | ut_tabs : utm -> utm
  | ut_tapp : utm -> utm
  | ut_zero : utm
  | ut_succ : utm -> utm
  | ut_natrec : utm -> utm -> utm -> utm.

Fixpoint erase (t : tm) : utm :=
  match t with
  | tm_bvar i => ut_bvar i
  | tm_fvar x => ut_fvar x
  | tm_abs _ t1 => ut_abs (erase t1)
  | tm_app t1 t2 => ut_app (erase t1) (erase t2)
  | tm_tabs t1 => ut_tabs (erase t1)
  | tm_tapp t1 _ => ut_tapp (erase t1)
  | tm_zero => ut_zero
  | tm_succ t1 => ut_succ (erase t1)
  | tm_natrec n b s => ut_natrec (erase n) (erase b) (erase s)
  end.

Fixpoint uopen_rec (k : nat) (u t : utm) : utm :=
  match t with
  | ut_bvar i => if Nat.eqb k i then u else ut_bvar i
  | ut_fvar x => ut_fvar x
  | ut_abs b => ut_abs (uopen_rec (S k) u b)
  | ut_app a b => ut_app (uopen_rec k u a) (uopen_rec k u b)
  | ut_tabs b => ut_tabs (uopen_rec k u b)
  | ut_tapp a => ut_tapp (uopen_rec k u a)
  | ut_zero => ut_zero
  | ut_succ a => ut_succ (uopen_rec k u a)
  | ut_natrec n b s => ut_natrec (uopen_rec k u n) (uopen_rec k u b) (uopen_rec k u s)
  end.

Definition uopen (t u : utm) : utm := uopen_rec 0 u t.

Fixpoint usubst (x : atom) (s t : utm) : utm :=
  match t with
  | ut_bvar i => ut_bvar i
  | ut_fvar y => if Nat.eqb x y then s else ut_fvar y
  | ut_abs b => ut_abs (usubst x s b)
  | ut_app a b => ut_app (usubst x s a) (usubst x s b)
  | ut_tabs b => ut_tabs (usubst x s b)
  | ut_tapp a => ut_tapp (usubst x s a)
  | ut_zero => ut_zero
  | ut_succ a => ut_succ (usubst x s a)
  | ut_natrec n b c => ut_natrec (usubst x s n) (usubst x s b) (usubst x s c)
  end.

Fixpoint usubst_all (sigma : atom -> utm) (t : utm) : utm :=
  match t with
  | ut_bvar i => ut_bvar i
  | ut_fvar y => sigma y
  | ut_abs b => ut_abs (usubst_all sigma b)
  | ut_app a b => ut_app (usubst_all sigma a) (usubst_all sigma b)
  | ut_tabs b => ut_tabs (usubst_all sigma b)
  | ut_tapp a => ut_tapp (usubst_all sigma a)
  | ut_zero => ut_zero
  | ut_succ a => ut_succ (usubst_all sigma a)
  | ut_natrec n b c => ut_natrec (usubst_all sigma n) (usubst_all sigma b) (usubst_all sigma c)
  end.

Fixpoint FV_tm (t : utm) : list atom :=
  match t with
  | ut_bvar _ => nil
  | ut_fvar x => [x]
  | ut_abs b => FV_tm b
  | ut_app a b => FV_tm a ++ FV_tm b
  | ut_tabs b => FV_tm b
  | ut_tapp a => FV_tm a
  | ut_zero => nil
  | ut_succ a => FV_tm a
  | ut_natrec n b s => FV_tm n ++ FV_tm b ++ FV_tm s
  end.

Fixpoint FV_ty (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => nil
  | Ty_FVar X => [X]
  | Ty_Arrow A B => FV_ty A ++ FV_ty B
  | Ty_All T0 => FV_ty T0
  | Ty_Nat => nil
  end.

Lemma erase_open_tm_rec : forall t k u,
  erase (open_tm_rec k u t) = uopen_rec k (erase u) (erase t).
Proof.
  intros t. induction t; intros k u; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
  - reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2, IHt3. reflexivity.
Qed.

Lemma erase_open_tm : forall t u, erase (open_tm t u) = uopen (erase t) (erase u).
Proof. intros. apply erase_open_tm_rec. Qed.

Lemma erase_open_tm_ty_rec : forall t k U, erase (open_tm_ty_rec k U t) = erase t.
Proof.
  intros t. induction t; intros k U; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
  - reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2, IHt3. reflexivity.
Qed.

Lemma erase_open_tm_ty : forall t U, erase (open_tm_ty t U) = erase t.
Proof. intros. apply erase_open_tm_ty_rec. Qed.

(* ---------- values ---------- *)

Inductive unum : utm -> Prop :=
  | un_zero : unum ut_zero
  | un_succ : forall n, unum n -> unum (ut_succ n).

Inductive uvalue : utm -> Prop :=
  | uv_abs : forall b, uvalue (ut_abs b)
  | uv_tabs : forall b, uvalue (ut_tabs b)
  | uv_zero : uvalue ut_zero
  | uv_succ : forall n, uvalue n -> uvalue (ut_succ n).

Hint Constructors unum uvalue : core.

Lemma unum_uvalue : forall n, unum n -> uvalue n.
Proof. intros n H. induction H; eauto. Qed.

Fixpoint unumeral (k : nat) : utm :=
  match k with O => ut_zero | S m => ut_succ (unumeral m) end.

Lemma numeral_unum : forall k, unum (unumeral k).
Proof. intros k. induction k; simpl; eauto. Qed.

Lemma unum_unumeral : forall n, unum n -> exists k, n = unumeral k.
Proof.
  intros n H. induction H as [| m Hm IHm].
  - exists 0. reflexivity.
  - destruct IHm as [k E]. exists (S k). simpl. rewrite E. reflexivity.
Qed.

(* ---------- small-step reduction on erased terms ---------- *)

Inductive ustep : utm -> utm -> Prop :=
  | us_app_abs : forall b v, uvalue v -> ustep (ut_app (ut_abs b) v) (uopen b v)
  | us_app_1 : forall e1 e1' e2, ustep e1 e1' -> ustep (ut_app e1 e2) (ut_app e1' e2)
  | us_app_2 : forall v1 e2 e2', uvalue v1 -> ustep e2 e2' -> ustep (ut_app v1 e2) (ut_app v1 e2')
  | us_tapp_tabs : forall b, ustep (ut_tapp (ut_tabs b)) b
  | us_tapp : forall e e', ustep e e' -> ustep (ut_tapp e) (ut_tapp e')
  | us_succ : forall e e', ustep e e' -> ustep (ut_succ e) (ut_succ e')
  | us_rec_arg : forall n n' b s, ustep n n' -> ustep (ut_natrec n b s) (ut_natrec n' b s)
  | us_rec_base : forall n b b' s, unum n -> ustep b b' -> ustep (ut_natrec n b s) (ut_natrec n b' s)
  | us_rec_step : forall n b s s', unum n -> uvalue b -> ustep s s' -> ustep (ut_natrec n b s) (ut_natrec n b s')
  | us_rec_zero : forall b s, uvalue b -> uvalue s -> ustep (ut_natrec ut_zero b s) b
  | us_rec_succ : forall n b s, unum n -> uvalue b -> uvalue s ->
        ustep (ut_natrec (ut_succ n) b s) (ut_app (ut_app s n) (ut_natrec n b s)).

Hint Constructors ustep : core.

Lemma ustep_not_value : forall e e', ustep e e' -> ~ uvalue e.
Proof.
  intros e e' H. induction H; intros Hv; inversion Hv; subst; eauto.
Qed.

Lemma uvalue_no_step : forall v v', uvalue v -> ustep v v' -> False.
Proof. intros v v' Hv Hs. exact (ustep_not_value v v' Hs Hv). Qed.

Lemma unum_no_step : forall v v', unum v -> ustep v v' -> False.
Proof. intros v v' H1 H2. exact (uvalue_no_step v v' (unum_uvalue v H1) H2). Qed.

Inductive usn : utm -> Prop :=
  | usn_intro : forall e, (forall e', ustep e e' -> usn e') -> usn e.

Hint Constructors usn : core.

Lemma usn_step : forall e, usn e -> forall e', ustep e e' -> usn e'.
Proof. intros e H. induction H as [e Hred]. intros e' Hs. apply Hred. assumption. Qed.

Lemma usn_succ : forall e, usn e -> usn (ut_succ e).
Proof.
  intros e H. induction H as [e Hred IH].
  apply usn_intro. intros e' Hs. inversion Hs as [b v | e1 e1' e2 Hst | v1 e2 e2' Hv Hst | b | e0 e0' Hst | e0 e0' Hst | n n' b s Hst | n b b' s Hn Hst | n b s s' Hn Hv Hst | b s Hv Hvs | n b s Hn Hv Hvs].
  - apply IH. assumption.
Qed.

Lemma usn_succ_inv : forall e, usn (ut_succ e) -> usn e.
Proof.
  intros e H. remember (ut_succ e) as u eqn:E. revert e E.
  induction H as [u Hred IH].
  intros e E. apply usn_intro. intros e' Hs.
  apply (IH (ut_succ e')). { rewrite E. apply us_succ. assumption. }
  reflexivity.
Qed.

Lemma usn_value : forall v, uvalue v -> usn v.
Proof.
  intros v H. induction H as [b | b | | n Hn IHn].
  - apply usn_intro. intros v' Hs. exfalso. exact (uvalue_no_step (ut_abs b) v' (uv_abs b) Hs).
  - apply usn_intro. intros v' Hs. exfalso. exact (uvalue_no_step (ut_tabs b) v' (uv_tabs b) Hs).
  - apply usn_intro. intros v' Hs. exfalso. exact (uvalue_no_step ut_zero v' uv_zero Hs).
  - apply usn_succ. exact IHn.
Qed.

Inductive umulti : utm -> utm -> Prop :=
  | umulti_refl : forall e, umulti e e
  | umulti_step : forall e1 e2 e3, ustep e1 e2 -> umulti e2 e3 -> umulti e1 e3.

Hint Constructors umulti : core.

Lemma umulti_one : forall e e', ustep e e' -> umulti e e'.
Proof. intros. apply umulti_step with e'; [assumption | apply umulti_refl]. Qed.

Lemma umulti_trans : forall e1 e2, umulti e1 e2 -> forall e3, umulti e2 e3 -> umulti e1 e3.
Proof.
  intros e1 e2 H. induction H as [a | a b c Hstep Hrest IH]; intros e3 H2.
  - assumption.
  - apply umulti_step with (e2 := b). assumption. apply IH. assumption.
Qed.

Lemma umulti_value : forall v e', uvalue v -> umulti v e' -> e' = v.
Proof.
  intros v e' Hv H. induction H as [a | a b c Hs Hrest IH].
  - reflexivity.
  - exfalso. exact (uvalue_no_step a b Hv Hs).
Qed.

Lemma umulti_cons : forall e v, umulti e v -> e = v \/ exists e2, ustep e e2 /\ umulti e2 v.
Proof. intros e v H. destruct H. - left; reflexivity. - right; eauto. Qed.

(* ---------- erasure preserves reduction ---------- *)

Lemma erase_numeric : forall n, numeric_value n -> unum (erase n).
Proof. intros n H. induction H. - simpl; constructor. - simpl; constructor; assumption. Qed.

Lemma erase_value : forall v, value v -> uvalue (erase v).
Proof.
  intros v H. induction H.
  - simpl; constructor.
  - simpl; constructor.
  - apply unum_uvalue. apply erase_numeric. assumption.
Qed.

Lemma erase_step : forall t t', step t t' -> ustep (erase t) (erase t').
Proof.
  intros t t' H. induction H; simpl.
  - (* ST_AppAbs *) rewrite erase_open_tm. constructor. apply erase_value. assumption.
  - (* ST_App1 *) constructor. assumption.
  - (* ST_App2 *) constructor; [apply erase_value; assumption | assumption].
  - (* ST_TAppTabs *) rewrite erase_open_tm_ty. constructor.
  - (* ST_TApp *) constructor. assumption.
  - (* ST_Succ *) constructor. assumption.
  - (* ST_RecArg *) constructor. assumption.
  - (* ST_RecBase *) econstructor; [apply erase_numeric; assumption | assumption].
  - (* ST_RecStep *) econstructor; [apply erase_numeric; assumption | apply erase_value; assumption | assumption].
  - (* ST_RecZero *) econstructor; [apply erase_value; assumption | apply erase_value; assumption].
  - (* ST_RecSucc *) econstructor; [apply erase_numeric; assumption | apply erase_value; assumption | apply erase_value; assumption].
Qed.

Lemma usn_erase_SN : forall t, usn (erase t) -> strongly_normalizing t.
Proof.
  intros t H. remember (erase t) as e eqn:E. revert t E.
  induction H as [e Hred IH].
  intros t E. apply SN_intro. intros t' Hst.
  apply (IH (erase t')). { rewrite E. apply erase_step. assumption. }
  reflexivity.
Qed.

(* ============================================================ *)
(* Part 2: the type-indexed logical relation on erased terms     *)
(* ============================================================ *)

Definition cand := utm -> Prop.

Definition default_cand : cand := fun e => usn e.

Definition sn_cand (P : cand) : Prop :=
  (forall e, P e -> usn e) /\
  (forall e e', P e -> ustep e e' -> P e') /\
  (forall e, ~ uvalue e -> usn e -> (forall e', ustep e e' -> P e') -> P e).

Definition rho_valid (rho : atom -> cand) : Prop :=
  forall X, sn_cand (rho X).

Definition db_valid (db : list cand) : Prop :=
  forall P, In P db -> sn_cand P.

Definition nth_cand (db : list cand) (i : nat) : cand := nth i db default_cand.

Fixpoint C (T : ty) (db : list cand) (rho : atom -> cand) : cand :=
  match T with
  | Ty_BVar i => nth_cand db i
  | Ty_FVar X => rho X
  | Ty_Nat => fun e => usn e /\ (forall v, umulti e v -> uvalue v -> unum v)
  | Ty_Arrow A B => fun e => usn e /\ (forall v, umulti e v -> uvalue v ->
        match v with
        | ut_abs body => (forall w, Vall A db rho w -> C B db rho (uopen body w))
        | _ => False
        end)
  | Ty_All T0 => fun e => usn e /\ (forall v, umulti e v -> uvalue v ->
        match v with
        | ut_tabs body => (forall P : cand, sn_cand P -> C T0 (P :: db) rho body)
        | _ => False
        end)
  end
with Vall (T : ty) (db : list cand) (rho : atom -> cand) : cand :=
  match T with
  | Ty_BVar i => nth_cand db i
  | Ty_FVar X => rho X
  | Ty_Nat => unum
  | Ty_Arrow A B => fun v =>
        match v with
        | ut_abs body => (forall w, Vall A db rho w -> C B db rho (uopen body w))
        | _ => False
        end
  | Ty_All T0 => fun v =>
        match v with
        | ut_tabs body => (forall P : cand, sn_cand P -> C T0 (P :: db) rho body)
        | _ => False
        end
  end.

(* ---------- validity of the default candidate and environments ---------- *)

Lemma default_cand_valid : sn_cand default_cand.
Proof.
  unfold sn_cand, default_cand. split.
  - intros e H. assumption.
  - split.
    + intros e e' H Hs. apply usn_step with e; assumption.
    + intros e Hnv Hs Hred. apply usn_intro. assumption.
Qed.

Lemma nth_cand_valid : forall db i, db_valid db -> sn_cand (nth_cand db i).
Proof.
  intros db. induction db as [| P db IH]; intros i Hvalid.
  - unfold nth_cand. destruct i; simpl; apply default_cand_valid.
  - destruct i; unfold nth_cand; simpl.
    + apply Hvalid. left. reflexivity.
    + apply IH. intros Q HQ. apply Hvalid. right. assumption.
Qed.

Lemma sn_cand_std : forall Body : utm -> Prop,
  sn_cand (fun e => usn e /\ (forall v, umulti e v -> uvalue v -> Body v)).
Proof.
  intros Body. unfold sn_cand. split.
  - intros e [H _]. assumption.
  - split.
    + intros e e' [Hsn Hval] Hs. split.
      * apply usn_step with e; assumption.
      * intros v Hm Hv.
        exact (Hval v (umulti_trans e e' (umulti_one e e' Hs) v Hm) Hv).
    + intros e Hnv Hsn Hred. split.
      * apply usn_intro. intros e' Hs. destruct (Hred e' Hs) as [H _]. assumption.
      * intros v Hm Hv. destruct (umulti_cons e v Hm) as [E | [e2 [Hs Hm']]].
        -- subst v. exfalso. apply Hnv. assumption.
        -- destruct (Hred e2 Hs) as [_ Hval]. exact (Hval v Hm' Hv).
Qed.

Lemma C_sn_cand : forall T db rho, db_valid db -> rho_valid rho -> sn_cand (C T db rho).
Proof.
  intros T. induction T; intros db rho Hdb Hrho.
  - (* BVar *) simpl. apply nth_cand_valid. assumption.
  - (* FVar *) simpl. apply Hrho.
  - (* Arrow *) simpl. apply sn_cand_std.
  - (* All *) simpl. apply sn_cand_std.
  - (* Nat *) simpl. apply sn_cand_std.
Qed.

Lemma C_usn : forall T db rho e, db_valid db -> rho_valid rho -> C T db rho e -> usn e.
Proof.
  intros T db rho e Hdb Hrho H. exact (proj1 (C_sn_cand T db rho Hdb Hrho) e H).
Qed.

Lemma C_step : forall T db rho e e', db_valid db -> rho_valid rho ->
  C T db rho e -> ustep e e' -> C T db rho e'.
Proof.
  intros T db rho e e' Hdb Hrho H Hs.
  exact (proj1 (proj2 (C_sn_cand T db rho Hdb Hrho)) e e' H Hs).
Qed.

Lemma C_multi : forall T db rho e e', db_valid db -> rho_valid rho ->
  C T db rho e -> umulti e e' -> C T db rho e'.
Proof.
  intros T db rho e e' Hdb Hrho H Hm. induction Hm as [a | a b c Hs Hrest IH].
  - assumption.
  - apply IH. apply C_step with a; assumption.
Qed.

Lemma cand_multi : forall P, sn_cand P -> forall e e', P e -> umulti e e' -> P e'.
Proof.
  intros P [Hsn [Hstep Hintro]] e e' H Hm. revert H. induction Hm as [a | a b c Hs Hrest IH]; intros H.
  - assumption.
  - apply IH. apply Hstep with a; assumption.
Qed.

Lemma C_intro : forall T db rho e, db_valid db -> rho_valid rho ->
  ~ uvalue e -> usn e -> (forall e', ustep e e' -> C T db rho e') -> C T db rho e.
Proof.
  intros T db rho e Hdb Hrho Hnv Hsn Hred.
  exact (proj2 (proj2 (C_sn_cand T db rho Hdb Hrho)) e Hnv Hsn Hred).
Qed.

Lemma C_to_Vall : forall T db rho e, C T db rho e -> uvalue e -> Vall T db rho e.
Proof.
  intros T. destruct T; intros db rho e H Hv; simpl in *.
  - assumption.
  - assumption.
  - destruct H as [_ Hval]. exact (Hval e (umulti_refl e) Hv).
  - destruct H as [_ Hval]. exact (Hval e (umulti_refl e) Hv).
  - destruct H as [_ Hval]. exact (Hval e (umulti_refl e) Hv).
Qed.

Lemma Vall_to_C : forall T db rho e, Vall T db rho e -> uvalue e -> C T db rho e.
Proof.
  intros T. destruct T; intros db rho e H Hv; simpl in *.
  - assumption.
  - assumption.
  - (* Arrow *)
    destruct e as [i | x | body | a b | body | a | | n | n b s]; simpl in H; try (exfalso; exact H).
    split.
    + apply usn_value. constructor.
    + intros v Hm Hv'. rewrite (umulti_value (ut_abs body) v (uv_abs body) Hm). simpl. exact H.
  - (* All *)
    destruct e as [i | x | body | a b | body | a | | n | n b s]; simpl in H; try (exfalso; exact H).
    split.
    + apply usn_value. constructor.
    + intros v Hm Hv'. rewrite (umulti_value (ut_tabs body) v (uv_tabs body) Hm). simpl. exact H.
  - (* Nat *)
    split.
    + apply usn_value. apply unum_uvalue. assumption.
    + intros v Hm Hv'. rewrite (umulti_value e v (unum_uvalue e H) Hm). assumption.
Qed.

(* value clause of the relation, uniform in the type *)
Lemma C_value : forall T db rho e v, db_valid db -> rho_valid rho ->
  C T db rho e -> umulti e v -> uvalue v -> Vall T db rho v.
Proof.
  intros T. destruct T; intros db rho e v Hdb Hrho H Hm Hv; simpl in *.
  - (* BVar *) exact (cand_multi (nth_cand db n) (nth_cand_valid db n Hdb) e v H Hm).
  - (* FVar *) exact (cand_multi (rho a) (Hrho a) e v H Hm).
  - (* Arrow *) destruct H as [_ Hval]. exact (Hval v Hm Hv).
  - (* All *) destruct H as [_ Hval]. exact (Hval v Hm Hv).
  - (* Nat *) destruct H as [_ Hval]. exact (Hval v Hm Hv).
Qed.

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  (* Complete the proof of normalization. *)
Qed.

End SystemFNormalizationRecursionHardTask.
