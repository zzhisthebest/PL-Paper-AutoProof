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
(* Part 1: erased term syntax (type annotations removed).        *)
(* ============================================================ *)

Inductive etm : Type :=
  | et_bvar : nat -> etm
  | et_fvar : atom -> etm
  | et_abs : etm -> etm
  | et_app : etm -> etm -> etm
  | et_tabs : etm -> etm
  | et_tapp : etm -> etm
  | et_zero : etm
  | et_succ : etm -> etm
  | et_natrec : etm -> etm -> etm -> etm.

Fixpoint erase (t : tm) : etm :=
  match t with
  | tm_bvar i => et_bvar i
  | tm_fvar x => et_fvar x
  | tm_abs _ t1 => et_abs (erase t1)
  | tm_app t1 t2 => et_app (erase t1) (erase t2)
  | tm_tabs t1 => et_tabs (erase t1)
  | tm_tapp t1 _ => et_tapp (erase t1)
  | tm_zero => et_zero
  | tm_succ t1 => et_succ (erase t1)
  | tm_natrec n b s => et_natrec (erase n) (erase b) (erase s)
  end.

Fixpoint eopen_rec (k : nat) (u t : etm) : etm :=
  match t with
  | et_bvar i => if Nat.eqb k i then u else et_bvar i
  | et_fvar x => et_fvar x
  | et_abs t1 => et_abs (eopen_rec (S k) u t1)
  | et_app t1 t2 => et_app (eopen_rec k u t1) (eopen_rec k u t2)
  | et_tabs t1 => et_tabs (eopen_rec k u t1)
  | et_tapp t1 => et_tapp (eopen_rec k u t1)
  | et_zero => et_zero
  | et_succ t1 => et_succ (eopen_rec k u t1)
  | et_natrec n b s =>
      et_natrec (eopen_rec k u n) (eopen_rec k u b) (eopen_rec k u s)
  end.

Definition eopen (t u : etm) : etm := eopen_rec 0 u t.

Fixpoint esubst (sigma : atom -> etm) (t : etm) : etm :=
  match t with
  | et_bvar i => et_bvar i
  | et_fvar x => sigma x
  | et_abs t1 => et_abs (esubst sigma t1)
  | et_app t1 t2 => et_app (esubst sigma t1) (esubst sigma t2)
  | et_tabs t1 => et_tabs (esubst sigma t1)
  | et_tapp t1 => et_tapp (esubst sigma t1)
  | et_zero => et_zero
  | et_succ t1 => et_succ (esubst sigma t1)
  | et_natrec n b s =>
      et_natrec (esubst sigma n) (esubst sigma b) (esubst sigma s)
  end.

Inductive e_numeric_value : etm -> Prop :=
  | en_zero : e_numeric_value et_zero
  | en_succ : forall n, e_numeric_value n -> e_numeric_value (et_succ n).

Inductive ev_value : etm -> Prop :=
  | ev_abs : forall t, ev_value (et_abs t)
  | ev_tabs : forall t, ev_value (et_tabs t)
  | ev_nat : forall n, e_numeric_value n -> ev_value n.

Inductive estep : etm -> etm -> Prop :=
  | ES_AppAbs : forall t v,
      ev_value v -> estep (et_app (et_abs t) v) (eopen t v)
  | ES_App1 : forall t1 t1' t2,
      estep t1 t1' -> estep (et_app t1 t2) (et_app t1' t2)
  | ES_App2 : forall v1 t2 t2',
      ev_value v1 -> estep t2 t2' -> estep (et_app v1 t2) (et_app v1 t2')
  | ES_TAppTabs : forall t, estep (et_tapp (et_tabs t)) t
  | ES_TApp : forall t t', estep t t' -> estep (et_tapp t) (et_tapp t')
  | ES_Succ : forall t t', estep t t' -> estep (et_succ t) (et_succ t')
  | ES_RecArg : forall n n' b s,
      estep n n' -> estep (et_natrec n b s) (et_natrec n' b s)
  | ES_RecBase : forall n b b' s,
      e_numeric_value n -> estep b b' ->
      estep (et_natrec n b s) (et_natrec n b' s)
  | ES_RecStep : forall n b s s',
      e_numeric_value n -> ev_value b -> estep s s' ->
      estep (et_natrec n b s) (et_natrec n b s')
  | ES_RecZero : forall b s,
      ev_value b -> ev_value s -> estep (et_natrec et_zero b s) b
  | ES_RecSucc : forall n b s,
      e_numeric_value n -> ev_value b -> ev_value s ->
      estep (et_natrec (et_succ n) b s)
        (et_app (et_app s n) (et_natrec n b s)).

Inductive eSN : etm -> Prop :=
  | eSN_intro : forall t, (forall u, estep t u -> eSN u) -> eSN t.

Hint Constructors e_numeric_value ev_value eSN : core.

(* ---------- erasure lemmas ---------- *)

Lemma erase_open_tm_rec : forall (t : tm) (k : nat) (u : tm),
  erase (open_tm_rec k u t) = eopen_rec k (erase u) (erase t).
Proof.
  induction t; intros k u; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - reflexivity.
  - f_equal. apply IHt.
  - rewrite IHt1, IHt2. reflexivity.
  - f_equal. apply IHt.
  - rewrite IHt. reflexivity.
  - reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2, IHt3. reflexivity.
Qed.

Lemma erase_open_tm : forall (t u : tm),
  erase (open_tm t u) = eopen (erase t) (erase u).
Proof. intros; apply erase_open_tm_rec. Qed.

Lemma erase_open_tm_ty_rec : forall (t : tm) (k : nat) (U : ty),
  erase (open_tm_ty_rec k U t) = erase t.
Proof.
  induction t; intros k U; simpl; auto.
  all: try (f_equal; auto).
  all: try (rewrite IHt1, IHt2; reflexivity).
  all: try (rewrite IHt; reflexivity).
  all: try (rewrite IHt1, IHt2, IHt3; reflexivity).
Qed.

Lemma erase_open_tm_ty : forall (t : tm) (U : ty),
  erase (open_tm_ty t U) = erase t.
Proof. intros; apply erase_open_tm_ty_rec. Qed.

Lemma erase_ty_subst : forall (X : atom) (U : ty) (t : tm),
  erase (tm_ty_subst X U t) = erase t.
Proof.
  induction t; simpl; auto.
  all: try (f_equal; auto).
  all: try (rewrite IHt1, IHt2; reflexivity).
  all: try (rewrite IHt; reflexivity).
  all: try (rewrite IHt1, IHt2, IHt3; reflexivity).
Qed.

Lemma erase_tm_subst : forall (x : atom) (s t : tm),
  erase (tm_subst x s t) = esubst (fun y => if Nat.eqb x y then erase s else et_fvar y) (erase t).
Proof.
  induction t; simpl; auto.
  all: try (f_equal; auto).
  all: try (match goal with
            | |- context [Nat.eqb ?a ?b] => destruct (Nat.eqb a b); auto
            end).
  all: try (rewrite IHt1, IHt2; reflexivity).
  all: try (rewrite IHt; reflexivity).
  all: try (rewrite IHt1, IHt2, IHt3; reflexivity).
Qed.

Lemma erase_numeric : forall n, numeric_value n -> e_numeric_value (erase n).
Proof. induction 1; simpl; constructor; auto. Qed.

Lemma erase_value : forall v, value v -> ev_value (erase v).
Proof. induction 1; simpl; constructor; auto using erase_numeric. Qed.

(* ---------- original steps erase to erased steps ---------- *)

Lemma estep_erase : forall t u, step t u -> estep (erase t) (erase u).
Proof.
  induction 1; simpl.
  - (* ST_AppAbs *)
    rewrite erase_open_tm. apply ES_AppAbs. apply erase_value; auto.
  - (* ST_App1 *) apply ES_App1; auto.
  - (* ST_App2 *) apply ES_App2; auto using erase_value.
  - (* ST_TAppTabs *)
    rewrite erase_open_tm_ty. apply ES_TAppTabs.
  - (* ST_TApp *) apply ES_TApp; auto.
  - (* ST_Succ *) apply ES_Succ; auto.
  - (* ST_RecArg *) apply ES_RecArg; auto.
  - (* ST_RecBase *) apply ES_RecBase; auto using erase_numeric.
  - (* ST_RecStep *)
    apply ES_RecStep; auto using erase_numeric, erase_value.
  - (* ST_RecZero *) apply ES_RecZero; auto using erase_value.
  - (* ST_RecSucc *)
    apply ES_RecSucc; auto using erase_numeric, erase_value.
Qed.

(* If the erasure is strongly normalizing for the erased step, so is t. *)
Lemma eSN_erase_SN : forall t, eSN (erase t) -> strongly_normalizing t.
Proof.
  intros t H.
  remember (erase t) as e eqn:He.
  revert t He.
  induction H as [e Hred IH]; intros t He.
  apply SN_intro. intros u Hstep.
  apply (IH (erase u)).
  - rewrite He. apply estep_erase; auto.
  - reflexivity.
Qed.

(* ============================================================ *)
(* Part 2: free variables, freshness, and type-level lemmas.     *)
(* ============================================================ *)

Fixpoint fta (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow T1 T2 => fta T1 ++ fta T2
  | Ty_All T1 => fta T1
  | Ty_Nat => []
  end.

Fixpoint max_list (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: xs => Nat.max x (max_list xs)
  end.

Lemma max_list_ub : forall l x, In x l -> x <= max_list l.
Proof.
  induction l as [|y ys IH]; intros x Hin; simpl in *.
  - destruct Hin.
  - destruct Hin as [-> | Hin].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; eauto | apply Nat.le_max_r].
Qed.

Definition fresh (l : list atom) : atom := S (max_list l).

Lemma fresh_notin : forall l, ~ In (fresh l) l.
Proof.
  intros l Hin. unfold fresh in Hin.
  pose proof (max_list_ub l (S (max_list l)) Hin). lia.
Qed.

Fixpoint tm_fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs _ t1 => tm_fv t1
  | tm_app t1 t2 => tm_fv t1 ++ tm_fv t2
  | tm_tabs t1 => tm_fv t1
  | tm_tapp t1 _ => tm_fv t1
  | tm_zero => []
  | tm_succ t1 => tm_fv t1
  | tm_natrec n b s => tm_fv n ++ tm_fv b ++ tm_fv s
  end.

Fixpoint tm_occ (x : atom) (t : tm) : Prop :=
  match t with
  | tm_bvar _ => False
  | tm_fvar y => x = y
  | tm_abs _ t1 => tm_occ x t1
  | tm_app t1 t2 => tm_occ x t1 \/ tm_occ x t2
  | tm_tabs t1 => tm_occ x t1
  | tm_tapp t1 _ => tm_occ x t1
  | tm_zero => False
  | tm_succ t1 => tm_occ x t1
  | tm_natrec n b s => tm_occ x n \/ tm_occ x b \/ tm_occ x s
  end.

Lemma tm_occ_fv : forall x t, tm_occ x t <-> In x (tm_fv t).
Proof.
  intros x t. induction t; simpl.
  all: try (repeat rewrite in_app_iff; firstorder congruence).
Qed.

Fixpoint etm_fv (t : etm) : list atom :=
  match t with
  | et_bvar _ => []
  | et_fvar x => [x]
  | et_abs t1 => etm_fv t1
  | et_app t1 t2 => etm_fv t1 ++ etm_fv t2
  | et_tabs t1 => etm_fv t1
  | et_tapp t1 => etm_fv t1
  | et_zero => []
  | et_succ t1 => etm_fv t1
  | et_natrec n b s => etm_fv n ++ etm_fv b ++ etm_fv s
  end.

Fixpoint eocc (x : atom) (t : etm) : Prop :=
  match t with
  | et_bvar _ => False
  | et_fvar y => x = y
  | et_abs t1 => eocc x t1
  | et_app t1 t2 => eocc x t1 \/ eocc x t2
  | et_tabs t1 => eocc x t1
  | et_tapp t1 => eocc x t1
  | et_zero => False
  | et_succ t1 => eocc x t1
  | et_natrec n b s => eocc x n \/ eocc x b \/ eocc x s
  end.

Lemma eocc_fv : forall x t, eocc x t <-> In x (etm_fv t).
Proof.
  intros x t. induction t; simpl.
  all: try (repeat rewrite in_app_iff; firstorder congruence).
Qed.

Lemma erase_fv : forall t, etm_fv (erase t) = tm_fv t.
Proof.
  induction t; simpl; auto.
  all: try (rewrite IHt1, IHt2; reflexivity).
  all: try (rewrite IHt1, IHt2, IHt3; reflexivity).
Qed.

Lemma erase_occ : forall x t, eocc x (erase t) <-> tm_occ x t.
Proof.
  intros x t. induction t; simpl.
  all: try (repeat rewrite in_app_iff; firstorder congruence).
Qed.

(* opening with a free variable preserves/reflects occurrences of other vars *)

Lemma open_tm_occ : forall (t : tm) (k : nat) (y x : atom),
  x <> y -> (tm_occ x (open_tm_rec k (tm_fvar y) t) <-> tm_occ x t).
Proof.
  induction t; intros k y x Hxy; simpl.
  all: try (repeat rewrite in_app_iff; firstorder congruence).
  all: try (match goal with
            | |- context [Nat.eqb ?a ?b] =>
                destruct (Nat.eqb a b); simpl; firstorder congruence
            end).
Qed.

Lemma open_tm_ty_occ : forall (t : tm) (k : nat) (U : ty) (x : atom),
  tm_occ x (open_tm_ty_rec k U t) <-> tm_occ x t.
Proof.
  induction t; intros k U x; simpl.
  all: try (repeat rewrite in_app_iff; firstorder congruence).
Qed.

(* free type atoms through opening *)

Lemma fta_open_ty_rec : forall (T : ty) (k : nat) (U : ty) (X : atom),
  In X (fta T) -> In X (fta (open_ty_rec k U T)).
Proof.
  induction T as [n | a | T1 IH1 T2 IH2 | T1 IH1 | ];
    intros k U X H; simpl in *.
  - destruct H.
  - auto.
  - apply in_app_iff in H. apply in_app_iff. destruct H as [H|H]; auto.
  - apply IH1. auto.
  - destruct H.
Qed.

Lemma fta_open_ty : forall (T U : ty) (X : atom),
  In X (fta T) -> In X (fta (open_ty T U)).
Proof. intros; apply fta_open_ty_rec; auto. Qed.

(* ---------- wf_ty: weakening, locally closed, free atoms ---------- *)

Lemma wf_ty_weaken : forall Delta T, wf_ty Delta T -> forall X, wf_ty (X :: Delta) T.
Proof.
  intros Delta T H. induction H; intros Y.
  - apply WF_Var. simpl. right; auto.
  - apply WF_Arrow; auto.
  - apply WF_All. intros Z HZ. simpl. apply H1; auto.
  - apply WF_Nat.
Qed.

Lemma lc_ty_open_fvar_inv : forall (T : ty) (k : nat) (X : atom),
  lc_ty_at k (open_ty_rec k (Ty_FVar X) T) -> lc_ty_at (S k) T.
Proof.
  induction T as [n | a | T1 IH1 T2 IH2 | T1 IH1 | ];
    intros k X H; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. constructor. lia.
    + inversion H; subst. constructor. apply Nat.eqb_neq in E. lia.
  - constructor.
  - inversion H; subst. constructor; auto.
  - apply lc_ty_all. apply IH1 with (k := S k).
    inversion H; subst. assumption.
  - inversion H. constructor.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> lc_ty_at 0 T.
Proof.
  intros Delta T H. induction H.
  - constructor.
  - constructor; auto.
  - apply lc_ty_all.
    set (X := fresh (L ++ fta T)).
    apply lc_ty_open_fvar_inv with (k := 0) (X := X).
    apply H1.
    unfold X. intro Hin. apply fresh_notin in Hin. apply Hin.
    apply in_app_iff. auto.
  - constructor.
Qed.

Lemma wf_ty_fta : forall Delta T, wf_ty Delta T -> forall X, In X (fta T) -> In X Delta.
Proof.
  intros Delta T H. induction H; intros X HX; simpl in *.
  - destruct HX as [-> | []]. auto.
  - apply in_app_iff in HX. destruct HX as [HX | HX]; auto.
  - set (Y := fresh (L ++ fta T ++ [X])).
    assert (HYL : ~ In Y L).
    { unfold Y. intro Hin. apply fresh_notin in Hin. apply Hin.
      apply in_app_iff. auto. }
    assert (HYX : X <> Y).
    { unfold Y. intro E. subst. apply fresh_notin in E. apply E.
      apply in_app_iff. right. apply in_app_iff. left. reflexivity. }
    assert (Hin : In X (fta (open_ty T (Ty_FVar Y)))).
    { apply fta_open_ty. auto. }
    specialize (H1 Y HYL X Hin). simpl in H1.
    destruct H1 as [H1 | H1]; auto. subst. contradiction.
  - destruct HX.
Qed.

(* ---------- substitution of free type atoms in types ---------- *)

Lemma ty_subst_open_ty_rec : forall (T : ty) (k : nat) (U V : ty) (X : atom),
  ty_subst X V (open_ty_rec k U T) =
  open_ty_rec k (ty_subst X V U) (ty_subst X V T).
Proof.
  induction T as [n | a | T1 IH1 T2 IH2 | T1 IH1 | ];
    intros k U V X; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - f_equal. apply IH1.
  - reflexivity.
Qed.

Lemma ty_subst_fvar_open : forall (T : ty) (k : nat) (U : ty) (X : atom),
  ~ In X (fta T) ->
  ty_subst X U (open_ty_rec k (Ty_FVar X) T) = open_ty_rec k U T.
Proof.
  induction T as [n | a | T1 IH1 T2 IH2 | T1 IH1 | ];
    intros k U X Hnot; simpl in *.
  - destruct (Nat.eqb k n); reflexivity.
  - assert (HaX : a <> X) by (intro E; subst; apply Hnot; simpl; auto).
    destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E. contradiction.
    + reflexivity.
  - assert (H1 : ~ In X (fta T1)).
    { intro Hin. apply Hnot. apply in_app_iff. left; auto. }
    assert (H2 : ~ In X (fta T2)).
    { intro Hin. apply Hnot. apply in_app_iff. right; auto. }
    rewrite IH1 by auto. rewrite IH2 by auto. reflexivity.
  - f_equal. apply IH1. auto.
  - reflexivity.
Qed.

Lemma wf_ty_subst_gen : forall D T, wf_ty D T ->
  forall X U Delta, D = X :: Delta -> wf_ty Delta U ->
  wf_ty Delta (ty_subst X U T).
Proof.
  intros D T H. induction H; intros X U Delta Heq HwU; subst.
  - destruct (Nat.eqb X X0) eqn:E.
    + apply Nat.eqb_eq in E. subst. auto.
    + apply WF_Var. apply Nat.eqb_neq in E.
      destruct H as [-> | H]; auto. contradiction.
  - apply WF_Arrow; auto.
  - apply WF_All with (L := X :: L).
    intros Y HY.
    assert (HYL : ~ In Y L) by (intro Ein; apply HY; simpl; auto).
    specialize (H1 Y HYL). simpl in H1.
    specialize (H1 X U (Y :: Delta) eq_refl (wf_ty_weaken Delta U Y HwU)).
    rewrite ty_subst_open_ty_rec in H1.
    assert (Esub : ty_subst X U (Ty_FVar Y) = Ty_FVar Y).
    { destruct (Nat.eqb X Y) eqn:E.
      - apply Nat.eqb_eq in E. subst. exfalso. apply HY. simpl.
        apply in_app_iff. auto.
      - reflexivity. }
    rewrite Esub in H1. simpl in H1. exact H1.
  - apply WF_Nat.
Qed.

Lemma wf_ty_subst : forall Delta X U T,
  wf_ty (X :: Delta) T -> wf_ty Delta U -> wf_ty Delta (ty_subst X U T).
Proof. intros; eapply wf_ty_subst_gen; eauto. Qed.

Lemma wf_ty_open : forall Delta T U,
  wf_ty Delta (Ty_All T) -> wf_ty Delta U -> wf_ty Delta (open_ty T U).
Proof.
  intros Delta T U HAll HU.
  inversion HAll as [| | L D Tb Hbody | ]; subst.
  set (X := fresh (L ++ fta T)).
  assert (HXL : ~ In X L).
  { unfold X. intro Hin. apply fresh_notin in Hin. apply Hin.
    apply in_app_iff. auto. }
  assert (HXf : ~ In X (fta T)).
  { unfold X. intro Hin. apply fresh_notin in Hin. apply Hin.
    apply in_app_iff. right; auto. }
  specialize (Hbody X HXL).
  pose proof (wf_ty_subst Delta X U (open_ty T (Ty_FVar X)) Hbody HU) as Hsub.
  rewrite ty_subst_fvar_open in Hsub; auto.
Qed.

(* ---------- every well-typed term has a well-formed type ---------- *)

Lemma wf_ty_arrow_inv : forall Delta T1 T2,
  wf_ty Delta (Ty_Arrow T1 T2) -> wf_ty Delta T2.
Proof. intros Delta T1 T2 H; inversion H; auto. Qed.

Lemma typing_wf : forall Delta Gamma t T, has_type Delta Gamma t T -> wf_ty Delta T.
Proof.
  intros Delta Gamma t T H. induction H.
  - auto.
  - apply WF_Arrow; auto.
  - apply wf_ty_arrow_inv in IHhas_type1. auto.
  - apply WF_All with (L := L). auto.
  - apply wf_ty_open with (T := T); auto.
  - apply WF_Nat.
  - auto.
  - auto.
Qed.

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  admit.
Admitted.

End SystemFNormalizationRecursionHardTask.
