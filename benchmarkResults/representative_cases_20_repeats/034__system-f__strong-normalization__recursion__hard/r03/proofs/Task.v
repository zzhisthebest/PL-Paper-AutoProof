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

(* Construct the logical relation and supporting proofs here. *)

(* ============================================================ *)
(* Part 1: basic facts about values, multi-step, and SN.        *)
(* ============================================================ *)

Hint Constructors numeric_value : core.

Lemma numeric_value_no_step :
  forall n u, numeric_value n -> step n u -> False.
Proof.
  intros n u Hnv. revert u. induction Hnv as [| n Hnv IH]; intros u Hs.
  - inversion Hs.
  - inversion Hs; subst; eauto.
Qed.

Lemma value_no_step :
  forall v u, value v -> step v u -> False.
Proof.
  intros v u Hv. revert u. induction Hv as [T t Hlc | t Hlc | n Hnv]; intros u Hs.
  - inversion Hs.
  - inversion Hs.
  - eapply numeric_value_no_step; eauto.
Qed.

Lemma SN_intro' :
  forall t, (forall u, step t u -> strongly_normalizing u) ->
            strongly_normalizing t.
Proof. intros t H; constructor; assumption. Qed.

Lemma SN_no_step :
  forall t, (forall u, step t u -> False) -> strongly_normalizing t.
Proof.
  intros t H. apply SN_intro'. intros u Hu. exfalso. apply (H u Hu).
Qed.

Lemma SN_step :
  forall t u, strongly_normalizing t -> step t u -> strongly_normalizing u.
Proof.
  intros t u H. induction H as [t Hstep]. intros Hu. apply Hstep. assumption.
Qed.

Lemma SN_value :
  forall v, value v -> strongly_normalizing v.
Proof.
  intros v Hv. apply SN_no_step. intros u Hu.
  eapply value_no_step; eauto.
Qed.

Lemma SN_succ :
  forall t, strongly_normalizing t -> strongly_normalizing (tm_succ t).
Proof.
  intros t H. induction H as [t Hstep IH].
  apply SN_intro'. intros u Hu. inversion Hu; subst.
  apply IH. assumption.
Qed.

Lemma multi_single :
  forall x y, step x y -> multi x y.
Proof.
  intros x y H. eapply multi_step. exact H. apply multi_refl.
Qed.

Lemma multi_trans :
  forall x y z, multi x y -> multi y z -> multi x z.
Proof.
  intros x y z Hxy. induction Hxy as [x | x y' z' Hstep Hm IH]; intros Hyz.
  - assumption.
  - eapply multi_step. exact Hstep. apply IH. assumption.
Qed.

Lemma multi_step_r :
  forall x y z, multi x y -> step y z -> multi x z.
Proof.
  intros x y z Hm. induction Hm as [x | x y' z' Hstep Hm IH]; intros Hyz.
  - apply multi_single. assumption.
  - eapply multi_step. exact Hstep. apply IH. assumption.
Qed.

Lemma multi_value_inv :
  forall v u, value v -> multi v u -> u = v.
Proof.
  intros v u Hv Hm. induction Hm as [x | x y z Hstep Hm IH].
  - reflexivity.
  - exfalso. eapply value_no_step; eauto.
Qed.

Lemma numeric_value_inv :
  forall n, numeric_value n -> n = tm_zero \/ (exists m, n = tm_succ m).
Proof.
  intros n H. induction H as [| n H IH].
  - left; reflexivity.
  - right; exists n; reflexivity.
Qed.

Lemma numeric_value_app :
  forall t1 t2, numeric_value (tm_app t1 t2) -> False.
Proof.
  intros t1 t2 H. destruct (numeric_value_inv _ H) as [E | [m E]]; discriminate.
Qed.

Lemma numeric_value_tapp :
  forall t T, numeric_value (tm_tapp t T) -> False.
Proof.
  intros t T H. destruct (numeric_value_inv _ H) as [E | [m E]]; discriminate.
Qed.

Lemma numeric_value_natrec :
  forall n b s, numeric_value (tm_natrec n b s) -> False.
Proof.
  intros n b s H. destruct (numeric_value_inv _ H) as [E | [m E]]; discriminate.
Qed.

Lemma numeric_value_abs :
  forall T t, numeric_value (tm_abs T t) -> False.
Proof.
  intros T t H. destruct (numeric_value_inv _ H) as [E | [m E]]; discriminate.
Qed.

Lemma numeric_value_tabs :
  forall t, numeric_value (tm_tabs t) -> False.
Proof.
  intros t H. destruct (numeric_value_inv _ H) as [E | [m E]]; discriminate.
Qed.

Lemma numeric_value_bvar :
  forall i, numeric_value (tm_bvar i) -> False.
Proof.
  intros i H. destruct (numeric_value_inv _ H) as [E | [m E]]; discriminate.
Qed.

Lemma numeric_value_fvar :
  forall x, numeric_value (tm_fvar x) -> False.
Proof.
  intros x H. destruct (numeric_value_inv _ H) as [E | [m E]]; discriminate.
Qed.

Lemma value_cases :
  forall v, value v ->
    (exists T t, v = tm_abs T t) \/
    (exists t, v = tm_tabs t) \/
    numeric_value v.
Proof.
  intros v H. destruct H as [T t H | t H | n H].
  - left. exists T, t. reflexivity.
  - right. left. exists t. reflexivity.
  - right. right. assumption.
Qed.

Lemma value_not_app : forall t1 t2, value (tm_app t1 t2) -> False.
Proof.
  intros t1 t2 Hv. destruct (value_cases _ Hv) as [[T [t E]] | [[t E] | Hn]].
  - discriminate.
  - discriminate.
  - apply numeric_value_app in Hn. assumption.
Qed.

Lemma value_not_tapp : forall t T, value (tm_tapp t T) -> False.
Proof.
  intros t T Hv. destruct (value_cases _ Hv) as [[T' [t' E]] | [[t' E] | Hn]].
  - discriminate.
  - discriminate.
  - apply numeric_value_tapp in Hn. assumption.
Qed.

Lemma value_not_natrec : forall n b s, value (tm_natrec n b s) -> False.
Proof.
  intros n b s Hv. destruct (value_cases _ Hv) as [[T [t E]] | [[t E] | Hn]].
  - discriminate.
  - discriminate.
  - apply numeric_value_natrec in Hn. assumption.
Qed.

Lemma value_not_bvar : forall i, value (tm_bvar i) -> False.
Proof.
  intros i Hv. destruct (value_cases _ Hv) as [[T [t E]] | [[t E] | Hn]].
  - discriminate.
  - discriminate.
  - apply numeric_value_bvar in Hn. assumption.
Qed.

Lemma value_not_fvar : forall x, value (tm_fvar x) -> False.
Proof.
  intros x Hv. destruct (value_cases _ Hv) as [[T [t E]] | [[t E] | Hn]].
  - discriminate.
  - discriminate.
  - apply numeric_value_fvar in Hn. assumption.
Qed.

Lemma value_numeric : forall n, numeric_value n -> value n.
Proof. intros n H. constructor. assumption. Qed.

Lemma SN_numeric : forall n, numeric_value n -> strongly_normalizing n.
Proof. intros n H. apply SN_value. apply value_numeric. assumption. Qed.

Lemma multi_numeric_no_step :
  forall n u, numeric_value n -> multi n u -> u = n.
Proof. intros n u Hn. apply multi_value_inv. apply value_numeric. assumption. Qed.

(* ============================================================ *)
(* Part 2: the type-indexed logical relation.                   *)
(* ============================================================ *)

Fixpoint ty_subst_env (rho : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => rho X
  | Ty_Arrow A B => Ty_Arrow (ty_subst_env rho A) (ty_subst_env rho B)
  | Ty_All B => Ty_All (ty_subst_env rho B)
  | Ty_Nat => Ty_Nat
  end.

Fixpoint tm_subst_all (rho : atom -> ty) (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_abs T t1 => tm_abs (ty_subst_env rho T) (tm_subst_all rho sigma t1)
  | tm_app t1 t2 => tm_app (tm_subst_all rho sigma t1) (tm_subst_all rho sigma t2)
  | tm_tabs t1 => tm_tabs (tm_subst_all rho sigma t1)
  | tm_tapp t1 T => tm_tapp (tm_subst_all rho sigma t1) (ty_subst_env rho T)
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (tm_subst_all rho sigma t1)
  | tm_natrec n b s =>
      tm_natrec (tm_subst_all rho sigma n) (tm_subst_all rho sigma b)
                (tm_subst_all rho sigma s)
  end.

Record SemTy : Type := {
  syn : ty;
  relv : tm -> Prop
}.

Definition C_ty (S : SemTy) (t : tm) : Prop :=
  strongly_normalizing t /\
  (forall v, multi t v -> value v -> relv S v).

Definition sem_nat : SemTy :=
  {| syn := Ty_Nat; relv := fun _ => True |}.

Definition sem_arrow (SA SB : SemTy) : SemTy :=
  {| syn := Ty_Arrow (syn SA) (syn SB);
     relv := fun v => forall u, C_ty SA u -> C_ty SB (tm_app v u) |}.

Fixpoint sem_ty (T : ty) (bv : list SemTy) (fv : atom -> SemTy) : SemTy :=
  match T with
  | Ty_BVar i => nth i bv sem_nat
  | Ty_FVar X => fv X
  | Ty_Nat => sem_nat
  | Ty_Arrow A B => sem_arrow (sem_ty A bv fv) (sem_ty B bv fv)
  | Ty_All B =>
      {| syn := Ty_All (ty_subst_env (fun X => syn (fv X)) B);
         relv := fun v =>
           forall S : SemTy, C_ty (sem_ty B (S :: bv) fv) (tm_tapp v (syn S)) |}
  end.

(* ---------------- basic properties of the relation ---------------- *)

Lemma C_SN : forall S t, C_ty S t -> strongly_normalizing t.
Proof. intros S t [H _]. exact H. Qed.

Lemma C_value_cond :
  forall S t v, C_ty S t -> multi t v -> value v -> relv S v.
Proof. intros S t v [_ H] Hm Hv. apply H; assumption. Qed.

Lemma C_step :
  forall S t t', C_ty S t -> step t t' -> C_ty S t'.
Proof.
  intros S t t' [Hsn Hv] Hs. split.
  - eapply SN_step; eauto.
  - intros v Hm Hval. apply Hv.
    + exact (multi_step t t' v Hs Hm).
    + exact Hval.
Qed.

Lemma C_multi :
  forall S t t', C_ty S t -> multi t t' -> C_ty S t'.
Proof.
  intros S t t' Hc Hm. induction Hm as [x | x y z Hs Hm IH].
  - assumption.
  - apply IH. eapply C_step; eauto.
Qed.

Lemma C_of_value :
  forall S v, value v -> relv S v -> C_ty S v.
Proof.
  intros S v Hval Hrel. split.
  - apply SN_value. assumption.
  - intros u Hm _. rewrite (multi_value_inv _ _ Hval Hm). assumption.
Qed.

Lemma C_multi_value :
  forall S (t v : tm), multi t v -> C_ty S t -> value v -> relv S v.
Proof.
  intros S t v Hm. induction Hm as [x | x y z Hst Hm IH].
  - intros Hc Hv. destruct Hc as [_ Hvc]. apply (Hvc x (multi_refl x) Hv).
  - intros Hc Hv. apply IH.
    + eapply C_step; eauto.
    + exact Hv.
Qed.

Lemma multi_no_step :
  forall t v, (forall y, step t y -> False) -> multi t v -> v = t.
Proof.
  intros t v Hns Hm. induction Hm as [x | x y z Hst Hm IH].
  - reflexivity.
  - exfalso. apply (Hns y Hst).
Qed.

Lemma C_of_no_step_relv :
  forall S (t : tm),
    (forall y, step t y -> False) -> relv S t -> C_ty S t.
Proof.
  intros S t Hns Hrel. split.
  - apply SN_no_step. exact Hns.
  - intros v Hm Hv. rewrite (multi_no_step _ _ Hns Hm). exact Hrel.
Qed.

Lemma C_of_steps :
  forall S (t : tm),
    ~ value t -> (forall y, step t y -> C_ty S y) -> C_ty S t.
Proof.
  intros S t Hnv Hst. split.
  - apply SN_intro'. intros y Hy. apply (C_SN S y). apply Hst. exact Hy.
  - intros v Hm Hv. destruct Hm as [x | x y z Hst' Hm].
    + exfalso. apply Hnv. exact Hv.
    + apply (C_multi_value S y z Hm (Hst y Hst') Hv).
Qed.

(* ---------------- inversion lemmas for the step relation -------- *)

Lemma step_app_inv :
  forall f u y, step (tm_app f u) y ->
    (exists T t0, f = tm_abs T t0 /\ locally_closed_tm (tm_abs T t0) /\
                  value u /\ y = open_tm t0 u) \/
    (exists f', y = tm_app f' u /\ step f f') \/
    (exists u', y = tm_app f u' /\ value f /\ step u u').
Proof.
  intros f u y H. inversion H; subst; eauto 8.
Qed.

Lemma step_tapp_inv :
  forall f U y, step (tm_tapp f U) y ->
    (exists t0, f = tm_tabs t0 /\ locally_closed_tm (tm_tabs t0) /\
                y = open_tm_ty t0 U) \/
    (exists f', y = tm_tapp f' U /\ step f f').
Proof.
  intros f U y H. inversion H; subst; eauto 8.
Qed.

Lemma step_succ_inv :
  forall t y, step (tm_succ t) y -> exists t', y = tm_succ t' /\ step t t'.
Proof.
  intros t y H. inversion H; subst; eauto.
Qed.

Lemma step_natrec_inv :
  forall n b s y, step (tm_natrec n b s) y ->
    (exists n', y = tm_natrec n' b s /\ step n n') \/
    (exists b', numeric_value n /\ y = tm_natrec n b' s /\ step b b') \/
    (exists s', numeric_value n /\ value b /\ y = tm_natrec n b s' /\ step s s') \/
    (numeric_value n /\ value b /\ value s /\ y = b) \/
    (exists m, n = tm_succ m /\ numeric_value m /\ value b /\ value s /\
               y = tm_app (tm_app s m) (tm_natrec m b s)).
Proof.
  intros n b s y H. inversion H; subst; eauto 10.
Qed.

(* ---------------- application, abstraction, type application --- *)

Lemma C_app :
  forall SA SB f u,
    C_ty (sem_arrow SA SB) f -> C_ty SA u -> C_ty SB (tm_app f u).
Proof.
  intros SA SB f u Hf Hu.
  destruct Hf as [Hsn Hval].
  revert SB u Hu Hval.
  induction Hsn as [f Hstep IH].
  intros SB u Hu Hval.
  apply C_of_steps.
  - intro Hnvapp; exact (value_not_app _ _ Hnvapp).
  - intros y Hy.
    destruct (step_app_inv _ _ _ Hy) as
      [[T [t0 [Ef [Hlc [Hvu Ey]]]]] | [[f' [Ey Hst]] | [u' [Ey [Hvf Hst]]]]];
      subst.
    + (* beta redex: f = tm_abs T t0, y = open_tm t0 u *)
      assert (Hrel : relv (sem_arrow SA SB) (tm_abs T t0)).
      { apply Hval.
        - apply multi_refl.
        - apply v_abs. exact Hlc. }
      simpl in Hrel.
      eapply C_step.
      * apply Hrel. exact Hu.
      * apply ST_AppAbs; assumption.
    + (* f steps *)
      apply (IH f' Hst SB u Hu).
      intros v Hm Hv. apply Hval.
      * eapply multi_step; eauto.
      * exact Hv.
    + (* argument steps; f is a value *)
      assert (Hrel : relv (sem_arrow SA SB) f).
      { apply Hval.
        - apply multi_refl.
        - exact Hvf. }
      simpl in Hrel.
      apply Hrel.
      eapply C_step; eauto.
Qed.

Lemma C_abs :
  forall SA SB (T : ty) body,
    (forall u, C_ty SA u -> C_ty SB (open_tm body u)) ->
    C_ty (sem_arrow SA SB) (tm_abs T body).
Proof.
  intros SA SB T body Hbody.
  apply C_of_no_step_relv.
  - intros y Hy. inversion Hy.
  - simpl. intros u Hu.
    cut (forall u, strongly_normalizing u ->
                   C_ty SA u -> C_ty SB (tm_app (tm_abs T body) u)).
    { intros Hmain. apply Hmain. apply C_SN in Hu. exact Hu. exact Hu. }
    clear u Hu.
    intros u Hsn. induction Hsn as [u Hstepu IHu]. intros Hu.
    apply C_of_steps.
    + intro Hnvapp; exact (value_not_app _ _ Hnvapp).
    + intros y Hy.
      destruct (step_app_inv _ _ _ Hy) as
        [[T' [t0 [Ef [Hlc [Hvu Ey]]]]] | [[f' [Ey Hst]] | [u' [Ey [Hvf Hst]]]]];
        subst.
      * (* the abstraction is exactly tm_abs T body *)
        injection Ef as ET Et0. subst. apply Hbody. exact Hu.
      * (* an abstraction does not step *)
        inversion Hst.
      * (* argument steps *)
        apply IHu.
        -- exact Hst.
        -- eapply C_step; eauto.
Qed.

Lemma C_tapp_tabs :
  forall S body U,
    C_ty S (open_tm_ty body U) -> C_ty S (tm_tapp (tm_tabs body) U).
Proof.
  intros S body U Hc.
  apply C_of_steps.
  - intro Hnvtapp; exact (value_not_tapp _ _ Hnvtapp).
  - intros y Hy.
    destruct (step_tapp_inv _ _ _ Hy) as
      [[t0 [Ef [Hlc Ey]]] | [f' [Ey Hst]]]; subst.
    + injection Ef as E. subst. exact Hc.
    + inversion Hst.
Qed.

Lemma C_tapp :
  forall (B : ty) (bv : list SemTy) (fv : atom -> SemTy) (u : tm) (U : ty) (SU : SemTy),
    syn SU = U ->
    locally_closed_ty U ->
    C_ty (sem_ty (Ty_All B) bv fv) u ->
    C_ty (sem_ty B (SU :: bv) fv) (tm_tapp u U).
Proof.
  intros B bv fv u U SU Esyn Hlc Hc.
  destruct Hc as [Hsn Hval].
  revert U SU Esyn Hlc Hval.
  induction Hsn as [u Hstepu IHu].
  intros U SU Esyn Hlc Hval. subst U.
  apply C_of_steps.
  - intro Hnvtapp; exact (value_not_tapp _ _ Hnvtapp).
  - intros y Hy.
    destruct (step_tapp_inv _ _ _ Hy) as
      [[t0 [Ef [HlcT Ey]]] | [f' [Ey Hst]]].
    + (* u = tm_tabs t0, y = open_tm_ty t0 U *)
      subst u. subst y.
      assert (Hrel : relv (sem_ty (Ty_All B) bv fv) (tm_tabs t0)).
      { apply Hval.
        - apply multi_refl.
        - apply v_tabs. exact HlcT. }
      simpl in Hrel.
      pose proof (Hrel SU) as Hcu.
      assert (HstTy : step (tm_tapp (tm_tabs t0) (syn SU))
                           (open_tm_ty t0 (syn SU))).
      { apply ST_TAppTabs.
        - exact HlcT.
        - exact Hlc. }
      exact (C_step _ _ _ Hcu HstTy).
    + subst y. apply (IHu f' Hst (syn SU) SU eq_refl Hlc).
      intros v Hm Hv. apply Hval.
      * eapply multi_step; eauto.
      * exact Hv.
Qed.

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  (* Complete the proof of normalization. *)
Qed.

End SystemFNormalizationRecursionHardTask.
