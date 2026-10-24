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
(* Part 1. Erased terms and their operational semantics.         *)
(*                                                               *)
(* Type annotations are irrelevant to the reduction of the       *)
(* annotated language (they are only inspected by the locality   *)
(* side conditions).  We therefore work with an erased syntax    *)
(* for the logical relation; this makes the relation insensitive *)
(* to type annotations and lets us interpret type abstraction    *)
(* by quantification over reducibility candidates.               *)
(* ============================================================ *)

Inductive etm : Type :=
  | etm_bvar : nat -> etm
  | etm_fvar : atom -> etm
  | etm_abs : etm -> etm
  | etm_app : etm -> etm -> etm
  | etm_tabs : etm -> etm
  | etm_tapp : etm -> etm
  | etm_zero : etm
  | etm_succ : etm -> etm
  | etm_natrec : etm -> etm -> etm -> etm.

Fixpoint erase (t : tm) : etm :=
  match t with
  | tm_bvar i => etm_bvar i
  | tm_fvar x => etm_fvar x
  | tm_abs T t1 => etm_abs (erase t1)
  | tm_app t1 t2 => etm_app (erase t1) (erase t2)
  | tm_tabs t1 => etm_tabs (erase t1)
  | tm_tapp t1 T => etm_tapp (erase t1)
  | tm_zero => etm_zero
  | tm_succ t1 => etm_succ (erase t1)
  | tm_natrec n b s => etm_natrec (erase n) (erase b) (erase s)
  end.

Fixpoint open_e_rec (k : nat) (u t : etm) : etm :=
  match t with
  | etm_bvar i => if Nat.eqb k i then u else etm_bvar i
  | etm_fvar x => etm_fvar x
  | etm_abs t1 => etm_abs (open_e_rec (S k) u t1)
  | etm_app t1 t2 => etm_app (open_e_rec k u t1) (open_e_rec k u t2)
  | etm_tabs t1 => etm_tabs (open_e_rec k u t1)
  | etm_tapp t1 => etm_tapp (open_e_rec k u t1)
  | etm_zero => etm_zero
  | etm_succ t1 => etm_succ (open_e_rec k u t1)
  | etm_natrec n b s => etm_natrec (open_e_rec k u n) (open_e_rec k u b) (open_e_rec k u s)
  end.

Definition open_e (t u : etm) : etm := open_e_rec 0 u t.

Fixpoint subst_e (sb : atom -> etm) (t : etm) : etm :=
  match t with
  | etm_bvar i => etm_bvar i
  | etm_fvar x => sb x
  | etm_abs t1 => etm_abs (subst_e sb t1)
  | etm_app t1 t2 => etm_app (subst_e sb t1) (subst_e sb t2)
  | etm_tabs t1 => etm_tabs (subst_e sb t1)
  | etm_tapp t1 => etm_tapp (subst_e sb t1)
  | etm_zero => etm_zero
  | etm_succ t1 => etm_succ (subst_e sb t1)
  | etm_natrec n b s => etm_natrec (subst_e sb n) (subst_e sb b) (subst_e sb s)
  end.

Inductive evalue : etm -> Prop :=
  | ev_abs : forall b, evalue (etm_abs b)
  | ev_tabs : forall b, evalue (etm_tabs b)
  | ev_zero : evalue etm_zero
  | ev_succ : forall n, evalue n -> evalue (etm_succ n).

Inductive numeric_value_e : etm -> Prop :=
  | nve_zero : numeric_value_e etm_zero
  | nve_succ : forall n, numeric_value_e n -> numeric_value_e (etm_succ n).

Fixpoint numeral_e (n : nat) : etm :=
  match n with
  | O => etm_zero
  | S m => etm_succ (numeral_e m)
  end.

Inductive estep : etm -> etm -> Prop :=
  | EST_AppAbs : forall b v,
      evalue v ->
      estep (etm_app (etm_abs b) v) (open_e b v)
  | EST_App1 : forall t1 t1' t2,
      estep t1 t1' ->
      estep (etm_app t1 t2) (etm_app t1' t2)
  | EST_App2 : forall v1 t2 t2',
      evalue v1 ->
      estep t2 t2' ->
      estep (etm_app v1 t2) (etm_app v1 t2')
  | EST_TAppTabs : forall b,
      estep (etm_tapp (etm_tabs b)) b
  | EST_TApp : forall t t',
      estep t t' ->
      estep (etm_tapp t) (etm_tapp t')
  | EST_Succ : forall t t',
      estep t t' ->
      estep (etm_succ t) (etm_succ t')
  | EST_RecArg : forall n n' b s,
      estep n n' ->
      estep (etm_natrec n b s) (etm_natrec n' b s)
  | EST_RecBase : forall n b b' s,
      numeric_value_e n ->
      estep b b' ->
      estep (etm_natrec n b s) (etm_natrec n b' s)
  | EST_RecStep : forall n b s s',
      numeric_value_e n ->
      evalue b ->
      estep s s' ->
      estep (etm_natrec n b s) (etm_natrec n b s')
  | EST_RecZero : forall b s,
      evalue b ->
      evalue s ->
      estep (etm_natrec etm_zero b s) b
  | EST_RecSucc : forall n b s,
      numeric_value_e n ->
      evalue b ->
      evalue s ->
      estep (etm_natrec (etm_succ n) b s)
            (etm_app (etm_app s n) (etm_natrec n b s)).

Inductive sn_e : etm -> Prop :=
  | sn_e_intro : forall u,
      (forall u', estep u u' -> sn_e u') ->
      sn_e u.

Hint Constructors evalue numeric_value_e sn_e estep : core.

(* ------------------------------------------------------------------ *)
(* Basic facts about erased values and strong normalization.           *)
(* ------------------------------------------------------------------ *)

Lemma evalue_no_step : forall u, evalue u -> forall u', ~ estep u u'.
Proof.
  intros u H. induction H as [b | b | | n Hn IH]; intros u' Hstep; inversion Hstep.
  eapply IH; eauto.
Qed.

Lemma sn_e_evalue : forall u, evalue u -> sn_e u.
Proof.
  intros u H. apply sn_e_intro. intros u' Hstep.
  exfalso. eapply evalue_no_step; eauto.
Qed.

Lemma numeric_value_e_evalue : forall u, numeric_value_e u -> evalue u.
Proof.
  intros u H. induction H; eauto using evalue.
Qed.

Lemma numeric_value_e_sn : forall u, numeric_value_e u -> sn_e u.
Proof.
  intros u H. induction H as [| m Hm IHm].
  - apply sn_e_evalue. constructor.
  - apply sn_e_evalue. apply ev_succ. apply numeric_value_e_evalue. assumption.
Qed.

Lemma sn_e_numeral : forall k, sn_e (numeral_e k).
Proof.
  intro k. apply numeric_value_e_sn.
  induction k; simpl; constructor; assumption.
Qed.

Lemma sn_e_succ : forall u, sn_e u -> sn_e (etm_succ u).
Proof.
  intros u H. induction H as [u Hstep IH].
  apply sn_e_intro. intros u' H'. inversion H'; subst. apply IH. assumption.
Qed.

Lemma numeric_value_e_numeral : forall n, numeric_value_e n -> exists k, n = numeral_e k.
Proof.
  intros n H. induction H as [| m Hm IHm].
  - exists 0. reflexivity.
  - destruct IHm as [k Hk]. exists (S k). simpl. rewrite Hk. reflexivity.
Qed.

Lemma numeral_e_numeric : forall k, numeric_value_e (numeral_e k).
Proof.
  induction k; simpl; constructor; assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* Erasure commutes with the operational machinery.                    *)
(* ------------------------------------------------------------------ *)

Lemma erase_open_tm_rec : forall t k u,
  erase (open_tm_rec k u t) = open_e_rec k (erase u) (erase t).
Proof.
  induction t; intros k u0; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - reflexivity.
  - rewrite (IHt (S k) u0). reflexivity.
  - rewrite (IHt1 k u0), (IHt2 k u0). reflexivity.
  - rewrite (IHt k u0). reflexivity.
  - rewrite (IHt k u0). reflexivity.
  - reflexivity.
  - rewrite (IHt k u0). reflexivity.
  - rewrite (IHt1 k u0), (IHt2 k u0), (IHt3 k u0). reflexivity.
Qed.

Lemma erase_open_tm : forall t u,
  erase (open_tm t u) = open_e (erase t) (erase u).
Proof.
  intros t u. unfold open_tm, open_e. apply erase_open_tm_rec.
Qed.

Lemma erase_open_tm_ty_rec : forall t k U,
  erase (open_tm_ty_rec k U t) = erase t.
Proof.
  induction t; intros k U0; simpl.
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

Lemma erase_open_tm_ty : forall t U,
  erase (open_tm_ty t U) = erase t.
Proof.
  intros t U. unfold open_tm_ty. apply erase_open_tm_ty_rec.
Qed.

Lemma erase_numeric_value : forall n, numeric_value n -> numeric_value_e (erase n).
Proof.
  intros n H. induction H as [| m Hm IHm]; simpl; constructor; assumption.
Qed.

Lemma erase_value : forall v, value v -> evalue (erase v).
Proof.
  intros v H. induction H as [T t Hlc | t Hlc | n Hn].
  - simpl. constructor.
  - simpl. constructor.
  - simpl. induction Hn as [| m Hm IHm]; simpl; constructor; assumption.
Qed.

Lemma erase_step : forall t t', step t t' -> estep (erase t) (erase t').
Proof.
  intros t t' H. induction H; simpl.
  - (* ST_AppAbs *) rewrite erase_open_tm. eauto using estep, erase_value.
  - (* ST_App1 *) eauto using estep.
  - (* ST_App2 *) eauto using estep, erase_value.
  - (* ST_TAppTabs *) rewrite erase_open_tm_ty. eauto using estep.
  - (* ST_TApp *) eauto using estep.
  - (* ST_Succ *) eauto using estep.
  - (* ST_RecArg *) eauto using estep.
  - (* ST_RecBase *) eauto using estep, erase_numeric_value.
  - (* ST_RecStep *) eauto using estep, erase_numeric_value, erase_value.
  - (* ST_RecZero *) eauto using estep, erase_value.
  - (* ST_RecSucc *) eauto using estep, erase_numeric_value, erase_value.
Qed.


(* ============================================================ *)
(* Part 2. Syntactic lemmas about types (locality, freshness).   *)
(* ============================================================ *)

Definition fresh_atom (l : list atom) : atom := S (fold_right Nat.max 0 l).

Lemma fold_max_bound : forall l x, In x l -> x <= fold_right Nat.max 0 l.
Proof.
  induction l as [| a l IH]; intros x Hx.
  - contradiction.
  - simpl in Hx. destruct Hx as [-> | Hx].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; eassumption | apply Nat.le_max_r].
Qed.

Lemma fresh_atom_notin : forall l, ~ In (fresh_atom l) l.
Proof.
  intros l H. unfold fresh_atom in H.
  pose proof (fold_max_bound l _ H). lia.
Qed.

Lemma lc_ty_at_mono : forall k T, lc_ty_at k T -> forall k', k <= k' -> lc_ty_at k' T.
Proof.
  intros k T H. induction H as [k i Hi | k X | k T1 T2 H1 IH1 H2 IH2 | k T1 H1 IH1 | k];
    intros k' Hle.
  - apply lc_ty_bvar. lia.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; auto.
  - apply lc_ty_all. apply IH1. lia.
  - apply lc_ty_nat.
Qed.

Lemma lc_ty_open_pres : forall T k U,
  lc_ty_at 0 U -> lc_ty_at (S k) T -> lc_ty_at k (open_ty_rec k U T).
Proof.
  induction T as [n | X | T1 IH1 T2 IH2 | T1 IH1 | ];
    intros k U0 HU HT; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E.
      apply (lc_ty_at_mono 0 U0 HU k). lia.
    + apply lc_ty_bvar. inversion HT as [k0 i Hi | | | | ]. apply Nat.eqb_neq in E. lia.
  - apply lc_ty_fvar.
  - inversion HT as [k0 i Hi | k0 X0 | k0 A B HA HB | | ]; subst.
    apply lc_ty_arrow.
    + apply (IH1 k U0); assumption.
    + apply (IH2 k U0); assumption.
  - inversion HT as [k0 i Hi | k0 X0 | | k0 A HA | ]; subst.
    apply lc_ty_all. apply (IH1 (S k) U0); assumption.
  - apply lc_ty_nat.
Qed.

Lemma lc_ty_open_refl : forall T k U,
  lc_ty_at k (open_ty_rec k U T) -> lc_ty_at (S k) T.
Proof.
  induction T as [n | X | T1 IH1 T2 IH2 | T1 IH1 | ];
    intros k U0 H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E.
      assert (n < S k) by lia. apply lc_ty_bvar. assumption.
    + apply Nat.eqb_neq in E. inversion H. apply lc_ty_bvar. lia.
  - apply lc_ty_fvar.
  - inversion H as [k0 i Hi | k0 X0 | k0 A B HA HB | | ]; subst.
    apply lc_ty_arrow.
    + apply (IH1 k U0). assumption.
    + apply (IH2 k U0). assumption.
  - inversion H as [k0 i Hi | k0 X0 | | k0 A HA | ]; subst.
    apply lc_ty_all. apply (IH1 (S k) U0). assumption.
  - apply lc_ty_nat.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> lc_ty_at 0 T.
Proof.
  intros Delta T H. induction H as
    [Delta X Hin | Delta T1 T2 H1 IH1 H2 IH2 | L Delta T Hbody IHb | Delta].
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; assumption.
  - apply lc_ty_all.
    pose (X := fresh_atom L).
    assert (HX : ~ In X L) by apply fresh_atom_notin.
    specialize (IHb X HX).
    apply (lc_ty_open_refl T 0 (Ty_FVar X)).
    apply IHb.
  - apply lc_ty_nat.
Qed.

Lemma lc_has_type : forall Delta Gamma t T, has_type Delta Gamma t T -> lc_ty_at 0 T.
Proof.
  intros Delta Gamma t T H. induction H as
    [Delta Gamma x T Hlk Hwf
    | L Delta Gamma T1 t2 T2 Hwf Hbody IHb
    | Delta Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
    | L Delta Gamma t T Hbody IHb
    | Delta Gamma t T U H1 IH1 Hwf
    | Delta Gamma
    | Delta Gamma n Hn IHn
    | Delta Gamma n b s T Hn IHn Hb IHb Hs IHs].
  - apply (wf_ty_lc Delta). assumption.
  - apply lc_ty_arrow.
    + apply (wf_ty_lc Delta). assumption.
    + pose (x := fresh_atom L).
      assert (Hx : ~ In x L) by apply fresh_atom_notin.
      apply (IHb x Hx).
  - inversion IH1; subst. assumption.
  - apply lc_ty_all.
    pose (X := fresh_atom L).
    assert (HX : ~ In X L) by apply fresh_atom_notin.
    apply (lc_ty_open_refl T 0 (Ty_FVar X)).
    apply (IHb X HX).
  - inversion IH1; subst.
    apply (lc_ty_open_pres T 0 U).
    + apply (wf_ty_lc Delta). assumption.
    + assumption.
  - apply lc_ty_nat.
  - apply lc_ty_nat.
  - assumption.
Qed.

Fixpoint fv_ty (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow T1 T2 => fv_ty T1 ++ fv_ty T2
  | Ty_All T1 => fv_ty T1
  | Ty_Nat => []
  end.

Fixpoint fv_e (t : etm) : list atom :=
  match t with
  | etm_bvar _ => []
  | etm_fvar x => [x]
  | etm_abs t1 => fv_e t1
  | etm_app t1 t2 => fv_e t1 ++ fv_e t2
  | etm_tabs t1 => fv_e t1
  | etm_tapp t1 => fv_e t1
  | etm_zero => []
  | etm_succ t1 => fv_e t1
  | etm_natrec n b s => fv_e n ++ fv_e b ++ fv_e s
  end.



(* ============================================================ *)
(* Part 2b. Locality for erased terms, and well-typed terms are  *)
(* locally closed.  The non-shifting opening operation of the    *)
(* language is only well behaved on locally closed terms, so the *)
(* logical relation contains only locally closed terms.          *)
(* ============================================================ *)

Inductive lc_e_at : nat -> etm -> Prop :=
  | lc_e_bvar : forall k i, i < k -> lc_e_at k (etm_bvar i)
  | lc_e_fvar : forall k x, lc_e_at k (etm_fvar x)
  | lc_e_abs : forall k b, lc_e_at (S k) b -> lc_e_at k (etm_abs b)
  | lc_e_app : forall k b1 b2, lc_e_at k b1 -> lc_e_at k b2 -> lc_e_at k (etm_app b1 b2)
  | lc_e_tabs : forall k b, lc_e_at k b -> lc_e_at k (etm_tabs b)
  | lc_e_tapp : forall k b, lc_e_at k b -> lc_e_at k (etm_tapp b)
  | lc_e_zero : forall k, lc_e_at k etm_zero
  | lc_e_succ : forall k b, lc_e_at k b -> lc_e_at k (etm_succ b)
  | lc_e_natrec : forall k b1 b2 b3,
      lc_e_at k b1 -> lc_e_at k b2 -> lc_e_at k b3 -> lc_e_at k (etm_natrec b1 b2 b3).

Definition lc_e (t : etm) : Prop := lc_e_at 0 t.

Hint Constructors lc_e_at : core.

Lemma lc_e_at_mono : forall k t, lc_e_at k t -> forall k', k <= k' -> lc_e_at k' t.
Proof.
  intros k t H. induction H as
    [k i Hi | k x | k b Hb IHb | k b1 b2 H1 IH1 H2 IH2 | k b Hb IHb
    | k b Hb IHb | k | k b Hb IHb | k b1 b2 b3 H1 IH1 H2 IH2 H3 IH3];
    intros k' Hle.
  - apply lc_e_bvar. lia.
  - apply lc_e_fvar.
  - apply lc_e_abs. apply IHb. lia.
  - apply lc_e_app; auto.
  - apply lc_e_tabs; auto.
  - apply lc_e_tapp; auto.
  - apply lc_e_zero.
  - apply lc_e_succ; auto.
  - apply lc_e_natrec; auto.
Qed.

Lemma lc_e_mono : forall t, lc_e t -> forall k, lc_e_at k t.
Proof. intros t H k. apply (lc_e_at_mono 0 t H k). lia. Qed.

Lemma lc_e_inv_abs : forall k b, lc_e_at k (etm_abs b) -> lc_e_at (S k) b.
Proof. intros k b H. inversion H as [| | k0 b0 H0 | | | | | | ]; subst. assumption. Qed.

Lemma lc_e_inv_app : forall k b1 b2, lc_e_at k (etm_app b1 b2) -> lc_e_at k b1 /\ lc_e_at k b2.
Proof.
  intros k b1 b2 H. inversion H as [| | | k0 c1 c2 H1 H2 | | | | | ]; subst.
  split; assumption.
Qed.

Lemma lc_e_inv_tabs : forall k b, lc_e_at k (etm_tabs b) -> lc_e_at k b.
Proof. intros k b H. inversion H as [| | | | k0 b0 H0 | | | | ]; subst. assumption. Qed.

Lemma lc_e_inv_tapp : forall k b, lc_e_at k (etm_tapp b) -> lc_e_at k b.
Proof. intros k b H. inversion H as [| | | | | k0 b0 H0 | | | ]; subst. assumption. Qed.

Lemma lc_e_inv_succ : forall k b, lc_e_at k (etm_succ b) -> lc_e_at k b.
Proof. intros k b H. inversion H as [| | | | | | | k0 b0 H0 | ]; subst. assumption. Qed.

Lemma lc_e_inv_natrec : forall k b1 b2 b3,
  lc_e_at k (etm_natrec b1 b2 b3) -> lc_e_at k b1 /\ lc_e_at k b2 /\ lc_e_at k b3.
Proof.
  intros k b1 b2 b3 H. inversion H as [| | | | | | | | k0 c1 c2 c3 H1 H2 H3]; subst.
  split; [assumption | split; assumption].
Qed.

Lemma lc_e_at_open : forall b k u,
  lc_e_at (S k) b -> lc_e u -> lc_e_at k (open_e_rec k u b).
Proof.
  induction b as [i | x | b1 IH1 | b1 IH1 b2 IH2 | b1 IH1 | b1 IH1 | | b1 IH1
                 | b1 IH1 b2 IH2 b3 IH3];
    intros k u0 Hb Hu; simpl.
  - destruct (Nat.eqb k i) eqn:E.
    + apply (lc_e_at_mono 0 u0 Hu k). lia.
    + apply lc_e_bvar. inversion Hb. apply Nat.eqb_neq in E. lia.
  - apply lc_e_fvar.
  - apply lc_e_abs. apply (IH1 (S k) u0); [inversion Hb; assumption | assumption].
  - apply lc_e_app.
    + apply (IH1 k u0); [inversion Hb; assumption | assumption].
    + apply (IH2 k u0); [inversion Hb; assumption | assumption].
  - apply lc_e_tabs. apply (IH1 k u0); [inversion Hb; assumption | assumption].
  - apply lc_e_tapp. apply (IH1 k u0); [inversion Hb; assumption | assumption].
  - apply lc_e_zero.
  - apply lc_e_succ. apply (IH1 k u0); [inversion Hb; assumption | assumption].
  - apply lc_e_natrec.
    + apply (IH1 k u0); [inversion Hb; assumption | assumption].
    + apply (IH2 k u0); [inversion Hb; assumption | assumption].
    + apply (IH3 k u0); [inversion Hb; assumption | assumption].
Qed.

Lemma lc_e_at_subst : forall b k sb,
  lc_e_at k b -> (forall x, lc_e (sb x)) -> lc_e_at k (subst_e sb b).
Proof.
  induction b as [i | x | b1 IH1 | b1 IH1 b2 IH2 | b1 IH1 | b1 IH1 | | b1 IH1
                 | b1 IH1 b2 IH2 b3 IH3];
    intros k sb Hlc Hsb; simpl.
  - apply lc_e_bvar. inversion Hlc; assumption.
  - apply (lc_e_at_mono 0 (sb x) (Hsb x) k). lia.
  - apply lc_e_abs. apply (IH1 (S k) sb); [inversion Hlc; assumption | assumption].
  - apply lc_e_app.
    + apply (IH1 k sb); [inversion Hlc; assumption | assumption].
    + apply (IH2 k sb); [inversion Hlc; assumption | assumption].
  - apply lc_e_tabs. apply (IH1 k sb); [inversion Hlc; assumption | assumption].
  - apply lc_e_tapp. apply (IH1 k sb); [inversion Hlc; assumption | assumption].
  - apply lc_e_zero.
  - apply lc_e_succ. apply (IH1 k sb); [inversion Hlc; assumption | assumption].
  - apply lc_e_natrec.
    + apply (IH1 k sb); [inversion Hlc; assumption | assumption].
    + apply (IH2 k sb); [inversion Hlc; assumption | assumption].
    + apply (IH3 k sb); [inversion Hlc; assumption | assumption].
Qed.

Lemma lc_e_open_id_at : forall t j, lc_e_at j t -> forall u, open_e_rec j u t = t.
Proof.
  induction t as [i | x | b1 IH1 | b1 IH1 b2 IH2 | b1 IH1 | b1 IH1 | | b1 IH1
                 | b1 IH1 b2 IH2 b3 IH3];
    intros j Hlt u0; simpl.
  - destruct (Nat.eqb j i) eqn:E.
    + apply Nat.eqb_eq in E. subst. inversion Hlt. lia.
    + reflexivity.
  - reflexivity.
  - apply f_equal. apply (IH1 (S j)). inversion Hlt; assumption.
  - apply f_equal2.
    + apply (IH1 j). inversion Hlt; assumption.
    + apply (IH2 j). inversion Hlt; assumption.
  - apply f_equal. apply (IH1 j). inversion Hlt; assumption.
  - apply f_equal. apply (IH1 j). inversion Hlt; assumption.
  - reflexivity.
  - apply f_equal. apply (IH1 j). inversion Hlt; assumption.
  - apply f_equal3.
    + apply (IH1 j). inversion Hlt; assumption.
    + apply (IH2 j). inversion Hlt; assumption.
    + apply (IH3 j). inversion Hlt; assumption.
Qed.

Lemma lc_e_open_id : forall t, lc_e t -> forall k u, open_e_rec k u t = t.
Proof.
  intros t Hlc k u. apply lc_e_open_id_at. apply (lc_e_at_mono 0 t Hlc k). lia.
Qed.

Lemma lc_e_at_step : forall u, lc_e u -> forall u', estep u u' -> lc_e u'.
Proof.
  intros u Hlc u' Hst. revert Hlc.
  induction Hst; intros Hlc.
  - (* AppAbs *) simpl in Hlc.
    apply lc_e_inv_app in Hlc. destruct Hlc as [HA HB].
    apply lc_e_inv_abs in HA.
    apply lc_e_at_open; assumption.
  - (* App1 *) simpl in Hlc.
    apply lc_e_inv_app in Hlc. destruct Hlc as [HA HB].
    apply lc_e_app; [apply IHHst; assumption | assumption].
  - (* App2 *) simpl in Hlc.
    apply lc_e_inv_app in Hlc. destruct Hlc as [HA HB].
    apply lc_e_app; [assumption | apply IHHst; assumption].
  - (* TAppTabs *) simpl in Hlc.
    apply lc_e_inv_tapp in Hlc. apply lc_e_inv_tabs in Hlc. assumption.
  - (* TApp *) simpl in Hlc.
    apply lc_e_inv_tapp in Hlc. apply lc_e_tapp. apply IHHst; assumption.
  - (* Succ *) simpl in Hlc.
    apply lc_e_inv_succ in Hlc. apply lc_e_succ. apply IHHst; assumption.
  - (* RecArg *) simpl in Hlc.
    apply lc_e_inv_natrec in Hlc. destruct Hlc as [HA [HB HC]].
    apply lc_e_natrec; [apply IHHst; assumption | assumption | assumption].
  - (* RecBase *) simpl in Hlc.
    apply lc_e_inv_natrec in Hlc. destruct Hlc as [HA [HB HC]].
    apply lc_e_natrec; [assumption | apply IHHst; assumption | assumption].
  - (* RecStep *) simpl in Hlc.
    apply lc_e_inv_natrec in Hlc. destruct Hlc as [HA [HB HC]].
    apply lc_e_natrec; [assumption | assumption | apply IHHst; assumption].
  - (* RecZero *) simpl in Hlc.
    apply lc_e_inv_natrec in Hlc. destruct Hlc as [HA [HB HC]]. assumption.
  - (* RecSucc *) simpl in Hlc.
    apply lc_e_inv_natrec in Hlc. destruct Hlc as [HA [HB HC]].
    apply lc_e_inv_succ in HA.
    apply lc_e_app.
    + apply lc_e_app; assumption.
    + apply lc_e_natrec; assumption.
Qed.

Lemma lc_e_step : forall u u', lc_e u -> estep u u' -> lc_e u'.
Proof. intros u u' H Hst. eapply lc_e_at_step; eauto. Qed.

(* Erasure of a locally closed annotated term is locally closed. *)
Lemma erase_lc : forall K k t, lc_tm_at K k t -> lc_e_at k (erase t).
Proof.
  intros K k t H. induction H as
    [K k i Hi | K k x | K k T t Hty Htm IHtm | K k t1 t2 H1 IH1 H2 IH2
    | K k t Ht IHt | K k t T Ht IHt Hty | K k | K k t Ht IHt
    | K k n b s Hn IHn Hb IHb Hs IHs].
  - simpl. apply lc_e_bvar. assumption.
  - simpl. apply lc_e_fvar.
  - simpl. apply lc_e_abs. assumption.
  - simpl. apply lc_e_app; assumption.
  - simpl. apply lc_e_tabs. assumption.
  - simpl. apply lc_e_tapp. assumption.
  - simpl. apply lc_e_zero.
  - simpl. apply lc_e_succ. assumption.
  - simpl. apply lc_e_natrec; assumption.
Qed.

(* Monotonicity of locality of annotated terms in both indices. *)
Lemma lc_tm_at_mono : forall K k t, lc_tm_at K k t ->
  forall K' k', K <= K' -> k <= k' -> lc_tm_at K' k' t.
Proof.
  intros K k t H. induction H as
    [K k i Hi | K k x | K k T t Hty Htm IHtm | K k t1 t2 H1 IH1 H2 IH2
    | K k t Ht IHt | K k t T Ht IHt Hty | K k | K k t Ht IHt
    | K k n b s Hn IHn Hb IHb Hs IHs];
    intros K' k' HK Hk.
  - apply lc_tm_bvar. lia.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + eapply lc_ty_at_mono; eassumption.
    + apply IHtm; lia.
  - apply lc_tm_app; auto.
  - apply lc_tm_tabs. apply IHt; lia.
  - apply lc_tm_tapp; [apply IHt; lia | eapply lc_ty_at_mono; eassumption].
  - apply lc_tm_zero.
  - apply lc_tm_succ; auto.
  - apply lc_tm_rec; auto.
Qed.

(* Reflection of term-variable opening for locality. *)
Lemma lc_tm_open_refl : forall t K k x,
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) -> lc_tm_at K (S k) t.
Proof.
  induction t as [i | y | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T | | t1 IH1
                 | t1 IH1 t2 IH2 t3 IH3];
    intros K k x0 H; simpl in H.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst. apply lc_tm_bvar. lia.
    + apply Nat.eqb_neq in E. inversion H; subst. apply lc_tm_bvar. lia.
  - inversion H; subst. apply lc_tm_fvar.
  - inversion H; subst. apply lc_tm_abs; [assumption | ].
    apply (IH1 K (S k) x0). assumption.
  - inversion H; subst. apply lc_tm_app.
    + apply (IH1 K k x0). assumption.
    + apply (IH2 K k x0). assumption.
  - inversion H; subst. apply lc_tm_tabs. apply (IH1 (S K) k x0). assumption.
  - inversion H; subst. apply lc_tm_tapp.
    + apply (IH1 K k x0). assumption.
    + assumption.
  - inversion H; subst. apply lc_tm_zero.
  - inversion H; subst. apply lc_tm_succ. apply (IH1 K k x0). assumption.
  - inversion H; subst. apply lc_tm_rec.
    + apply (IH1 K k x0). assumption.
    + apply (IH2 K k x0). assumption.
    + apply (IH3 K k x0). assumption.
Qed.

(* Reflection of type-variable opening for locality. *)
Lemma lc_tm_ty_open_refl : forall t K k X,
  lc_tm_at K k (open_tm_ty_rec K (Ty_FVar X) t) -> lc_tm_at (S K) k t.
Proof.
  induction t as [i | y | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T | | t1 IH1
                 | t1 IH1 t2 IH2 t3 IH3];
    intros K k X0 H; simpl in H.
  - inversion H; subst. apply lc_tm_bvar. assumption.
  - inversion H; subst. apply lc_tm_fvar.
  - inversion H; subst. apply lc_tm_abs.
    + apply (lc_ty_open_refl T K (Ty_FVar X0)). assumption.
    + apply (IH1 K (S k) X0). assumption.
  - inversion H; subst. apply lc_tm_app.
    + apply (IH1 K k X0). assumption.
    + apply (IH2 K k X0). assumption.
  - inversion H; subst. apply lc_tm_tabs. apply (IH1 (S K) k X0). assumption.
  - inversion H; subst. apply lc_tm_tapp.
    + apply (IH1 K k X0). assumption.
    + apply (lc_ty_open_refl T K (Ty_FVar X0)). assumption.
  - inversion H; subst. apply lc_tm_zero.
  - inversion H; subst. apply lc_tm_succ. apply (IH1 K k X0). assumption.
  - inversion H; subst. apply lc_tm_rec.
    + apply (IH1 K k X0). assumption.
    + apply (IH2 K k X0). assumption.
    + apply (IH3 K k X0). assumption.
Qed.

(* Every well-typed term is locally closed. *)
Lemma lc_has_type_tm : forall Delta Gamma t T, has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T H. induction H as
    [Delta Gamma x T Hlk Hwf
    | L Delta Gamma T1 t2 T2 Hwf Hbody IHb
    | Delta Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
    | L Delta Gamma t T Hbody IHb
    | Delta Gamma t T U H1 IH1 Hwf
    | Delta Gamma
    | Delta Gamma n Hn IHn
    | Delta Gamma n b s T Hn IHn Hb IHb Hs IHs].
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + apply (wf_ty_lc Delta). assumption.
    + pose (x := fresh_atom L).
      assert (Hx : ~ In x L) by apply fresh_atom_notin.
      apply (lc_tm_open_refl t2 0 0 x).
      apply (IHb x Hx).
  - apply lc_tm_app; assumption.
  - apply lc_tm_tabs.
    pose (X := fresh_atom L).
    assert (HX : ~ In X L) by apply fresh_atom_notin.
    apply (lc_tm_ty_open_refl t 0 0 X).
    apply (IHb X HX).
  - apply lc_tm_tapp.
    + assumption.
    + apply (wf_ty_lc Delta). assumption.
  - apply lc_tm_zero.
  - apply lc_tm_succ. assumption.
  - apply lc_tm_rec; assumption.
Qed.

(* ============================================================ *)
(* Part 3. Reducibility candidates and the logical relation.     *)
(* ============================================================ *)

Lemma sn_e_step : forall u u', sn_e u -> estep u u' -> sn_e u'.
Proof.
  intros u u' H Hst. destruct H as [u0 Hprem]. apply (Hprem u'). assumption.
Qed.

Lemma not_evalue_app : forall u v, ~ evalue (etm_app u v).
Proof. intros u v H. inversion H. Qed.

Lemma not_evalue_tapp : forall u, ~ evalue (etm_tapp u).
Proof. intros u H. inversion H. Qed.

Lemma not_evalue_natrec : forall n b s, ~ evalue (etm_natrec n b s).
Proof. intros n b s H. inversion H. Qed.

Lemma lc_e_numeral : forall k, lc_e (numeral_e k).
Proof.
  induction k; simpl.
  - apply lc_e_zero.
  - apply lc_e_succ. assumption.
Qed.

(* Inversion principles for the erased reduction relation. *)
Lemma estep_app_inv : forall u v w, estep (etm_app u v) w ->
  (exists b, u = etm_abs b /\ evalue v /\ w = open_e b v)
  \/ (exists u', estep u u' /\ w = etm_app u' v)
  \/ (exists v', evalue u /\ estep v v' /\ w = etm_app u v').
Proof.
  intros u v w H. inversion H as [b v0 Hev | t1 t1' t2 Hst | v1 t2 t2' Hev Hst | | | | | | | | ];
    subst; eauto 8.
Qed.

Lemma estep_tapp_inv : forall u w, estep (etm_tapp u) w ->
  (exists b, u = etm_tabs b /\ w = b) \/ (exists u', estep u u' /\ w = etm_tapp u').
Proof.
  intros u w H. inversion H as [| | | b | t t' Hst | | | | | | ]; subst; eauto.
Qed.

Lemma estep_succ_inv : forall u w, estep (etm_succ u) w ->
  exists u', estep u u' /\ w = etm_succ u'.
Proof.
  intros u w H. inversion H as [| | | | | t t' Hst | | | | | ]; subst; eauto.
Qed.

Lemma estep_natrec_inv : forall n b s w, estep (etm_natrec n b s) w ->
     (exists n', estep n n' /\ w = etm_natrec n' b s)
  \/ (exists b', numeric_value_e n /\ estep b b' /\ w = etm_natrec n b' s)
  \/ (exists s', numeric_value_e n /\ evalue b /\ estep s s' /\ w = etm_natrec n b s')
  \/ (n = etm_zero /\ evalue b /\ evalue s /\ w = b)
  \/ (exists n0, n = etm_succ n0 /\ numeric_value_e n0 /\ evalue b /\ evalue s /\
                 w = etm_app (etm_app s n0) (etm_natrec n0 b s)).
Proof.
  intros n b s w H.
  inversion H as [| | | | | | n0 n0' b0 s0 Hst | n0 b0 b0' s0 Hnum Hst
                 | n0 b0 s0 s0' Hnum Hev Hst | b0 s0 Hevb Hevs | n0 b0 s0 Hnum Hevb Hevs ];
    subst; eauto 8.
  right; right; right; right. exists n0. repeat split; auto.
Qed.

(* A reducibility candidate: a set of locally closed strongly normalizing
   terms, closed under reduction and under head expansion. *)
Definition cand (P : etm -> Prop) : Prop :=
  (forall u, P u -> lc_e u) /\
  (forall u, P u -> sn_e u) /\
  (forall u u', P u -> estep u u' -> P u') /\
  (forall u, lc_e u -> ~ evalue u -> (forall u', estep u u' -> P u') -> P u).

Lemma cand_lc : forall P, cand P -> forall u, P u -> lc_e u.
Proof. intros P [H1 [H2 [H3 H4]]] u Hu. apply H1. assumption. Qed.

Lemma cand_sn : forall P, cand P -> forall u, P u -> sn_e u.
Proof. intros P [H1 [H2 [H3 H4]]] u Hu. apply H2. assumption. Qed.

Lemma cand_step : forall P, cand P -> forall u u', P u -> estep u u' -> P u'.
Proof. intros P [H1 [H2 [H3 H4]]] u u' Hu Hst. eapply H3; eauto. Qed.

Lemma cand_expand : forall P, cand P -> forall u, lc_e u -> ~ evalue u ->
  (forall u', estep u u' -> P u') -> P u.
Proof. intros P [H1 [H2 [H3 H4]]] u Hlc Hne Hall. eapply H4; eauto. Qed.

Lemma cand_lc_sn : cand (fun u => lc_e u /\ sn_e u).
Proof.
  split.
  - intros u [Hlc Hsn]. assumption.
  - split.
    + intros u [Hlc Hsn]. assumption.
    + split.
      * intros u u' [Hlc Hsn] Hst. split.
        -- eapply lc_e_step; eauto.
        -- eapply sn_e_step; eauto.
      * intros u Hlc Hne Hall. split; [assumption |].
        apply sn_e_intro. intros u' Hst. apply (proj2 (Hall u' Hst)).
Qed.

(* Valuation of bound type variables, extended under a universal type. *)
Definition consB (C : etm -> Prop) (rho : nat -> etm -> Prop) : nat -> etm -> Prop :=
  fun i => match i with
           | O => C
           | S j => rho j
           end.

(* Point update of the valuation of bound type variables. *)
Definition updB (rho : nat -> etm -> Prop) (k : nat) (C : etm -> Prop) : nat -> etm -> Prop :=
  fun i => if Nat.eqb i k then C else rho i.

(* Update of the valuation of free type variables. *)
Definition updA (rho : atom -> etm -> Prop) (X : atom) (C : etm -> Prop) : atom -> etm -> Prop :=
  fun Y => if Nat.eqb Y X then C else rho Y.

(* The unary, type-indexed logical relation on erased terms. *)
Fixpoint lr (rhoA : atom -> etm -> Prop) (rhoB : nat -> etm -> Prop) (T : ty) : etm -> Prop :=
  match T with
  | Ty_BVar i => fun u => lc_e u /\ rhoB i u
  | Ty_FVar X => fun u => lc_e u /\ rhoA X u
  | Ty_Arrow T1 T2 =>
      fun u => lc_e u /\ sn_e u /\
               (forall v, lr rhoA rhoB T1 v -> lr rhoA rhoB T2 (etm_app u v))
  | Ty_All T1 =>
      fun u => lc_e u /\ sn_e u /\
               (forall C, cand C -> lr rhoA (consB C rhoB) T1 (etm_tapp u))
  | Ty_Nat => fun u => lc_e u /\ sn_e u
  end.

Definition cand_val (rhoA : atom -> etm -> Prop) (rhoB : nat -> etm -> Prop) : Prop :=
  (forall X, cand (rhoA X)) /\ (forall i, cand (rhoB i)).

Lemma cand_val_consB : forall rhoA rhoB C,
  cand_val rhoA rhoB -> cand C -> cand_val rhoA (consB C rhoB).
Proof.
  intros rhoA rhoB C [HA HB] HC. split; [assumption |].
  intros i. destruct i as [| j].
  - simpl. assumption.
  - simpl. apply HB.
Qed.

Lemma cand_val_updA : forall rhoA rhoB X C,
  cand_val rhoA rhoB -> cand C -> cand_val (updA rhoA X C) rhoB.
Proof.
  intros rhoA rhoB X C [HA HB] HC. split; [| assumption].
  intros Y. unfold updA. destruct (Nat.eqb Y X); [assumption | apply HA].
Qed.

Lemma cand_val_updB : forall rhoA rhoB k C,
  cand_val rhoA rhoB -> cand C -> cand_val rhoA (updB rhoB k C).
Proof.
  intros rhoA rhoB k C [HA HB] HC. split; [assumption |].
  intros i. unfold updB. destruct (Nat.eqb i k); [assumption | apply HB].
Qed.

Lemma cand_lr : forall T rhoA rhoB, cand_val rhoA rhoB -> cand (lr rhoA rhoB T).
Proof.
  induction T as [n | X | T1 IH1 T2 IH2 | T1 IH1 | ];
    intros rhoA rhoB Hcv; simpl.
  - (* BVar *)
    destruct (proj2 Hcv n) as [HlcP [HsnP [HstP HexpP]]].
    split.
    + intros u [HA HB]. assumption.
    + split.
      * intros u [HA HB]. apply HsnP. assumption.
      * split.
        -- intros u u' [HA HB] Hstep. split; [eapply lc_e_step; eauto |].
           apply (HstP u u'); assumption.
        -- intros u HA Hne Hall. split; [assumption |].
           apply (HexpP u HA Hne). intros u' Hst. apply (proj2 (Hall u' Hst)).
  - (* FVar *)
    destruct (proj1 Hcv X) as [HlcP [HsnP [HstP HexpP]]].
    split.
    + intros u [HA HB]. assumption.
    + split.
      * intros u [HA HB]. apply HsnP. assumption.
      * split.
        -- intros u u' [HA HB] Hstep. split; [eapply lc_e_step; eauto |].
           apply (HstP u u'); assumption.
        -- intros u HA Hne Hall. split; [assumption |].
           apply (HexpP u HA Hne). intros u' Hst. apply (proj2 (Hall u' Hst)).
  - (* Arrow *)
    destruct (IH1 rhoA rhoB Hcv) as [Hlc1 [Hsn1 [Hst1 Hexp1]]].
    destruct (IH2 rhoA rhoB Hcv) as [Hlc2 [Hsn2 [Hst2 Hexp2]]].
    split.
    + intros u [HA [HB HC]]. assumption.
    + split.
      * intros u [HA [HB HC]]. assumption.
      * split.
        -- intros u u' [HA [HB HC]] Hstep. split; [eapply lc_e_step; eauto |].
           split; [eapply sn_e_step; eauto |].
           intros v Hv. apply (Hst2 (etm_app u v) (etm_app u' v)).
           ++ apply HC. assumption.
           ++ apply EST_App1. assumption.
        -- intros u HAlc Hne Hall. split; [assumption |]. split.
           ++ apply sn_e_intro. intros u' Hst. exact (proj1 (proj2 (Hall u' Hst))).
           ++ intros v Hv.
              apply (Hexp2 (etm_app u v)).
              ** apply lc_e_app; [assumption | apply Hlc1; assumption].
              ** apply not_evalue_app.
              ** intros w Hw.
                 destruct (estep_app_inv u v w Hw) as
                   [[b [Hu [Hev Hw']]] | [[u' [Hst Hw']] | [v' [Hevu [Hst Hw']]]]].
                 --- subst. exfalso. apply Hne. apply ev_abs.
                 --- subst. exact (proj2 (proj2 (Hall u' Hst)) v Hv).
                 --- subst. exfalso. apply Hne. assumption.
  - (* All *)
    split.
    + intros u [HA [HB HC]]. assumption.
    + split.
      * intros u [HA [HB HC]]. assumption.
      * split.
        -- intros u u' [HA [HB HC]] Hstep. split; [eapply lc_e_step; eauto |].
           split; [eapply sn_e_step; eauto |].
           intros C HCc.
           destruct (IH1 rhoA (consB C rhoB) (cand_val_consB rhoA rhoB C Hcv HCc))
             as [Hlc1 [Hsn1 [Hst1 Hexp1]]].
           apply (Hst1 (etm_tapp u) (etm_tapp u')).
           ++ apply HC. assumption.
           ++ apply EST_TApp. assumption.
        -- intros u HAlc Hne Hall. split; [assumption |]. split.
           ++ apply sn_e_intro. intros u' Hst. exact (proj1 (proj2 (Hall u' Hst))).
           ++ intros C HCc.
              destruct (IH1 rhoA (consB C rhoB) (cand_val_consB rhoA rhoB C Hcv HCc))
                as [Hlc1 [Hsn1 [Hst1 Hexp1]]].
              apply (Hexp1 (etm_tapp u)).
              ** apply lc_e_tapp. assumption.
              ** apply not_evalue_tapp.
              ** intros w Hw.
                 destruct (estep_tapp_inv u w Hw) as [[b [Hu Hw']] | [u' [Hst Hw']]].
                 --- subst. exfalso. apply Hne. apply ev_tabs.
                 --- subst. exact (proj2 (proj2 (Hall u' Hst)) C HCc).
  - (* Nat *)
    apply cand_lc_sn.
Qed.

(* ============================================================ *)
(* Part 4. The relation depends only on the relevant valuations, *)
(* and commutes with opening of bound type variables.            *)
(* ============================================================ *)

Lemma lr_lc : forall T rhoA rhoB u, lr rhoA rhoB T u -> lc_e u.
Proof.
  induction T as [n | X | T1 IH1 T2 IH2 | T1 IH1 | ]; intros rhoA rhoB u H; simpl in H.
  - destruct H as [HA HB]. assumption.
  - destruct H as [HA HB]. assumption.
  - destruct H as [HA [HB HC]]. assumption.
  - destruct H as [HA [HB HC]]. assumption.
  - destruct H as [HA HB]. assumption.
Qed.

Lemma consB_equiv : forall C rho rho',
  (forall i u, rho i u <-> rho' i u) ->
  forall i u, consB C rho i u <-> consB C rho' i u.
Proof.
  intros C rho rho' H i u. destruct i as [| j]; simpl; [reflexivity | apply H].
Qed.

Lemma consB_agree : forall C rho rho' m,
  (forall i, i < m -> forall u, rho i u <-> rho' i u) ->
  forall i, i < S m -> forall u, consB C rho i u <-> consB C rho' i u.
Proof.
  intros C rho rho' m H i Hi u. destruct i as [| j].
  - simpl. reflexivity.
  - simpl. apply H. lia.
Qed.

Lemma lr_mapB_equiv : forall T rhoA rho rho',
  (forall i u, rho i u <-> rho' i u) ->
  forall u, lr rhoA rho T u <-> lr rhoA rho' T u.
Proof.
  induction T as [n | X | T1 IH1 T2 IH2 | T1 IH1 | ];
    intros rhoA rho rho' Hagree u; simpl.
  - split.
    + intros [HA HB]. split; [assumption |]. apply (Hagree n u). assumption.
    + intros [HA HB]. split; [assumption |]. apply (Hagree n u). assumption.
  - reflexivity.
  - split.
    + intros [HA [HB HC]]. split; [assumption | split].
      * assumption.
      * intros v Hv. apply (proj1 (IH2 rhoA rho rho' Hagree (etm_app u v))).
        apply HC. apply (proj2 (IH1 rhoA rho rho' Hagree v)). assumption.
    + intros [HA [HB HC]]. split; [assumption | split].
      * assumption.
      * intros v Hv. apply (proj2 (IH2 rhoA rho rho' Hagree (etm_app u v))).
        apply HC. apply (proj1 (IH1 rhoA rho rho' Hagree v)). assumption.
  - split.
    + intros [HA [HB HC]]. split; [assumption | split].
      * assumption.
      * intros C HCc.
        apply (proj1 (IH1 rhoA (consB C rho) (consB C rho') (consB_equiv C rho rho' Hagree) (etm_tapp u))).
        apply HC. assumption.
    + intros [HA [HB HC]]. split; [assumption | split].
      * assumption.
      * intros C HCc.
        apply (proj2 (IH1 rhoA (consB C rho) (consB C rho') (consB_equiv C rho rho' Hagree) (etm_tapp u))).
        apply HC. assumption.
  - reflexivity.
Qed.

Lemma lr_mapB_agree : forall T m, lc_ty_at m T ->
  forall rhoA rho rho',
    (forall i, i < m -> forall u, rho i u <-> rho' i u) ->
  forall u, lr rhoA rho T u <-> lr rhoA rho' T u.
Proof.
  induction T as [n | X | T1 IH1 T2 IH2 | T1 IH1 | ];
    intros m Hlc rhoA rho rho' Hagree u; simpl.
  - inversion Hlc as [k i Hi | k X0 | | | ]; subst.
    split.
    + intros [HA HB]. split; [assumption |]. apply (Hagree n Hi). assumption.
    + intros [HA HB]. split; [assumption |]. apply (Hagree n Hi). assumption.
  - reflexivity.
  - inversion Hlc as [k i Hi | k X0 | k A B HA HB | k A HA | ]; subst.
    split.
    + intros [H1 [H2 H3]]. split; [assumption | split].
      * assumption.
      * intros v Hv. apply (proj1 (IH2 m HB rhoA rho rho' Hagree (etm_app u v))).
        apply H3. apply (proj2 (IH1 m HA rhoA rho rho' Hagree v)). assumption.
    + intros [H1 [H2 H3]]. split; [assumption | split].
      * assumption.
      * intros v Hv. apply (proj2 (IH2 m HB rhoA rho rho' Hagree (etm_app u v))).
        apply H3. apply (proj1 (IH1 m HA rhoA rho rho' Hagree v)). assumption.
  - inversion Hlc as [k i Hi | k X0 | k A B HA HB | k A HA | ]; subst.
    split.
    + intros [H1 [H2 H3]]. split; [assumption | split].
      * assumption.
      * intros C HCc.
        apply (proj1 (IH1 (S m) HA rhoA (consB C rho) (consB C rho') (consB_agree C rho rho' m Hagree) (etm_tapp u))).
        apply H3. assumption.
    + intros [H1 [H2 H3]]. split; [assumption | split].
      * assumption.
      * intros C HCc.
        apply (proj2 (IH1 (S m) HA rhoA (consB C rho) (consB C rho') (consB_agree C rho rho' m Hagree) (etm_tapp u))).
        apply H3. assumption.
  - reflexivity.
Qed.

Lemma lr_mapB_closed : forall T, lc_ty_at 0 T ->
  forall rhoA rho rho' u, lr rhoA rho T u <-> lr rhoA rho' T u.
Proof.
  intros T Hlc rhoA rho rho' u.
  apply (lr_mapB_agree T 0 Hlc rhoA rho rho'). intros i Hi. lia.
Qed.

Lemma lr_consB_irrel : forall T, lc_ty_at 0 T ->
  forall rhoA rhoB C u, lr rhoA (consB C rhoB) T u <-> lr rhoA rhoB T u.
Proof.
  intros T Hlc rhoA rhoB C u.
  apply (lr_mapB_closed T Hlc rhoA (consB C rhoB) rhoB u).
Qed.

Lemma in_app_l : forall (X : atom) l m, In X l -> In X (l ++ m).
Proof. intros X l m H. apply in_or_app. auto. Qed.

Lemma in_app_r : forall (X : atom) l m, In X m -> In X (l ++ m).
Proof. intros X l m H. apply in_or_app. auto. Qed.

Lemma lr_mapA_agree : forall T rhoA rhoA' rhoB,
  (forall X, In X (fv_ty T) -> forall u, rhoA X u <-> rhoA' X u) ->
  forall u, lr rhoA rhoB T u <-> lr rhoA' rhoB T u.
Proof.
  induction T as [n | X | T1 IH1 T2 IH2 | T1 IH1 | ];
    intros rhoA rhoA' rhoB Hagree u; simpl.
  - reflexivity.
  - split.
    + intros [HA HB]. split; [assumption |]. apply (Hagree X). simpl. auto. assumption.
    + intros [HA HB]. split; [assumption |]. apply (Hagree X). simpl. auto. assumption.
  - split.
    + intros [H1 [H2 H3]]. split; [assumption | split].
      * assumption.
      * intros v Hv.
        apply (proj1 (IH2 rhoA rhoA' rhoB (fun Y HY => Hagree Y (in_app_r Y (fv_ty T1) (fv_ty T2) HY)) (etm_app u v))).
        apply H3. apply (proj2 (IH1 rhoA rhoA' rhoB (fun Y HY => Hagree Y (in_app_l Y (fv_ty T1) (fv_ty T2) HY)) v)). assumption.
    + intros [H1 [H2 H3]]. split; [assumption | split].
      * assumption.
      * intros v Hv.
        apply (proj2 (IH2 rhoA rhoA' rhoB (fun Y HY => Hagree Y (in_app_r Y (fv_ty T1) (fv_ty T2) HY)) (etm_app u v))).
        apply H3. apply (proj1 (IH1 rhoA rhoA' rhoB (fun Y HY => Hagree Y (in_app_l Y (fv_ty T1) (fv_ty T2) HY)) v)). assumption.
  - split.
    + intros [H1 [H2 H3]]. split; [assumption | split].
      * assumption.
      * intros C HCc. apply (proj1 (IH1 rhoA rhoA' (consB C rhoB) Hagree (etm_tapp u))). apply H3. assumption.
    + intros [H1 [H2 H3]]. split; [assumption | split].
      * assumption.
      * intros C HCc. apply (proj2 (IH1 rhoA rhoA' (consB C rhoB) Hagree (etm_tapp u))). apply H3. assumption.
  - reflexivity.
Qed.

Lemma lr_updA_irrel : forall T X C rhoA rhoB,
  ~ In X (fv_ty T) ->
  forall u, lr (updA rhoA X C) rhoB T u <-> lr rhoA rhoB T u.
Proof.
  intros T X C rhoA rhoB Hfresh u. apply lr_mapA_agree.
  intros Y HY. unfold updA. destruct (Nat.eqb Y X) eqn:E.
  - apply Nat.eqb_eq in E. subst. exfalso. apply Hfresh. assumption.
  - reflexivity.
Qed.

Lemma updB_cons : forall C C1 C2 rho k,
  (forall u, C1 u <-> C2 u) ->
  forall i u, updB (consB C rho) (S k) C1 i u <-> consB C (updB rho k C2) i u.
Proof.
  intros C C1 C2 rho k HC i u.
  destruct i as [| j].
  - simpl. unfold updB. simpl.
    destruct (Nat.eqb 0 (S k)) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + reflexivity.
  - simpl. unfold updB. simpl.
    destruct (Nat.eqb j k) eqn:E.
    + apply Nat.eqb_eq in E. subst. apply HC.
    + reflexivity.
Qed.

(* Correspondence between opening a bound type variable with a type and
   interpreting that bound variable by the candidate of the type. *)
Lemma lr_open_ty_gen : forall T k U,
  lc_ty_at 0 U ->
  forall rhoA rhoB u,
    lr rhoA rhoB (open_ty_rec k U T) u <->
    lr rhoA (updB rhoB k (lr rhoA rhoB U)) T u.
Proof.
  induction T as [n | X | T1 IH1 T2 IH2 | T1 IH1 | ];
    intros k U0 HU rhoA rhoB u; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + (* the opened type is U0 itself *)
      apply Nat.eqb_eq in E. subst n.
      simpl. unfold updB. rewrite Nat.eqb_refl. simpl.
      split.
      * intro Hx. split; [apply lr_lc in Hx; assumption | assumption].
      * intros [HA HB]. assumption.
    + (* the opened type is the variable itself *)
      apply Nat.eqb_neq in E.
      unfold updB. simpl.
      destruct (Nat.eqb n k) eqn:E2.
      * apply Nat.eqb_eq in E2. congruence.
      * split; intros [HA HB]; split; assumption.
  - reflexivity.
  - split.
    + intros [HA [HB HC]]. split; [assumption | split].
      * assumption.
      * intros v Hv. apply (proj1 (IH2 k U0 HU rhoA rhoB (etm_app u v))).
        apply HC. apply (proj2 (IH1 k U0 HU rhoA rhoB v)). assumption.
    + intros [HA [HB HC]]. split; [assumption | split].
      * assumption.
      * intros v Hv. apply (proj2 (IH2 k U0 HU rhoA rhoB (etm_app u v))).
        apply HC. apply (proj1 (IH1 k U0 HU rhoA rhoB v)). assumption.
  - split.
    + intros [HA [HB HC]]. split; [assumption | split].
      * assumption.
      * intros C HCc.
        apply (proj1 (lr_mapB_equiv T1 rhoA
          (updB (consB C rhoB) (S k) (lr rhoA (consB C rhoB) U0))
          (consB C (updB rhoB k (lr rhoA rhoB U0)))
          (updB_cons C (lr rhoA (consB C rhoB) U0) (lr rhoA rhoB U0) rhoB k
             (lr_consB_irrel U0 HU rhoA rhoB C)) (etm_tapp u))).
        apply (proj1 (IH1 (S k) U0 HU rhoA (consB C rhoB) (etm_tapp u))).
        apply HC. assumption.
    + intros [HA [HB HC]]. split; [assumption | split].
      * assumption.
      * intros C HCc.
        apply (proj2 (IH1 (S k) U0 HU rhoA (consB C rhoB) (etm_tapp u))).
        apply (proj2 (lr_mapB_equiv T1 rhoA
          (updB (consB C rhoB) (S k) (lr rhoA (consB C rhoB) U0))
          (consB C (updB rhoB k (lr rhoA rhoB U0)))
          (updB_cons C (lr rhoA (consB C rhoB) U0) (lr rhoA rhoB U0) rhoB k
             (lr_consB_irrel U0 HU rhoA rhoB C)) (etm_tapp u))).
        apply HC. assumption.
  - reflexivity.
Qed.

Lemma updB0_consB : forall (rhoB : nat -> etm -> Prop) (C : etm -> Prop),
  forall i, i < 1 -> forall u, updB rhoB 0 C i u <-> consB C rhoB i u.
Proof.
  intros rhoB C i Hi u. assert (i = 0) by lia. subst.
  unfold updB, consB. simpl. reflexivity.
Qed.

Lemma lr_open_ty : forall T U, lc_ty_at 1 T -> lc_ty_at 0 U ->
  forall rhoA rhoB u,
    lr rhoA rhoB (open_ty T U) u <->
    lr rhoA (consB (lr rhoA rhoB U) rhoB) T u.
Proof.
  intros T U HlcT HlcU rhoA rhoB u.
  assert (H := lr_open_ty_gen T 0 U HlcU rhoA rhoB u).
  split.
  - intro Hx. apply H in Hx.
    apply (proj1 (lr_mapB_agree T 1 HlcT rhoA
      (updB rhoB 0 (lr rhoA rhoB U)) (consB (lr rhoA rhoB U) rhoB)
      (updB0_consB rhoB (lr rhoA rhoB U)) u)).
    apply Hx.
  - intro Hx. apply H.
    apply (proj2 (lr_mapB_agree T 1 HlcT rhoA
      (updB rhoB 0 (lr rhoA rhoB U)) (consB (lr rhoA rhoB U) rhoB)
      (updB0_consB rhoB (lr rhoA rhoB U)) u)).
    apply Hx.
Qed.

(* ============================================================ *)
(* Part 5. The relation is closed under primitive recursion.     *)
(* ============================================================ *)

Lemma lr_sn : forall T rhoA rhoB, cand_val rhoA rhoB ->
  forall u, lr rhoA rhoB T u -> sn_e u.
Proof.
  intros T rhoA rhoB Hcv u Hu.
  apply (cand_sn (lr rhoA rhoB T)); [apply cand_lr; assumption | assumption].
Qed.

Lemma lr_step : forall T rhoA rhoB, cand_val rhoA rhoB ->
  forall u u', lr rhoA rhoB T u -> estep u u' -> lr rhoA rhoB T u'.
Proof.
  intros T rhoA rhoB Hcv u u' Hu Hst.
  eapply (cand_step (lr rhoA rhoB T)); [apply cand_lr; assumption | apply Hu | apply Hst].
Qed.

Lemma lr_nat_iff : forall rhoA rhoB u, lr rhoA rhoB Ty_Nat u <-> lc_e u /\ sn_e u.
Proof. intros. simpl. reflexivity. Qed.

(* Primitive recursion applied to an erased numeral. *)
Lemma lr_natrec_numeral : forall k b, sn_e b ->
  forall s, sn_e s ->
  forall rhoA rhoB T, cand_val rhoA rhoB ->
    lr rhoA rhoB T b ->
    lr rhoA rhoB (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
    lr rhoA rhoB T (etm_natrec (numeral_e k) b s).
Proof.
  induction k as [| k' IHk].
  - (* k = 0 *)
    intros b Hsnb. pose proof Hsnb as Hsnb0. induction Hsnb as [b Hstepb IHb].
    intros s Hsns. pose proof Hsns as Hsns0. induction Hsns as [s Hsteps IHs].
    intros rhoA rhoB T Hcv Hb Hs.
    apply cand_expand with (P := lr rhoA rhoB T).
    + apply cand_lr. assumption.
    + apply lc_e_natrec.
      * apply lc_e_zero.
      * apply lr_lc with (rhoA := rhoA) (rhoB := rhoB) (T := T). assumption.
      * apply lr_lc with (rhoA := rhoA) (rhoB := rhoB) (T := Ty_Arrow Ty_Nat (Ty_Arrow T T)). assumption.
    + apply not_evalue_natrec.
    + intros u Hu.
      destruct (estep_natrec_inv etm_zero b s u Hu) as
        [ [n' [Hst Hw]]
        | [ [b' [Hnum [Hst Hw]]]
          | [ [s' [Hnum [Hevb [Hst Hw]]]]
            | [ [Hn [Hevb [Hevs Hw]]]
              | [n0 [Hn [Hnum [Hevb [Hevs Hw]]]]] ] ] ] ].
      * subst u. exfalso. exact (evalue_no_step etm_zero ev_zero n' Hst).
      * subst u. apply (IHb b' Hst (Hstepb b' Hst) s Hsns0 rhoA rhoB T Hcv).
        -- apply (lr_step T rhoA rhoB Hcv b b' Hb Hst).
        -- apply Hs.
      * subst u. apply (IHs s' Hst (Hsteps s' Hst) rhoA rhoB T Hcv).
        -- apply Hb.
        -- apply (lr_step (Ty_Arrow Ty_Nat (Ty_Arrow T T)) rhoA rhoB Hcv s s' Hs Hst).
      * subst u. apply Hb.
      * subst u. inversion Hn.
  - (* k = S k' *)
    intros b Hsnb. pose proof Hsnb as Hsnb0. induction Hsnb as [b Hstepb IHb].
    intros s Hsns. pose proof Hsns as Hsns0. induction Hsns as [s Hsteps IHs].
    intros rhoA rhoB T Hcv Hb Hs.
    apply cand_expand with (P := lr rhoA rhoB T).
    + apply cand_lr. assumption.
    + apply lc_e_natrec.
      * apply lc_e_succ. apply lc_e_numeral.
      * apply lr_lc with (rhoA := rhoA) (rhoB := rhoB) (T := T). assumption.
      * apply lr_lc with (rhoA := rhoA) (rhoB := rhoB) (T := Ty_Arrow Ty_Nat (Ty_Arrow T T)). assumption.
    + apply not_evalue_natrec.
    + intros u Hu.
      destruct (estep_natrec_inv (etm_succ (numeral_e k')) b s u Hu) as
        [ [n' [Hst Hw]]
        | [ [b' [Hnum [Hst Hw]]]
          | [ [s' [Hnum [Hevb [Hst Hw]]]]
            | [ [Hn [Hevb [Hevs Hw]]]
              | [n0 [Hn [Hnum [Hevb [Hevs Hw]]]]] ] ] ] ].
      * subst u. exfalso.
        exact (evalue_no_step (numeral_e (S k'))
                 (numeric_value_e_evalue (numeral_e (S k')) (numeral_e_numeric (S k'))) n' Hst).
      * subst u. apply (IHb b' Hst (Hstepb b' Hst) s Hsns0 rhoA rhoB T Hcv).
        -- apply (lr_step T rhoA rhoB Hcv b b' Hb Hst).
        -- apply Hs.
      * subst u. apply (IHs s' Hst (Hsteps s' Hst) rhoA rhoB T Hcv).
        -- apply Hb.
        -- apply (lr_step (Ty_Arrow Ty_Nat (Ty_Arrow T T)) rhoA rhoB Hcv s s' Hs Hst).
      * subst u. inversion Hn.
      * subst u. inversion Hn; subst.
        pose proof (proj2 (proj2 Hs)) as Hcl.
        pose proof (Hcl (numeral_e k') (conj (lc_e_numeral k') (numeric_value_e_sn (numeral_e k') (numeral_e_numeric k')))) as Happ.
        apply (proj2 (proj2 Happ) (etm_natrec (numeral_e k') b s)).
        apply (IHk b Hsnb0 s Hsns0 rhoA rhoB T Hcv Hb Hs).
Qed.

(* Primitive recursion applied to any strongly normalizing erased term. *)
Lemma lr_natrec : forall n, sn_e n -> lc_e n ->
  forall b s rhoA rhoB T, cand_val rhoA rhoB ->
    lr rhoA rhoB T b ->
    lr rhoA rhoB (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
    lr rhoA rhoB T (etm_natrec n b s).
Proof.
  intros n Hsn. induction Hsn as [n Hstep IH].
  intros Hlcn b s rhoA rhoB T Hcv Hb Hs.
  apply cand_expand with (P := lr rhoA rhoB T).
  - apply cand_lr. assumption.
  - apply lc_e_natrec.
    + apply Hlcn.
    + apply lr_lc with (rhoA := rhoA) (rhoB := rhoB) (T := T). assumption.
    + apply lr_lc with (rhoA := rhoA) (rhoB := rhoB) (T := Ty_Arrow Ty_Nat (Ty_Arrow T T)). assumption.
  - apply not_evalue_natrec.
  - intros u Hu.
    destruct (estep_natrec_inv n b s u Hu) as
      [ [n' [Hst Hw]]
      | [ [b' [Hnum [Hst Hw]]]
        | [ [s' [Hnum [Hevb [Hst Hw]]]]
          | [ [Hn [Hevb [Hevs Hw]]]
            | [n0 [Hn [Hnum [Hevb [Hevs Hw]]]]] ] ] ] ].
    * subst u. apply (IH n' Hst (lc_e_step n n' Hlcn Hst) b s rhoA rhoB T Hcv Hb Hs).
    * subst u.
      destruct (numeric_value_e_numeral n Hnum) as [k Hk]. subst n.
      assert (Hsnb' : sn_e b') by (apply (lr_sn T rhoA rhoB Hcv); apply (lr_step T rhoA rhoB Hcv b b' Hb Hst)).
      assert (Hsns' : sn_e s) by (apply (lr_sn (Ty_Arrow Ty_Nat (Ty_Arrow T T)) rhoA rhoB Hcv s Hs)).
      apply (lr_natrec_numeral k b' Hsnb' s Hsns' rhoA rhoB T Hcv).
      + apply (lr_step T rhoA rhoB Hcv b b' Hb Hst).
      + apply Hs.
    * subst u.
      destruct (numeric_value_e_numeral n Hnum) as [k Hk]. subst n.
      assert (Hsnb' : sn_e b) by (apply (lr_sn T rhoA rhoB Hcv b Hb)).
      assert (Hsns' : sn_e s') by (apply (lr_sn (Ty_Arrow Ty_Nat (Ty_Arrow T T)) rhoA rhoB Hcv); apply (lr_step (Ty_Arrow Ty_Nat (Ty_Arrow T T)) rhoA rhoB Hcv s s' Hs Hst)).
      apply (lr_natrec_numeral k b Hsnb' s' Hsns' rhoA rhoB T Hcv).
      + apply Hb.
      + apply (lr_step (Ty_Arrow Ty_Nat (Ty_Arrow T T)) rhoA rhoB Hcv s s' Hs Hst).
    * subst u. subst n. apply Hb.
    * subst u.
      destruct (numeric_value_e_numeral n0 Hnum) as [k Hk]. subst n0. subst n.
      pose proof (proj2 (proj2 Hs)) as Hcl.
      pose proof (Hcl (numeral_e k) (conj (lc_e_numeral k) (numeric_value_e_sn (numeral_e k) (numeral_e_numeric k)))) as Happ.
      apply (proj2 (proj2 Happ) (etm_natrec (numeral_e k) b s)).
      assert (Hsnb' : sn_e b) by (apply (lr_sn T rhoA rhoB Hcv b Hb)).
      assert (Hsns' : sn_e s) by (apply (lr_sn (Ty_Arrow Ty_Nat (Ty_Arrow T T)) rhoA rhoB Hcv s Hs)).
      apply (lr_natrec_numeral k b Hsnb' s Hsns' rhoA rhoB T Hcv).
      + apply Hb.
      + apply Hs.
Qed.

(* ============================================================ *)
(* Part 6. Substitution commutes with opening, and the           *)
(* beta-expansion property for applications of abstractions.     *)
(* ============================================================ *)

Lemma subst_e_id : forall t, subst_e (fun x => etm_fvar x) t = t.
Proof.
  induction t; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal. assumption.
  - f_equal; assumption.
  - f_equal. assumption.
  - f_equal. assumption.
  - reflexivity.
  - f_equal. assumption.
  - f_equal; assumption.
Qed.

Lemma notin_app : forall (x : atom) l1 l2, ~ In x (l1 ++ l2) -> ~ In x l1 /\ ~ In x l2.
Proof.
  intros x l1 l2 H. split; intro Hx; apply H; [apply in_app_l | apply in_app_r]; assumption.
Qed.

Lemma subst_open_e_gen : forall b k x v sb sb',
  (forall y, lc_e (sb y)) ->
  ~ In x (fv_e b) ->
  sb' x = v ->
  (forall y, y <> x -> sb' y = sb y) ->
  subst_e sb' (open_e_rec k (etm_fvar x) b) = open_e_rec k v (subst_e sb b).
Proof.
  induction b as [i | y | b1 IH1 | b1 IH1 b2 IH2 | b1 IH1 | b1 IH1 | | b1 IH1
                 | b1 IH1 b2 IH2 b3 IH3];
    intros k x v sb sb' Hlc Hfresh Hx Hy; simpl.
  - destruct (Nat.eqb k i) eqn:E; simpl.
    + rewrite Hx. reflexivity.
    + reflexivity.
  - simpl in Hfresh. assert (Hyx : y <> x) by (intro EE; subst; apply Hfresh; simpl; auto).
    rewrite Hy; [| assumption].
    symmetry. apply (lc_e_open_id (sb y) (Hlc y) k v).
  - simpl in Hfresh.
    rewrite (IH1 (S k) x v sb sb' Hlc Hfresh Hx Hy). reflexivity.
  - apply notin_app in Hfresh. destruct Hfresh as [Hf1 Hf2].
    rewrite (IH1 k x v sb sb' Hlc Hf1 Hx Hy).
    rewrite (IH2 k x v sb sb' Hlc Hf2 Hx Hy). reflexivity.
  - simpl in Hfresh.
    rewrite (IH1 k x v sb sb' Hlc Hfresh Hx Hy). reflexivity.
  - simpl in Hfresh.
    rewrite (IH1 k x v sb sb' Hlc Hfresh Hx Hy). reflexivity.
  - reflexivity.
  - simpl in Hfresh.
    rewrite (IH1 k x v sb sb' Hlc Hfresh Hx Hy). reflexivity.
  - apply notin_app in Hfresh. destruct Hfresh as [Hf1 Hf23].
    apply notin_app in Hf23. destruct Hf23 as [Hf2 Hf3].
    rewrite (IH1 k x v sb sb' Hlc Hf1 Hx Hy).
    rewrite (IH2 k x v sb sb' Hlc Hf2 Hx Hy).
    rewrite (IH3 k x v sb sb' Hlc Hf3 Hx Hy). reflexivity.
Qed.

Lemma subst_open_e : forall b x v sb sb',
  (forall y, lc_e (sb y)) ->
  ~ In x (fv_e b) ->
  sb' x = v ->
  (forall y, y <> x -> sb' y = sb y) ->
  subst_e sb' (open_e b (etm_fvar x)) = open_e (subst_e sb b) v.
Proof.
  intros b x v sb sb' H1 H2 H3 H4. unfold open_e.
  apply (subst_open_e_gen b 0 x v sb sb'); assumption.
Qed.

Lemma lr_app_abs : forall T1 T2 rhoA rhoB b,
  cand_val rhoA rhoB ->
  lc_e_at 1 b ->
  (forall v, lr rhoA rhoB T1 v -> lr rhoA rhoB T2 (open_e b v)) ->
  forall v, lr rhoA rhoB T1 v -> lr rhoA rhoB T2 (etm_app (etm_abs b) v).
Proof.
  intros T1 T2 rhoA rhoB b Hcv Hlcb Hbody v Hv.
  assert (Hsn : sn_e v) by (apply (lr_sn T1 rhoA rhoB Hcv v Hv)).
  revert Hv. induction Hsn as [v0 Hstep IH]. intros Hv.
  apply cand_expand with (P := lr rhoA rhoB T2).
  - apply cand_lr. assumption.
  - apply lc_e_app.
    + apply lc_e_abs. assumption.
    + apply lr_lc with (rhoA := rhoA) (rhoB := rhoB) (T := T1). assumption.
  - apply not_evalue_app.
  - intros w Hw.
    destruct (estep_app_inv (etm_abs b) v0 w Hw) as
      [[b0 [Hu [Hev Hw']]] | [[u' [Hst Hw']] | [v' [Hevu [Hst Hw']]]]].
    + subst w. injection Hu as Hb0. subst b0. apply Hbody. apply Hv.
    + subst w. exfalso. exact (evalue_no_step (etm_abs b) (ev_abs b) u' Hst).
    + subst w. apply (IH v' Hst). apply (lr_step T1 rhoA rhoB Hcv v0 v' Hv Hst).
Qed.

Lemma consB_head_equiv : forall (C1 C2 : etm -> Prop) rho,
  (forall u, C1 u <-> C2 u) ->
  forall i u, consB C1 rho i u <-> consB C2 rho i u.
Proof.
  intros C1 C2 rho H i u. destruct i as [| j]; simpl; [apply H | reflexivity].
Qed.

Lemma lr_updA_head : forall rhoA rhoB X C, cand C ->
  forall u, lr (updA rhoA X C) rhoB (Ty_FVar X) u <-> C u.
Proof.
  intros rhoA rhoB X C HC u. simpl. unfold updA. rewrite Nat.eqb_refl. simpl.
  split.
  - intros [HA HB]. assumption.
  - intro H. split; [apply (cand_lc C HC u H) | assumption].
Qed.

(* ============================================================ *)
(* Part 7. The term-variable environment and the fundamental     *)
(* theorem for the logical relation.                             *)
(* ============================================================ *)

Definition env_rel (rhoA : atom -> etm -> Prop) (rhoB : nat -> etm -> Prop)
  (sb : atom -> etm) (Gamma : context) : Prop :=
  (forall y, lc_e (sb y)) /\
  (forall x T, lookup_context x Gamma = Some T -> lr rhoA rhoB T (sb x)).

Lemma upd_apply : forall (sb : atom -> etm) x v,
  (if Nat.eqb x x then v else sb x) = v.
Proof.
  intros sb x v. destruct (Nat.eqb x x) eqn:E.
  - reflexivity.
  - apply Nat.eqb_neq in E. exfalso. apply (E eq_refl).
Qed.

Fixpoint fv_context (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (x, T) :: Gamma' => fv_ty T ++ fv_context Gamma'
  end.

Lemma in_fv_context : forall Gamma x T X,
  lookup_context x Gamma = Some T -> In X (fv_ty T) -> In X (fv_context Gamma).
Proof.
  induction Gamma as [| [y Ty] Gamma' IH]; intros x T X Hlk HX; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + injection Hlk as HT. subst T. apply in_app_l. assumption.
    + apply in_app_r. apply (IH x T X Hlk HX).
Qed.

Lemma env_rel_updA : forall rhoA rhoB sb Gamma X C,
  ~ In X (fv_context Gamma) ->
  env_rel rhoA rhoB sb Gamma ->
  env_rel (updA rhoA X C) rhoB sb Gamma.
Proof.
  intros rhoA rhoB sb Gamma X C Hfresh [Hlc Henv]. split; [assumption |].
  intros x T Hlk.
  assert (HXnotin : ~ In X (fv_ty T)) by (intro HH; apply Hfresh; eapply in_fv_context; eauto).
  apply (proj2 (lr_updA_irrel T X C rhoA rhoB HXnotin (sb x))).
  apply Henv. assumption.
Qed.

Lemma env_rel_update : forall rhoA rhoB sb Gamma x T1 v,
  env_rel rhoA rhoB sb Gamma ->
  lr rhoA rhoB T1 v ->
  env_rel rhoA rhoB (fun y => if Nat.eqb y x then v else sb y) (update Gamma x T1).
Proof.
  intros rhoA rhoB sb Gamma x T1 v [Hlc Henv] Hv. split.
  - intros y. destruct (Nat.eqb y x) eqn:E.
    + apply lr_lc with (rhoA := rhoA) (rhoB := rhoB) (T := T1). assumption.
    + apply Hlc.
  - intros y A Hlk. simpl in Hlk.
    destruct (Nat.eqb y x) eqn:E.
    + apply Nat.eqb_eq in E. subst y. injection Hlk as HA. subst A.
      simpl. assumption.
    + apply Nat.eqb_neq in E.
      apply Henv with (x := y). assumption.
Qed.

Theorem fundamental : forall Delta Gamma t T, has_type Delta Gamma t T ->
  forall rhoA rhoB sb,
    cand_val rhoA rhoB ->
    env_rel rhoA rhoB sb Gamma ->
    lr rhoA rhoB T (subst_e sb (erase t)).
Proof.
  intros Delta Gamma t T Hty.
  induction Hty as
    [ Delta Gamma x T Hlk Hwf
    | L Delta Gamma T1 t2 T2 Hwf Hbody IHb
    | Delta Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
    | L Delta Gamma t T Hbody IHb
    | Delta Gamma t T U H1 IH1 Hwf
    | Delta Gamma
    | Delta Gamma n Hn IHn
    | Delta Gamma n b s T Hn IHn Hb IHb Hs IHs ];
    intros rhoA rhoB sb Hcv Henv.
  - (* T_Var *) simpl. apply (proj2 Henv). assumption.
  - (* T_Abs *)
    assert (Hlcb : lc_e_at 1 (erase t2)).
    { pose (x0 := fresh_atom L).
      assert (Hx0 : ~ In x0 L) by apply fresh_atom_notin.
      pose proof (lc_has_type_tm _ _ _ _ (Hbody x0 Hx0)) as Hlc.
      apply (lc_tm_open_refl t2 0 0 x0) in Hlc.
      apply (erase_lc 0 1) in Hlc. assumption. }
    simpl. split.
    + apply lc_e_abs.
      apply (lc_e_at_subst (erase t2) 1 sb Hlcb (proj1 Henv)).
    + split.
      * apply sn_e_evalue. apply ev_abs.
      * assert (Hbody' : forall v, lr rhoA rhoB T1 v ->
            lr rhoA rhoB T2 (open_e (subst_e sb (erase t2)) v)).
        { intros v Hv.
          set (x := fresh_atom (L ++ fv_e (erase t2))).
          assert (Hnotin : ~ In x (L ++ fv_e (erase t2))) by (subst x; apply fresh_atom_notin).
          assert (HxL : ~ In x L) by (intro HH; apply Hnotin; apply in_app_l; assumption).
          assert (Hxfv : ~ In x (fv_e (erase t2))) by (intro HH; apply Hnotin; apply in_app_r; assumption).
          pose proof (env_rel_update rhoA rhoB sb Gamma x T1 v Henv Hv) as Henv'.
          pose proof (IHb x HxL rhoA rhoB (fun y => if Nat.eqb y x then v else sb y) Hcv Henv') as IHx.
          rewrite erase_open_tm in IHx. simpl in IHx.
          assert (Heq : subst_e (fun y => if Nat.eqb y x then v else sb y)
                         (open_e (erase t2) (etm_fvar x))
                       = open_e (subst_e sb (erase t2)) v).
          { apply (subst_open_e (erase t2) x v sb (fun y => if Nat.eqb y x then v else sb y)).
            - apply (proj1 Henv).
            - assumption.
            - rewrite Nat.eqb_refl. reflexivity.
            - intros y Hy. destruct (Nat.eqb y x) eqn:E.
              + apply Nat.eqb_eq in E. congruence.
              + reflexivity. }
          rewrite Heq in IHx. exact IHx. }
        apply (lr_app_abs T1 T2 rhoA rhoB (subst_e sb (erase t2)) Hcv).
        -- apply (lc_e_at_subst (erase t2) 1 sb Hlcb (proj1 Henv)).
        -- apply Hbody'.
  - (* T_App *) simpl.
    pose proof (IH1 rhoA rhoB sb Hcv Henv) as H1'.
    pose proof (IH2 rhoA rhoB sb Hcv Henv) as H2'.
    exact (proj2 (proj2 H1') (subst_e sb (erase t2)) H2').
  - (* T_TAbs *)
    assert (Hlct : lc_e (erase t)).
    { pose (X0 := fresh_atom L).
      assert (HX0 : ~ In X0 L) by apply fresh_atom_notin.
      pose proof (lc_has_type_tm _ _ _ _ (Hbody X0 HX0)) as Hlc.
      apply (lc_tm_ty_open_refl t 0 0 X0) in Hlc.
      apply (erase_lc 1 0) in Hlc. assumption. }
    simpl. split.
    + apply lc_e_tabs.
      apply (lc_e_at_subst (erase t) 0 sb Hlct (proj1 Henv)).
    + split.
      * apply sn_e_evalue. apply ev_tabs.
      * intros C HCc.
        apply cand_expand with (P := lr rhoA (consB C rhoB) T).
        -- apply cand_lr. apply cand_val_consB; assumption.
        -- apply lc_e_tapp. apply lc_e_tabs.
           apply (lc_e_at_subst (erase t) 0 sb Hlct (proj1 Henv)).
        -- apply not_evalue_tapp.
        -- intros w Hw.
           destruct (estep_tapp_inv (etm_tabs (subst_e sb (erase t))) w Hw) as
             [[b0 [Hu Hw']] | [u' [Hst Hw']]].
           ++ subst w. injection Hu as Hb0. subst b0.
              set (X := fresh_atom (L ++ (fv_ty T ++ fv_context Gamma))).
              assert (Hnotin : ~ In X (L ++ (fv_ty T ++ fv_context Gamma))) by (subst X; apply fresh_atom_notin).
              apply notin_app in Hnotin. destruct Hnotin as [HXL Hrest].
              apply notin_app in Hrest. destruct Hrest as [HXfv HXctx].
              pose proof (cand_val_updA rhoA rhoB X C Hcv HCc) as Hcv'.
              pose proof (env_rel_updA rhoA rhoB sb Gamma X C HXctx Henv) as Henv'.
              pose proof (IHb X HXL (updA rhoA X C) rhoB sb Hcv' Henv') as IHx.
              rewrite erase_open_tm_ty in IHx.
              assert (HlcT : lc_ty_at 1 T).
              { pose proof (lc_has_type _ _ _ _ (Hbody X HXL)) as HlcOpen.
                apply (lc_ty_open_refl T 0 (Ty_FVar X)) in HlcOpen. assumption. }
              pose proof (lr_open_ty T (Ty_FVar X) HlcT (lc_ty_fvar 0 X)
                            (updA rhoA X C) rhoB (subst_e sb (erase t))) as Hopen.
              apply (proj1 Hopen) in IHx.
              assert (Hconv : lr (updA rhoA X C)
                                (consB (lr (updA rhoA X C) rhoB (Ty_FVar X)) rhoB) T
                                (subst_e sb (erase t))
                           <-> lr (updA rhoA X C) (consB C rhoB) T
                                (subst_e sb (erase t))).
              { apply lr_mapB_equiv. apply consB_head_equiv. apply lr_updA_head. assumption. }
              apply (proj1 Hconv) in IHx.
              apply (proj1 (lr_updA_irrel T X C rhoA (consB C rhoB) HXfv
                              (subst_e sb (erase t)))).
              exact IHx.
           ++ subst w. exfalso.
              exact (evalue_no_step (etm_tabs (subst_e sb (erase t))) (ev_tabs _) u' Hst).
  - (* T_TApp *) simpl.
    pose proof (IH1 rhoA rhoB sb Hcv Henv) as H1'.
    assert (HlcT : lc_ty_at 1 T).
    { pose proof (lc_has_type _ _ _ _ H1) as HlcAll.
      inversion HlcAll as [k i Hi | k X0 | | k A HA | ]; subst. assumption. }
    assert (HlcU : lc_ty_at 0 U) by (apply (wf_ty_lc Delta); assumption).
    assert (HcandU : cand (lr rhoA rhoB U)) by (apply cand_lr; assumption).
    pose proof (proj2 (proj2 H1') (lr rhoA rhoB U) HcandU) as H2'.
    apply (proj2 (lr_open_ty T U HlcT HlcU rhoA rhoB (etm_tapp (subst_e sb (erase t))))).
    exact H2'.
  - (* T_Zero *) simpl. split.
    + apply lc_e_zero.
    + apply sn_e_evalue. apply ev_zero.
  - (* T_Succ *) simpl.
    pose proof (IHn rhoA rhoB sb Hcv Henv) as Hn'.
    destruct Hn' as [Hlc Hsn]. split.
    + apply lc_e_succ. assumption.
    + apply sn_e_succ. assumption.
  - (* T_Rec *) simpl.
    pose proof (IHn rhoA rhoB sb Hcv Henv) as Hn'.
    pose proof (IHb rhoA rhoB sb Hcv Henv) as Hb'.
    pose proof (IHs rhoA rhoB sb Hcv Henv) as Hs'.
    destruct Hn' as [Hlcn Hsnn].
    apply (lr_natrec (subst_e sb (erase n)) Hsnn Hlcn
            (subst_e sb (erase b)) (subst_e sb (erase s)) rhoA rhoB T Hcv Hb' Hs').
Qed.

(* ============================================================ *)
(* Part 8. Strong normalization of closed well-typed terms.      *)
(* ============================================================ *)

Lemma sn_erase : forall u, sn_e u -> forall t, erase t = u -> strongly_normalizing t.
Proof.
  intros u H. induction H as [u Hstep IH]. intros t Heq.
  apply SN_intro. intros t' Ht'.
  apply IH with (u' := erase t').
  - rewrite <- Heq. apply erase_step. assumption.
  - reflexivity.
Qed.

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  intros t T Hty.
  set (rhoA := fun (_ : atom) (u : etm) => lc_e u /\ sn_e u).
  set (rhoB := fun (_ : nat) (u : etm) => lc_e u /\ sn_e u).
  assert (Hcv : cand_val rhoA rhoB).
  { split; intros; subst rhoA; subst rhoB; apply cand_lc_sn. }
  assert (Hlr : lr rhoA rhoB T (subst_e (fun x => etm_fvar x) (erase t))).
  { apply (fundamental [] empty t T Hty rhoA rhoB (fun x => etm_fvar x) Hcv).
    split.
    - intros y. simpl. apply lc_e_fvar.
    - intros x A Hlk. simpl in Hlk. discriminate. }
  rewrite subst_e_id in Hlr.
  assert (Hsn : sn_e (erase t)) by (apply (lr_sn T rhoA rhoB Hcv (erase t) Hlr)).
  apply (sn_erase (erase t) Hsn t eq_refl).
Qed.
End SystemFNormalizationRecursionHardTask.
