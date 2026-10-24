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

(* ===================================================================== *)
(* Basic infrastructure.                                                 *)
(* ===================================================================== *)

Lemma SN_step : forall t t', strongly_normalizing t -> step t t' -> strongly_normalizing t'.
Proof.
  intros t t' H Hst. induction H as [t Hred IH].
  apply Hred. exact Hst.
Qed.

Lemma numeric_value_lc : forall n, numeric_value n -> locally_closed_tm n.
Proof. induction 1; constructor; assumption. Qed.

Lemma numeric_no_step : forall n, numeric_value n -> forall u, ~ step n u.
Proof.
  intros n H. induction H as [| n Hn IH]; intros u Hstep.
  - inversion Hstep.
  - inversion Hstep; subst.
    match goal with
    | H : step n ?x |- _ => exact (IH x H)
    end.
Qed.

Lemma value_no_step : forall v, value v -> forall u, ~ step v u.
Proof.
  intros v Hv u Hstep.
  destruct Hv as [T t Hlc | t Hlc | n Hn].
  - inversion Hstep.
  - inversion Hstep.
  - apply (numeric_no_step n Hn u). assumption.
Qed.

Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof.
  intros v Hv. induction Hv as [T t Hlc | t Hlc | n Hn].
  - assumption.
  - assumption.
  - apply numeric_value_lc. assumption.
Qed.

Lemma SN_of_no_step : forall t, (forall u, ~ step t u) -> strongly_normalizing t.
Proof.
  intros t H. constructor. intros u Hst. exfalso. apply (H u). assumption.
Qed.

Lemma SN_abs : forall T t, strongly_normalizing (tm_abs T t).
Proof.
  intros. apply SN_of_no_step. intros u H; inversion H.
Qed.

Lemma SN_tabs : forall t, strongly_normalizing (tm_tabs t).
Proof.
  intros. apply SN_of_no_step. intros u H; inversion H.
Qed.

Lemma SN_zero : strongly_normalizing tm_zero.
Proof.
  apply SN_of_no_step. intros u H; inversion H.
Qed.

Lemma SN_succ : forall t, strongly_normalizing t -> strongly_normalizing (tm_succ t).
Proof.
  intros t H. induction H as [t Hred IH].
  apply SN_intro. intros u Hst. inversion Hst; subst.
  match goal with H : step t ?x |- _ => apply IH; exact H end.
Qed.

(* ===================================================================== *)
(* Erasure of type annotations.                                          *)
(* ===================================================================== *)

Fixpoint erase (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T t1 => tm_abs Ty_Nat (erase t1)
  | tm_app t1 t2 => tm_app (erase t1) (erase t2)
  | tm_tabs t1 => tm_tabs (erase t1)
  | tm_tapp t1 T => tm_tapp (erase t1) Ty_Nat
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (erase t1)
  | tm_natrec n b s => tm_natrec (erase n) (erase b) (erase s)
  end.

Lemma erase_idem : forall t, erase (erase t) = erase t.
Proof. induction t; simpl; congruence. Qed.

Lemma erase_open_tm_rec : forall k (u t : tm),
  erase (open_tm_rec k u t) = open_tm_rec k (erase u) (erase t).
Proof.
  intros k u t; revert k. induction t; intros k; simpl; try reflexivity;
    try (f_equal; auto).
  - destruct (Nat.eqb k n); reflexivity.
Qed.

Lemma erase_open_tm : forall (u t : tm),
  erase (open_tm t u) = open_tm (erase t) (erase u).
Proof. intros; unfold open_tm; apply erase_open_tm_rec. Qed.

Lemma erase_open_tm_ty_rec : forall k U (t : tm),
  erase (open_tm_ty_rec k U t) = erase t.
Proof.
  intros k U t; revert k. induction t; intros k; simpl; try congruence.
Qed.

Lemma erase_open_tm_ty : forall (t : tm) U,
  erase (open_tm_ty t U) = erase t.
Proof. intros; unfold open_tm_ty; apply erase_open_tm_ty_rec. Qed.

(* Parallel free-variable substitution. *)
Fixpoint subst_tm (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_abs T t1 => tm_abs T (subst_tm sigma t1)
  | tm_app t1 t2 => tm_app (subst_tm sigma t1) (subst_tm sigma t2)
  | tm_tabs t1 => tm_tabs (subst_tm sigma t1)
  | tm_tapp t1 T => tm_tapp (subst_tm sigma t1) T
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (subst_tm sigma t1)
  | tm_natrec n b s => tm_natrec (subst_tm sigma n) (subst_tm sigma b) (subst_tm sigma s)
  end.

Definition extend_sigma (x : atom) (v : tm) (sigma : atom -> tm) : atom -> tm :=
  fun y => if Nat.eqb y x then v else sigma y.

Lemma subst_tm_id : forall t, subst_tm tm_fvar t = t.
Proof. induction t; simpl; congruence. Qed.

Lemma erase_subst_tm : forall (sigma : atom -> tm) t,
  erase (subst_tm sigma t) = subst_tm (fun x => erase (sigma x)) (erase t).
Proof. intros sigma t; induction t; simpl; congruence. Qed.

(* Free term variables. *)
Fixpoint fv_tm (t : tm) : list atom :=
  match t with
  | tm_bvar i => []
  | tm_fvar x => [x]
  | tm_abs T t1 => fv_tm t1
  | tm_app t1 t2 => fv_tm t1 ++ fv_tm t2
  | tm_tabs t1 => fv_tm t1
  | tm_tapp t1 T => fv_tm t1
  | tm_zero => []
  | tm_succ t1 => fv_tm t1
  | tm_natrec n b s => fv_tm n ++ fv_tm b ++ fv_tm s
  end.

Lemma fv_erase : forall t, fv_tm (erase t) = fv_tm t.
Proof. induction t; simpl; congruence. Qed.

Lemma subst_tm_ext : forall (sigma1 sigma2 : atom -> tm) t,
  (forall x, In x (fv_tm t) -> sigma1 x = sigma2 x) ->
  subst_tm sigma1 t = subst_tm sigma2 t.
Proof.
  intros s1 s2 t H. induction t; simpl in *; try reflexivity.
  - apply H. simpl; auto.
  - f_equal. apply IHt. intros x Hx. apply H. exact Hx.
  - f_equal.
    + apply IHt1. intros x Hx. apply H. apply in_app_iff; left; exact Hx.
    + apply IHt2. intros x Hx. apply H. apply in_app_iff; right; exact Hx.
  - f_equal. apply IHt. intros x Hx. apply H. exact Hx.
  - f_equal. apply IHt. intros x Hx. apply H. exact Hx.
  - f_equal. apply IHt. intros x Hx. apply H. exact Hx.
  - f_equal.
    + apply IHt1. intros x Hx. apply H. repeat rewrite in_app_iff in *. tauto.
    + apply IHt2. intros x Hx. apply H. repeat rewrite in_app_iff in *. tauto.
    + apply IHt3. intros x Hx. apply H. repeat rewrite in_app_iff in *. tauto.
Qed.

Lemma subst_tm_extend_notin : forall x v (sigma : atom -> tm) t,
  ~ In x (fv_tm t) ->
  subst_tm (extend_sigma x v sigma) t = subst_tm sigma t.
Proof.
  intros x v sigma t Hx. apply subst_tm_ext. intros y Hy.
  unfold extend_sigma. destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst. exfalso. apply Hx. exact Hy.
  - reflexivity.
Qed.


(* ===================================================================== *)
(* Local closure: monotonicity, opening.                                 *)
(* ===================================================================== *)

Lemma lc_ty_mono : forall k T, lc_ty_at k T -> forall k', k <= k' -> lc_ty_at k' T.
Proof.
  intros k T H. induction H as [k i Hi | k X | k T1 T2 H1 IH1 H2 IH2 | k T H IH | k].
  - intros k' Hle. constructor. lia.
  - intros k' Hle. constructor.
  - intros k' Hle. constructor; [apply IH1 | apply IH2]; assumption.
  - intros k' Hle. apply lc_ty_all. apply IH. lia.
  - intros k' Hle. constructor.
Qed.

Lemma lc_tm_mono : forall K k t, lc_tm_at K k t ->
  forall K' k', K <= K' -> k <= k' -> lc_tm_at K' k' t.
Proof.
  intros K k t H. induction H as
    [ K k i Hi | K k x
    | K k T t Hty Hbody IH
    | K k t1 t2 H1 IH1 H2 IH2
    | K k t H IH
    | K k t T H IH Hty
    | K k
    | K k t H IH
    | K k n b s Hn IHn Hb IHb Hs IHs ].
  - intros K' k' HK Hk. constructor. lia.
  - intros K' k' HK Hk. constructor.
  - intros K' k' HK Hk. constructor.
    + apply lc_ty_mono with (k:=K); assumption.
    + apply IH; lia.
  - intros K' k' HK Hk. constructor.
    + apply IH1; assumption.
    + apply IH2; assumption.
  - intros K' k' HK Hk. constructor. apply IH; lia.
  - intros K' k' HK Hk. constructor.
    + apply IH; assumption.
    + apply lc_ty_mono with (k:=K); assumption.
  - intros K' k' HK Hk. constructor.
  - intros K' k' HK Hk. constructor. apply IH; assumption.
  - intros K' k' HK Hk. constructor.
    + apply IHn; assumption.
    + apply IHb; assumption.
    + apply IHs; assumption.
Qed.

Lemma lc_ty_open_rec : forall k T U,
  lc_ty_at (S k) T -> lc_ty_at k U -> lc_ty_at k (open_ty_rec k U T).
Proof.
  intros k T. revert k. induction T; intros k U Hlc HU; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. exact HU.
    + apply lc_ty_bvar. apply Nat.eqb_neq in E. inversion Hlc; lia.
  - constructor.
  - inversion Hlc; subst. apply lc_ty_arrow; [apply IHT1 with (k:=k) (U:=U); assumption | apply IHT2 with (k:=k) (U:=U); assumption].
  - inversion Hlc; subst. apply lc_ty_all.
    apply IHT with (k:=S k) (U:=U).
    + assumption.
    + apply lc_ty_mono with (k:=k); [assumption | lia].
  - constructor.
Qed.

Lemma lc_ty_open_rec_inv : forall k T U,
  lc_ty_at k (open_ty_rec k U T) -> lc_ty_at (S k) T.
Proof.
  intros k T. revert k. induction T; intros k U Hlc; simpl in Hlc.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. apply lc_ty_bvar. lia.
    + inversion Hlc; subst. apply lc_ty_bvar. lia.
  - constructor.
  - inversion Hlc; subst. apply lc_ty_arrow; [apply IHT1 with (k:=k) (U:=U); assumption | apply IHT2 with (k:=k) (U:=U); assumption].
  - inversion Hlc; subst. apply lc_ty_all.
    apply IHT with (k:=S k) (U:=U); assumption.
  - constructor.
Qed.

Lemma lc_ty_open : forall T U,
  lc_ty_at 1 T -> locally_closed_ty U -> locally_closed_ty (open_ty T U).
Proof. intros T U H HU. unfold open_ty, locally_closed_ty. apply lc_ty_open_rec; assumption. Qed.

(* ===================================================================== *)
(* Erasure preserves closure, values and steps.                          *)
(* ===================================================================== *)

Lemma numeric_value_erase : forall n, numeric_value n -> numeric_value (erase n).
Proof.
  intros n H. induction H; simpl; [constructor | constructor; assumption].
Qed.

Lemma lc_erase : forall K k t, lc_tm_at K k t -> forall K', lc_tm_at K' k (erase t).
Proof.
  intros K k t H. induction H as
    [ K k i Hi | K k x
    | K k T t Hty Hbody IH
    | K k t1 t2 H1 IH1 H2 IH2
    | K k t H IH
    | K k t T H IH Hty
    | K k
    | K k t H IH
    | K k n b s Hn IHn Hb IHb Hs IHs ].
  - simpl. constructor. assumption.
  - simpl. constructor.
  - simpl. constructor. constructor. apply IH.
  - simpl. constructor; [apply IH1 | apply IH2].
  - simpl. constructor. apply IH.
  - simpl. constructor; [apply IH | constructor].
  - simpl. constructor.
  - simpl. constructor. apply IH.
  - simpl. constructor; [apply IHn | apply IHb | apply IHs].
Qed.

Lemma value_erase : forall v, value v -> value (erase v).
Proof.
  intros v Hv. destruct Hv as [T t Hlc | t Hlc | n Hn].
  - simpl. apply v_abs. change (lc_tm_at 0 0 (erase (tm_abs T t))).
    apply lc_erase with (K:=0) (k:=0); assumption.
  - simpl. apply v_tabs. change (lc_tm_at 0 0 (erase (tm_tabs t))).
    apply lc_erase with (K:=0) (k:=0); assumption.
  - simpl. apply v_nat. apply numeric_value_erase; assumption.
Qed.

Lemma lc_open_id_rec : forall K k t, lc_tm_at K k t ->
  forall j u, k <= j -> open_tm_rec j u t = t.
Proof.
  intros K k t H. induction H as
    [ K k i Hi | K k x
    | K k T t Hty Hbody IH
    | K k t1 t2 H1 IH1 H2 IH2
    | K k t H IH
    | K k t T H IH Hty
    | K k
    | K k t H IH
    | K k n b s Hn IHn Hb IHb Hs IHs ].
  - intros j u Hj. simpl. destruct (Nat.eqb j i) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + reflexivity.
  - intros j u Hj. reflexivity.
  - intros j u Hj. simpl. f_equal. apply IH. lia.
  - intros j u Hj. simpl. f_equal; [apply IH1 | apply IH2]; assumption.
  - intros j u Hj. simpl. f_equal. apply IH. assumption.
  - intros j u Hj. simpl. f_equal. apply IH. assumption.
  - intros j u Hj. reflexivity.
  - intros j u Hj. simpl. f_equal. apply IH. assumption.
  - intros j u Hj. simpl. f_equal; [apply IHn | apply IHb | apply IHs]; assumption.
Qed.

Lemma lc_open_id : forall t, locally_closed_tm t -> forall j u, open_tm_rec j u t = t.
Proof.
  intros t H j u. apply lc_open_id_rec with (K:=0) (k:=0); [assumption | lia].
Qed.

Lemma open_tm_ty_erased : forall t, erase t = t ->
  forall k U, open_tm_ty_rec k U t = t.
Proof.
  intros t H. induction t; intros k U; simpl in *; try reflexivity.
  - (* abs *) injection H as HT Hb. subst. simpl.
    rewrite (IHt Hb k U). reflexivity.
  - (* app *) injection H as H1 H2. subst. simpl. rewrite (IHt1 H1 k U), (IHt2 H2 k U). reflexivity.
  - (* tabs *) simpl. f_equal. apply IHt. injection H as Hb. exact Hb.
  - (* tapp *) injection H as Hb HT. subst. simpl.
    rewrite (IHt Hb k U). reflexivity.
  - (* succ *) simpl. f_equal. apply IHt. injection H as Hb. exact Hb.
  - (* natrec *) injection H as H1 H2 H3. subst. simpl.
    rewrite (IHt1 H1 k U), (IHt2 H2 k U), (IHt3 H3 k U). reflexivity.
Qed.

Lemma open_tm_ty_erase : forall t U, open_tm_ty (erase t) U = erase t.
Proof. intros. apply open_tm_ty_erased. apply erase_idem. Qed.

Lemma step_erase : forall t t', step t t' -> step (erase t) (erase t').
Proof.
  intros t t' H. induction H as
    [ T t v Hlc Hv
    | t1 t1' t2 Hst IH Hlc
    | v1 t2 t2' Hv Hst IH
    | t T Hlc Hlcty
    | t t' T Hst IH Hlcty
    | t t' Hst IH
    | n n' b s Hst IH Hlcb Hlcs
    | n b b' s Hnv Hst IH Hlcs
    | n b s s' Hnv Hvb Hst IH
    | b s Hvb Hvs
    | n b s Hnv Hvb Hvs ].
  - rewrite erase_open_tm. simpl. apply ST_AppAbs.
    + change (lc_tm_at 0 0 (erase (tm_abs T t))). apply lc_erase with (K:=0) (k:=0). exact Hlc.
    + apply value_erase. exact Hv.
  - simpl. apply ST_App1.
    + apply IH.
    + apply lc_erase with (K:=0) (k:=0). exact Hlc.
  - simpl. apply ST_App2.
    + apply value_erase. exact Hv.
    + apply IH.
  - replace (erase (open_tm_ty t T)) with (open_tm_ty (erase t) Ty_Nat).
    2: { rewrite erase_open_tm_ty. apply open_tm_ty_erase. }
    simpl. apply ST_TAppTabs.
    + change (lc_tm_at 0 0 (erase (tm_tabs t))). apply lc_erase with (K:=0) (k:=0). exact Hlc.
    + constructor.
  - simpl. apply ST_TApp.
    + apply IH.
    + constructor.
  - simpl. apply ST_Succ. apply IH.
  - simpl. apply ST_RecArg.
    + apply IH.
    + apply lc_erase with (K:=0) (k:=0). exact Hlcb.
    + apply lc_erase with (K:=0) (k:=0). exact Hlcs.
  - simpl. apply ST_RecBase.
    + apply numeric_value_erase. exact Hnv.
    + apply IH.
    + apply lc_erase with (K:=0) (k:=0). exact Hlcs.
  - simpl. apply ST_RecStep.
    + apply numeric_value_erase. exact Hnv.
    + apply value_erase. exact Hvb.
    + apply IH.
  - simpl. apply ST_RecZero.
    + apply value_erase. exact Hvb.
    + apply value_erase. exact Hvs.
  - simpl. apply ST_RecSucc.
    + apply numeric_value_erase. exact Hnv.
    + apply value_erase. exact Hvb.
    + apply value_erase. exact Hvs.
Qed.

Lemma step_erase_id : forall t t', step t t' -> erase t = t -> erase t' = t'.
Proof.
  intros t t' H. induction H as
    [ T t v Hlc Hv
    | t1 t1' t2 Hst IH Hlc
    | v1 t2 t2' Hv Hst IH
    | t T Hlc Hlcty
    | t t' T Hst IH Hlcty
    | t t' Hst IH
    | n n' b s Hst IH Hlcb Hlcs
    | n b b' s Hnv Hst IH Hlcs
    | n b s s' Hnv Hvb Hst IH
    | b s Hvb Hvs
    | n b s Hnv Hvb Hvs ]; intros He.
  - simpl in He. injection He as HT Ht0 Hv0. subst.
    rewrite erase_open_tm, Ht0, Hv0. reflexivity.
  - simpl in He. injection He as Ht1_0 Ht2_0. subst.
    simpl. rewrite (IH Ht1_0), Ht2_0. reflexivity.
  - simpl in He. injection He as Hv1_0 Ht2_0. subst.
    simpl. rewrite Hv1_0, (IH Ht2_0). reflexivity.
  - simpl in He. injection He as Ht0 HT. subst.
    rewrite erase_open_tm_ty, Ht0. symmetry. apply open_tm_ty_erased; assumption.
  - simpl in He. injection He as Ht0 HT. subst.
    simpl. rewrite (IH Ht0). reflexivity.
  - simpl in He. injection He as Ht0. subst.
    simpl. rewrite (IH Ht0). reflexivity.
  - simpl in He. injection He as Hn0 Hb0 Hs0. subst.
    simpl. rewrite (IH Hn0), Hb0, Hs0. reflexivity.
  - simpl in He. injection He as Hn0 Hb0 Hs0. subst.
    simpl. rewrite Hn0, (IH Hb0), Hs0. reflexivity.
  - simpl in He. injection He as Hn0 Hb0 Hs0. subst.
    simpl. rewrite Hn0, Hb0, (IH Hs0). reflexivity.
  - simpl in He. injection He as Hb0 Hs0. subst. assumption.
  - simpl in He. injection He as Hn0 Hb0 Hs0. subst.
    simpl. rewrite Hb0, Hn0, Hs0. reflexivity.
Qed.

(* ===================================================================== *)
(* Fresh names.                                                          *)
(* ===================================================================== *)

Definition fresh (l : list atom) : atom := S (fold_right Nat.max 0 l).

Lemma in_le_fold_max : forall l x, In x l -> x <= fold_right Nat.max 0 l.
Proof.
  induction l as [| a l IH]; simpl; intros x Hx.
  - contradiction.
  - destruct Hx as [<- | Hx].
    + apply Nat.le_max_l.
    + transitivity (fold_right Nat.max 0 l); [apply IH; assumption | apply Nat.le_max_r].
Qed.

Lemma fresh_notin : forall l, ~ In (fresh l) l.
Proof.
  intros l H. unfold fresh in H. pose proof (in_le_fold_max l (S (fold_right Nat.max 0 l)) H). lia.
Qed.

(* ===================================================================== *)
(* The type-indexed logical relation.                                    *)
(* ===================================================================== *)

Definition Rel := tm -> Prop.

Definition top : Rel := fun t => strongly_normalizing (erase t).

Inductive value_form : tm -> Prop :=
  | vf_abs : forall T b, value_form (tm_abs T b)
  | vf_tabs : forall b, value_form (tm_tabs b)
  | vf_zero : value_form tm_zero
  | vf_succ : forall n, value_form n -> value_form (tm_succ n).

Lemma numeric_value_value_form : forall n, numeric_value n -> value_form n.
Proof. induction 1; constructor; assumption. Qed.

Lemma value_value_form : forall v, value v -> value_form v.
Proof.
  intros v Hv. destruct Hv as [T b Hlc | b Hlc | n Hn].
  - apply vf_abs.
  - apply vf_tabs.
  - apply numeric_value_value_form. assumption.
Qed.

Definition neutral (t : tm) : Prop := ~ value_form t.

Definition cand (C : Rel) : Prop :=
  (forall t, C t -> strongly_normalizing (erase t))
  /\ (forall t t', C t -> step (erase t) t' -> C t')
  /\ (forall t, strongly_normalizing (erase t) -> neutral (erase t) ->
        (forall t', step (erase t) t' -> C t') -> C t)
  /\ (forall t, C t <-> C (erase t)).

Definition cand_xi (xi : atom -> Rel) : Prop := forall X, cand (xi X).

Fixpoint fv_ty (T : ty) : list atom :=
  match T with
  | Ty_BVar i => []
  | Ty_FVar X => [X]
  | Ty_Arrow T1 T2 => fv_ty T1 ++ fv_ty T2
  | Ty_All T1 => fv_ty T1
  | Ty_Nat => []
  end.

Fixpoint nth_rel (i : nat) (bs : list Rel) : Rel :=
  match i, bs with
  | O, [] => top
  | O, C :: _ => C
  | S j, [] => top
  | S j, _ :: bs' => nth_rel j bs'
  end.

Fixpoint insert_rel (k : nat) (C : Rel) (bs : list Rel) : list Rel :=
  match k with
  | O => C :: bs
  | S k' => match bs with
            | [] => top :: insert_rel k' C []
            | b :: bs' => b :: insert_rel k' C bs'
            end
  end.

Definition cand_stack (bs : list Rel) : Prop := forall i, cand (nth_rel i bs).

Fixpoint R (T : ty) (xi : atom -> Rel) (bs : list Rel) (t : tm) : Prop :=
  match T with
  | Ty_BVar i => nth_rel i bs (erase t)
  | Ty_FVar X => xi X (erase t)
  | Ty_Arrow T1 T2 =>
      strongly_normalizing (erase t)
      /\ (forall v, multi (erase t) v -> value v -> exists T0 b, v = tm_abs T0 b)
      /\ (forall T0 b, multi (erase t) (tm_abs T0 b) ->
            forall v, value v -> R T1 xi bs v -> R T2 xi bs (open_tm b v))
  | Ty_All T1 =>
      strongly_normalizing (erase t)
      /\ (forall v, multi (erase t) v -> value v -> exists b, v = tm_tabs b)
      /\ (forall b, multi (erase t) (tm_tabs b) ->
            forall C, cand C -> R T1 xi (C :: bs) b)
  | Ty_Nat => strongly_normalizing (erase t)
  end.

(* --------------------------------------------------------------------- *)
(* Basic facts about candidates and stacks.                              *)
(* --------------------------------------------------------------------- *)

Lemma cand_top : cand top.
Proof. unfold cand, top, neutral. split.
- intros t H. exact H.
- split.
  + intros t t' H Hstep.
    assert (He : erase t' = t') by (apply (step_erase_id (erase t) t'); [exact Hstep | apply erase_idem]).
    rewrite He. exact (SN_step (erase t) t' H Hstep).
  + split.
    * intros t H Hn Hsteps. exact H.
    * intros t. split; intro H.
      -- rewrite erase_idem. exact H.
      -- rewrite erase_idem in H. exact H.
Qed.

Lemma cand_stack_nil : cand_stack [].
Proof. intro i. destruct i; simpl; apply cand_top. Qed.

Lemma cand_stack_cons : forall C bs,
  cand_stack (C :: bs) <-> cand C /\ cand_stack bs.
Proof.
  intros C bs. unfold cand_stack. split.
  - intros H. split.
    + exact (H 0).
    + intro i. exact (H (S i)).
  - intros [HC Hs] [| i]; simpl; auto.
Qed.

Lemma nth_rel_insert_lt : forall i k C bs, i < k ->
  nth_rel i (insert_rel k C bs) = nth_rel i bs.
Proof.
  intros i. induction i; intros k C bs Hik.
  - destruct k; [lia | simpl]. destruct bs; simpl; reflexivity.
  - destruct k as [| k']; [lia | simpl]. destruct bs; simpl.
    + rewrite (IHi k' C [] ltac:(lia)). destruct i; simpl; reflexivity.
    + apply IHi. lia.
Qed.

Lemma nth_rel_insert_eq : forall k C bs,
  nth_rel k (insert_rel k C bs) = C.
Proof.
  induction k; intros C bs.
  - simpl. reflexivity.
  - destruct bs; simpl; apply IHk.
Qed.

Lemma insert_rel_ext_same : forall k C1 C2 bs,
  (forall t, C1 t <-> C2 t) ->
  forall i t, nth_rel i (insert_rel k C1 bs) t <-> nth_rel i (insert_rel k C2 bs) t.
Proof.
  induction k as [| k IH]; intros C1 C2 bs Heq i t.
  - destruct i as [| i]; simpl; [apply Heq | apply iff_refl].
  - destruct bs as [| b bs'].
    + destruct i as [| i]; simpl; [apply iff_refl | apply (IH C1 C2 [] Heq i t)].
    + destruct i as [| i]; simpl; [apply iff_refl | apply (IH C1 C2 bs' Heq i t)].
Qed.

(* --------------------------------------------------------------------- *)
(* Multi-step facts.                                                     *)
(* --------------------------------------------------------------------- *)

Lemma multi_trans : forall x y z, multi x y -> multi y z -> multi x z.
Proof.
  intros x y z Hxy. revert z. induction Hxy as [x | x y0 z0 Hst Hm IH].
  - intros zz Hmz. exact Hmz.
  - intros zz Hmz. apply multi_step with y0; [exact Hst | apply IH; exact Hmz].
Qed.

Lemma multi_cases : forall s u, multi s u -> u = s \/ (exists y, step s y /\ multi y u).
Proof.
  intros s u H. induction H as [x | x y z Hst Hm IH].
  - left; reflexivity.
  - right. exists y. split; [exact Hst | exact Hm].
Qed.

Lemma step_abs_false : forall T b u, ~ step (tm_abs T b) u.
Proof. intros T b u H; inversion H. Qed.

Lemma step_tabs_false : forall b u, ~ step (tm_tabs b) u.
Proof. intros b u H; inversion H. Qed.

Lemma multi_abs_inv : forall T b u, multi (tm_abs T b) u -> u = tm_abs T b.
Proof.
  intros T b u H. destruct (multi_cases (tm_abs T b) u H) as [Heq | [y [Hst Hm]]].
  - exact Heq.
  - exfalso. exact (step_abs_false T b y Hst).
Qed.

Lemma multi_tabs_inv : forall b u, multi (tm_tabs b) u -> u = tm_tabs b.
Proof.
  intros b u H. destruct (multi_cases (tm_tabs b) u H) as [Heq | [y [Hst Hm]]].
  - exact Heq.
  - exfalso. exact (step_tabs_false b y Hst).
Qed.

(* --------------------------------------------------------------------- *)
(* The relation only depends on the erasure of the term.                 *)
(* --------------------------------------------------------------------- *)

Lemma R_erase_eq : forall T xi bs t, R T xi bs t <-> R T xi bs (erase t).
Proof.
  intros T. induction T; intros xi bs t; simpl; rewrite erase_idem; reflexivity.
Qed.

Lemma R_erase_congr : forall T xi bs t t',
  erase t = erase t' -> (R T xi bs t <-> R T xi bs t').
Proof.
  intros T xi bs t t' He.
  rewrite (R_erase_eq T xi bs t), (R_erase_eq T xi bs t'), He. reflexivity.
Qed.

(* --------------------------------------------------------------------- *)
(* The relation is a candidate.                                          *)
(* --------------------------------------------------------------------- *)

Lemma R_sn : forall T xi bs t,
  (forall X, In X (fv_ty T) -> cand (xi X)) ->
  cand_stack bs ->
  R T xi bs t -> strongly_normalizing (erase t).
Proof.
  intros T xi bs t Hxi Hbs HR. destruct T; simpl in *.
  - rewrite <- (erase_idem t). exact (proj1 (Hbs n) (erase t) HR).
  - rewrite <- (erase_idem t). exact (proj1 (Hxi a (in_eq a [])) (erase t) HR).
  - exact (proj1 HR).
  - exact (proj1 HR).
  - exact HR.
Qed.

Lemma R_step : forall T xi bs t t',
  (forall X, In X (fv_ty T) -> cand (xi X)) ->
  cand_stack bs ->
  R T xi bs t -> step (erase t) t' -> R T xi bs t'.
Proof.
  intros T xi bs t t' Hxi Hbs HR Hstep.
  assert (He : erase t' = t').
  { apply (step_erase_id (erase t) t'); [exact Hstep | apply erase_idem]. }
  assert (Hst' : step (erase (erase t)) t') by (rewrite erase_idem; exact Hstep).
  destruct T; simpl in *.
  - rewrite He. exact (proj1 (proj2 (Hbs n)) (erase t) t' HR Hst').
  - rewrite He. exact (proj1 (proj2 (Hxi a (in_eq a []))) (erase t) t' HR Hst').
  - rewrite He. split; [| split].
    + exact (SN_step (erase t) t' (proj1 HR) Hstep).
    + intros v Hm Hv. apply (proj1 (proj2 HR) v).
      * apply multi_step with t'; [exact Hstep | exact Hm].
      * exact Hv.
    + intros T0 b Hm v Hv HR1. apply (proj2 (proj2 HR) T0 b).
      * apply multi_step with t'; [exact Hstep | exact Hm].
      * exact Hv.
      * exact HR1.
  - rewrite He. split; [| split].
    + exact (SN_step (erase t) t' (proj1 HR) Hstep).
    + intros v Hm Hv. apply (proj1 (proj2 HR) v).
      * apply multi_step with t'; [exact Hstep | exact Hm].
      * exact Hv.
    + intros b Hm C HC. apply (proj2 (proj2 HR) b).
      * apply multi_step with t'; [exact Hstep | exact Hm].
      * exact HC.
  - rewrite He. exact (SN_step (erase t) t' HR Hstep).
Qed.

Lemma R_neutral : forall T xi bs t,
  (forall X, In X (fv_ty T) -> cand (xi X)) ->
  cand_stack bs ->
  strongly_normalizing (erase t) ->
  neutral (erase t) ->
  (forall t', step (erase t) t' -> R T xi bs t') ->
  R T xi bs t.
Proof.
  intros T. induction T; intros xi bs t Hxi Hbs Hsn Hn Hsteps; simpl in *.
  - apply (proj1 (proj2 (proj2 (Hbs n))) (erase t)).
    + rewrite erase_idem. exact Hsn.
    + unfold neutral. rewrite erase_idem. exact Hn.
    + intros t' Hst.
      rewrite erase_idem in Hst.
      assert (He : erase t' = t')
        by (apply (step_erase_id (erase t) t'); [exact Hst | apply erase_idem]).
      rewrite <- He. apply Hsteps. exact Hst.
  - apply (proj1 (proj2 (proj2 (Hxi a (in_eq a [])))) (erase t)).
    + rewrite erase_idem. exact Hsn.
    + unfold neutral. rewrite erase_idem. exact Hn.
    + intros t' Hst.
      rewrite erase_idem in Hst.
      assert (He : erase t' = t')
        by (apply (step_erase_id (erase t) t'); [exact Hst | apply erase_idem]).
      rewrite <- He. apply Hsteps. exact Hst.
  - split; [exact Hsn | split].
    + intros v Hm Hv.
      destruct (multi_cases (erase t) v Hm) as [Heq | [y [Hst Hm']]].
      * exfalso. apply Hn. rewrite <- Heq. apply value_value_form. exact Hv.
      * assert (He : erase y = y)
          by (apply (step_erase_id (erase t) y); [exact Hst | apply erase_idem]).
        rewrite <- He in Hm'.
        exact (proj1 (proj2 (Hsteps y Hst)) v Hm' Hv).
    + intros T0 b Hm v Hv HR1.
      destruct (multi_cases (erase t) (tm_abs T0 b) Hm) as [Heq | [y [Hst Hm']]].
      * exfalso. apply Hn. rewrite <- Heq. apply vf_abs.
      * assert (He : erase y = y)
          by (apply (step_erase_id (erase t) y); [exact Hst | apply erase_idem]).
        rewrite <- He in Hm'.
        exact (proj2 (proj2 (Hsteps y Hst)) T0 b Hm' v Hv HR1).
  - split; [exact Hsn | split].
    + intros v Hm Hv.
      destruct (multi_cases (erase t) v Hm) as [Heq | [y [Hst Hm']]].
      * exfalso. apply Hn. rewrite <- Heq. apply value_value_form. exact Hv.
      * assert (He : erase y = y)
          by (apply (step_erase_id (erase t) y); [exact Hst | apply erase_idem]).
        rewrite <- He in Hm'.
        exact (proj1 (proj2 (Hsteps y Hst)) v Hm' Hv).
    + intros b Hm C HC.
      destruct (multi_cases (erase t) (tm_tabs b) Hm) as [Heq | [y [Hst Hm']]].
      * exfalso. apply Hn. rewrite <- Heq. apply vf_tabs.
      * assert (He : erase y = y)
          by (apply (step_erase_id (erase t) y); [exact Hst | apply erase_idem]).
        rewrite <- He in Hm'.
        exact (proj2 (proj2 (Hsteps y Hst)) b Hm' C HC).
  - exact Hsn.
Qed.

Lemma cand_R : forall T xi bs,
  (forall X, In X (fv_ty T) -> cand (xi X)) ->
  cand_stack bs ->
  cand (R T xi bs).
Proof.
  intros T xi bs Hxi Hbs. unfold cand. split; [| split; [| split]].
  - intros t HR. apply (R_sn T xi bs t Hxi Hbs HR).
  - intros t t' HR Hst. apply (R_step T xi bs t t' Hxi Hbs HR Hst).
  - intros t Hsn Hn Hsteps. apply (R_neutral T xi bs t Hxi Hbs Hsn Hn Hsteps).
  - intros t. apply R_erase_eq.
Qed.

(* --------------------------------------------------------------------- *)
(* The relation depends only on the free type variables in scope.        *)
(* --------------------------------------------------------------------- *)

Lemma R_agree_xi : forall T xi xi' bs,
  (forall X, In X (fv_ty T) -> forall t, xi X t <-> xi' X t) ->
  forall t, R T xi bs t <-> R T xi' bs t.
Proof.
  induction T as [n | a | T1 IHT1 T2 IHT2 | T0 IHT0 | ]; intros xi xi' bs Hag t; simpl.
  - reflexivity.
  - apply Hag. simpl; auto.
  - assert (H1 : forall X, In X (fv_ty T1) -> forall t, xi X t <-> xi' X t).
    { intros X HX. apply Hag. simpl. apply in_app_iff. left. exact HX. }
    assert (H2 : forall X, In X (fv_ty T2) -> forall t, xi X t <-> xi' X t).
    { intros X HX. apply Hag. simpl. apply in_app_iff. right. exact HX. }
    split.
    + intros [Hsn [Hsh Hm]]. split; [exact Hsn | split; [exact Hsh |]].
      intros T0 b Hm0 v Hv HR1.
      apply (proj1 (IHT2 xi xi' bs H2 (open_tm b v))).
      exact (Hm T0 b Hm0 v Hv (proj2 (IHT1 xi xi' bs H1 v) HR1)).
    + intros [Hsn [Hsh Hm]]. split; [exact Hsn | split; [exact Hsh |]].
      intros T0 b Hm0 v Hv HR1.
      apply (proj2 (IHT2 xi xi' bs H2 (open_tm b v))).
      exact (Hm T0 b Hm0 v Hv (proj1 (IHT1 xi xi' bs H1 v) HR1)).
  - split.
    + intros [Hsn [Hsh Hm]]. split; [exact Hsn | split; [exact Hsh |]].
      intros b Hm0 C HC.
      apply (proj1 (IHT0 xi xi' (C :: bs) Hag b)).
      exact (Hm b Hm0 C HC).
    + intros [Hsn [Hsh Hm]]. split; [exact Hsn | split; [exact Hsh |]].
      intros b Hm0 C HC.
      apply (proj2 (IHT0 xi xi' (C :: bs) Hag b)).
      exact (Hm b Hm0 C HC).
  - reflexivity.
Qed.

(* --------------------------------------------------------------------- *)
(* The relation depends only on the first entries of the stack.          *)
(* --------------------------------------------------------------------- *)

Lemma R_stack_congr : forall T xi bs bs',
  (forall i t, nth_rel i bs t <-> nth_rel i bs' t) ->
  forall t, R T xi bs t <-> R T xi bs' t.
Proof.
  induction T as [n | a | T1 IHT1 T2 IHT2 | T0 IHT0 | ]; intros xi bs bs' Hag t; simpl.
  - apply Hag.
  - reflexivity.
  - split.
    + intros [Hsn [Hsh Hm]]. split; [exact Hsn | split; [exact Hsh |]].
      intros T0 b Hm0 v Hv HR1.
      apply (proj1 (IHT2 xi bs bs' Hag (open_tm b v))).
      exact (Hm T0 b Hm0 v Hv (proj2 (IHT1 xi bs bs' Hag v) HR1)).
    + intros [Hsn [Hsh Hm]]. split; [exact Hsn | split; [exact Hsh |]].
      intros T0 b Hm0 v Hv HR1.
      apply (proj2 (IHT2 xi bs bs' Hag (open_tm b v))).
      exact (Hm T0 b Hm0 v Hv (proj1 (IHT1 xi bs bs' Hag v) HR1)).
  - assert (Hag' : forall C0 i t,
      nth_rel i (C0 :: bs) t <-> nth_rel i (C0 :: bs') t).
    { intros C0 [| i] t0; simpl; [apply iff_refl | apply Hag]. }
    split.
    + intros [Hsn [Hsh Hm]]. split; [exact Hsn | split; [exact Hsh |]].
      intros b Hm0 C0 HC.
      apply (proj1 (IHT0 xi (C0 :: bs) (C0 :: bs') (Hag' C0) b)).
      exact (Hm b Hm0 C0 HC).
    + intros [Hsn [Hsh Hm]]. split; [exact Hsn | split; [exact Hsh |]].
      intros b Hm0 C0 HC.
      apply (proj2 (IHT0 xi (C0 :: bs) (C0 :: bs') (Hag' C0) b)).
      exact (Hm b Hm0 C0 HC).
  - reflexivity.
Qed.

Lemma R_stack_ind : forall T k, lc_ty_at k T -> forall xi bs bs',
  (forall i, i < k -> forall t, nth_rel i bs t <-> nth_rel i bs' t) ->
  forall t, R T xi bs t <-> R T xi bs' t.
Proof.
  induction T as [n | a | T1 IHT1 T2 IHT2 | T0 IHT0 | ]; intros k Hlc xi bs bs' Hag t; simpl in *.
  - inversion Hlc; subst. apply Hag. lia.
  - reflexivity.
  - inversion Hlc as [k0 i Hi | k0 X | k0 U1 U2 H1 H2 | k0 U H | k0]; subst.
    split.
    + intros [Hsn [Hsh Hm]]. split; [exact Hsn | split; [exact Hsh |]].
      intros T0 b Hm0 v Hv HR1.
      apply (proj1 (IHT2 k H2 xi bs bs' Hag (open_tm b v))).
      exact (Hm T0 b Hm0 v Hv (proj2 (IHT1 k H1 xi bs bs' Hag v) HR1)).
    + intros [Hsn [Hsh Hm]]. split; [exact Hsn | split; [exact Hsh |]].
      intros T0 b Hm0 v Hv HR1.
      apply (proj2 (IHT2 k H2 xi bs bs' Hag (open_tm b v))).
      exact (Hm T0 b Hm0 v Hv (proj1 (IHT1 k H1 xi bs bs' Hag v) HR1)).
  - inversion Hlc as [k0 i Hi | k0 X | k0 U1 U2 H1 H2 | k0 U H | k0]; subst.
    assert (Hag' : forall C0 i, i < S k -> forall t,
      nth_rel i (C0 :: bs) t <-> nth_rel i (C0 :: bs') t).
    { intros C0 [| i] Hi t0; simpl; [apply iff_refl | apply Hag; lia]. }
    split.
    + intros [Hsn [Hsh Hm]]. split; [exact Hsn | split; [exact Hsh |]].
      intros b Hm0 C0 HC.
      apply (proj1 (IHT0 (S k) H xi (C0 :: bs) (C0 :: bs') (Hag' C0) b)).
      exact (Hm b Hm0 C0 HC).
    + intros [Hsn [Hsh Hm]]. split; [exact Hsn | split; [exact Hsh |]].
      intros b Hm0 C0 HC.
      apply (proj2 (IHT0 (S k) H xi (C0 :: bs) (C0 :: bs') (Hag' C0) b)).
      exact (Hm b Hm0 C0 HC).
  - reflexivity.
Qed.

(* --------------------------------------------------------------------- *)
(* Opening a type variable in the relation.                              *)
(* --------------------------------------------------------------------- *)

Lemma R_open_ty : forall T k U xi bs t,
  lc_ty_at (S k) T ->
  locally_closed_ty U ->
  R (open_ty_rec k U T) xi bs t
  <-> R T xi (insert_rel k (fun s => R U xi bs s) bs) t.
Proof.
  induction T as [n | a | T1 IHT1 T2 IHT2 | T0 IHT0 | ];
    intros k U xi bs t Hlc HU; simpl in *.
  - (* Ty_BVar *) inversion Hlc as [k0 i Hi | k0 X | k0 U1 U2 H1 H2 | k0 U0 H0 | k0]; subst.
    destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst.
      rewrite nth_rel_insert_eq. apply R_erase_eq.
    + apply Nat.eqb_neq in E.
      rewrite nth_rel_insert_lt; [reflexivity | lia].
  - (* Ty_FVar *) reflexivity.
  - (* Ty_Arrow *) inversion Hlc as [k0 i Hi | k0 X | k0 U1 U2 H1 H2 | k0 U0 H0 | k0]; subst.
    split.
    + intros [Hsn [Hsh Hm]]. split; [exact Hsn | split; [exact Hsh |]].
      intros T0 b Hm0 v Hv HR1.
      apply (proj1 (IHT2 k U xi bs (open_tm b v) H2 HU)).
      exact (Hm T0 b Hm0 v Hv (proj2 (IHT1 k U xi bs v H1 HU) HR1)).
    + intros [Hsn [Hsh Hm]]. split; [exact Hsn | split; [exact Hsh |]].
      intros T0 b Hm0 v Hv HR1.
      apply (proj2 (IHT2 k U xi bs (open_tm b v) H2 HU)).
      exact (Hm T0 b Hm0 v Hv (proj1 (IHT1 k U xi bs v H1 HU) HR1)).
  - (* Ty_All *) inversion Hlc as [k0 i Hi | k0 X | k0 U1 U2 H1 H2 | k0 U0 H0 | k0]; subst.
    assert (Heq : forall C0 s, R U xi (C0 :: bs) s -> R U xi bs s).
    { intros C0 s HRU. apply (proj1 (R_stack_ind U 0 HU xi (C0 :: bs) bs
        (fun i Hi => ltac:(lia)) s)). exact HRU. }
    assert (Heq' : forall C0 s, R U xi bs s -> R U xi (C0 :: bs) s).
    { intros C0 s HRU. apply (proj2 (R_stack_ind U 0 HU xi (C0 :: bs) bs
        (fun i Hi => ltac:(lia)) s)). exact HRU. }
    split.
    + intros [Hsn [Hsh Hm]]. split; [exact Hsn | split; [exact Hsh |]].
      intros b Hm0 C0 HC.
      assert (Hagree : forall i t0,
        nth_rel i (C0 :: insert_rel k (fun s => R U xi (C0 :: bs) s) bs) t0
        <-> nth_rel i (C0 :: insert_rel k (fun s => R U xi bs s) bs) t0).
      { intros [| i] t0; simpl.
        - apply iff_refl.
        - apply (insert_rel_ext_same k
            (fun s => R U xi (C0 :: bs) s) (fun s => R U xi bs s) bs
            ltac:(intros s; split; [apply (Heq C0) | apply (Heq' C0)]) i t0). }
      apply (proj1 (R_stack_congr T0 xi
        (C0 :: insert_rel k (fun s => R U xi (C0 :: bs) s) bs)
        (C0 :: insert_rel k (fun s => R U xi bs s) bs) Hagree b)).
      apply (proj1 (IHT0 (S k) U xi (C0 :: bs) b H0 HU)).
      apply (Hm b Hm0 C0 HC).
    + intros [Hsn [Hsh Hm]]. split; [exact Hsn | split; [exact Hsh |]].
      intros b Hm0 C0 HC.
      assert (Hagree : forall i t0,
        nth_rel i (C0 :: insert_rel k (fun s => R U xi (C0 :: bs) s) bs) t0
        <-> nth_rel i (C0 :: insert_rel k (fun s => R U xi bs s) bs) t0).
      { intros [| i] t0; simpl.
        - apply iff_refl.
        - apply (insert_rel_ext_same k
            (fun s => R U xi (C0 :: bs) s) (fun s => R U xi bs s) bs
            ltac:(intros s; split; [apply (Heq C0) | apply (Heq' C0)]) i t0). }
      apply (proj2 (IHT0 (S k) U xi (C0 :: bs) b H0 HU)).
      apply (proj2 (R_stack_congr T0 xi
        (C0 :: insert_rel k (fun s => R U xi (C0 :: bs) s) bs)
        (C0 :: insert_rel k (fun s => R U xi bs s) bs) Hagree b)).
      apply (Hm b Hm0 C0 HC).
  - (* Ty_Nat *) reflexivity.
Qed.

(* --------------------------------------------------------------------- *)
(* Characterizations of the possible steps of compound terms.            *)
(* --------------------------------------------------------------------- *)

Lemma step_app_inv : forall a b t',
  step (tm_app a b) t' ->
  (exists T body v, a = tm_abs T body /\ b = v /\ value v /\ t' = open_tm body v)
  \/ (exists a', step a a' /\ t' = tm_app a' b)
  \/ (value a /\ exists b', step b b' /\ t' = tm_app a b').
Proof.
  intros a b t' H. inversion H as
    [T0 t0 v Hlc0 Hv0
    | t1 t1' t2 Hstep1 Hlc1
    | v1 t2 t2' Hv2 Hstep2
    | t0 T0 Hlc3 Hlcty3
    | t0 t'0 T0 Hstep4 Hlcty4
    | t0 t'0 Hstep5
    | n0 n' b0 s0 Hstep6 Hlcb6 Hlcs6
    | n0 b0 b' s0 Hnum7 Hstep7 Hlcs7
    | n0 b0 s0 s' Hnum8 Hvb8 Hstep8
    | b0 s0 Hvb9 Hvs9
    | n0 b0 s0 Hnum10 Hvb10 Hvs10]; subst; try discriminate.
  - left. eexists T0, t0, b. repeat split; eauto.
  - right. left. eexists. split; eauto.
  - right. right. split; [exact Hv2 | eexists; split; eauto].
Qed.

Lemma step_tapp_inv : forall a T t',
  step (tm_tapp a T) t' ->
  (exists body, a = tm_tabs body /\ t' = open_tm_ty body T)
  \/ (exists a', step a a' /\ t' = tm_tapp a' T).
Proof.
  intros a T t' H. inversion H as
    [T0 t0 v Hlc0 Hv0
    | t1 t1' t2 Hstep1 Hlc1
    | v1 t2 t2' Hv2 Hstep2
    | t0 T0 Hlc3 Hlcty3
    | t0 t'0 T0 Hstep4 Hlcty4
    | t0 t'0 Hstep5
    | n0 n' b0 s0 Hstep6 Hlcb6 Hlcs6
    | n0 b0 b' s0 Hnum7 Hstep7 Hlcs7
    | n0 b0 s0 s' Hnum8 Hvb8 Hstep8
    | b0 s0 Hvb9 Hvs9
    | n0 b0 s0 Hnum10 Hvb10 Hvs10]; subst; try discriminate.
  - left. eexists. split; eauto.
  - right. eexists. split; eauto.
Qed.

Lemma step_natrec_inv : forall n b s t',
  step (tm_natrec n b s) t' ->
  (exists n', step n n' /\ t' = tm_natrec n' b s)
  \/ (numeric_value n /\ exists b', step b b' /\ t' = tm_natrec n b' s)
  \/ (numeric_value n /\ value b /\ exists s', step s s' /\ t' = tm_natrec n b s')
  \/ (n = tm_zero /\ value b /\ value s /\ t' = b)
  \/ (exists m, n = tm_succ m /\ numeric_value m /\ value b /\ value s /\
        t' = tm_app (tm_app s m) (tm_natrec m b s)).
Proof.
  intros n b s t' H. inversion H as
    [T0 t0 v Hlc0 Hv0
    | t1 t1' t2 Hstep1 Hlc1
    | v1 t2 t2' Hv2 Hstep2
    | t0 T0 Hlc3 Hlcty3
    | t0 t'0 T0 Hstep4 Hlcty4
    | t0 t'0 Hstep5
    | n0 n' b0 s0 Hstep6 Hlcb6 Hlcs6
    | n0 b0 b' s0 Hnum7 Hstep7 Hlcs7
    | n0 b0 s0 s' Hnum8 Hvb8 Hstep8
    | b0 s0 Hvb9 Hvs9
    | n0 b0 s0 Hnum10 Hvb10 Hvs10]; subst; try discriminate.
  - left. eexists. split; eauto.
  - right. left. split; [exact Hnum7 | eexists; split; eauto].
  - right. right. left. split; [exact Hnum8 | split; [exact Hvb8 | eexists; split; eauto]].
  - right. right. right. left. repeat split; eauto.
  - right. right. right. right. eexists. repeat split; eauto.
Qed.

(* --------------------------------------------------------------------- *)
(* Semantic lemmas for the term constructors.                            *)
(* --------------------------------------------------------------------- *)

Lemma SN_numeric : forall n, numeric_value n -> strongly_normalizing n.
Proof.
  intros n H. induction H as [| n Hn IH].
  - apply SN_zero.
  - apply SN_succ. exact IH.
Qed.

Lemma numeric_value_erase_eq : forall n, numeric_value n -> erase n = n.
Proof.
  intros n H. induction H as [| n Hn IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma R_nat_numeric : forall n xi bs, numeric_value n -> R Ty_Nat xi bs n.
Proof.
  intros n xi bs Hn. simpl. rewrite (numeric_value_erase_eq n Hn).
  apply SN_numeric. exact Hn.
Qed.

Lemma R_abs : forall T1 T2 xi bs b,
  erase b = b ->
  (forall v, value v -> R T1 xi bs v -> R T2 xi bs (open_tm b v)) ->
  R (Ty_Arrow T1 T2) xi bs (tm_abs Ty_Nat b).
Proof.
  intros T1 T2 xi bs b Eb Hbeta. simpl. rewrite Eb.
  split.
  - apply SN_abs.
  - split.
    + intros v Hm Hv. exists Ty_Nat, b.
      exact (multi_abs_inv Ty_Nat b v Hm).
    + intros T0 b0 Hm v Hv HR1.
      assert (Heq : tm_abs T0 b0 = tm_abs Ty_Nat b) by (exact (multi_abs_inv Ty_Nat b (tm_abs T0 b0) Hm)).
      injection Heq as HT Hb. subst.
      apply Hbeta; assumption.
Qed.

Lemma R_tabs : forall T xi bs b,
  erase b = b ->
  (forall C, cand C -> R T xi (C :: bs) b) ->
  R (Ty_All T) xi bs (tm_tabs b).
Proof.
  intros T xi bs b Eb Hclause. simpl. rewrite Eb.
  split.
  - apply SN_tabs.
  - split.
    + intros v Hm Hv. exists b.
      exact (multi_tabs_inv b v Hm).
    + intros b0 Hm C HC.
      assert (Heq : tm_tabs b0 = tm_tabs b) by (exact (multi_tabs_inv b (tm_tabs b0) Hm)).
      injection Heq as Hb. subst.
      apply Hclause; exact HC.
Qed.

Lemma R_app : forall T1 T2 xi bs e1 e2,
  erase e1 = e1 -> erase e2 = e2 ->
  cand_xi xi -> cand_stack bs ->
  R (Ty_Arrow T1 T2) xi bs e1 -> R T1 xi bs e2 ->
  R T2 xi bs (tm_app e1 e2).
Proof.
  intros T1 T2 xi bs e1 e2 E1 E2 Hxi Hbs HR1 HR2.
  assert (Hsn1 : strongly_normalizing e1).
  { pose proof (R_sn (Ty_Arrow T1 T2) xi bs e1 (fun X _ => Hxi X) Hbs HR1) as H.
    rewrite E1 in H. exact H. }
  assert (Hsn2 : strongly_normalizing e2).
  { pose proof (R_sn T1 xi bs e2 (fun X _ => Hxi X) Hbs HR2) as H.
    rewrite E2 in H. exact H. }
  assert (Hmain : forall a, strongly_normalizing a ->
      forall b, strongly_normalizing b -> erase a = a -> erase b = b ->
      R (Ty_Arrow T1 T2) xi bs a -> R T1 xi bs b ->
      R T2 xi bs (tm_app a b)).
  { intros a HsnA. induction HsnA as [a Hreda IHa].
    intros b HsnB. induction HsnB as [b Hredb IHb].
    intros Ea Eb Ha Hb.
    assert (HstepR : forall t', step (tm_app a b) t' -> R T2 xi bs t').
    { intros t' Hst.
      destruct (step_app_inv a b t' Hst) as
        [[T0 [body [v [Ha_eq [Hb_eq [Hv Ht]]]]]] |
         [[a' [Hsta Ht]] | [Hva [b' [Hstb Ht]]]]].
      - subst a. subst b. subst t'.
        rewrite (R_erase_eq T2 xi bs (open_tm body v)).
        rewrite erase_open_tm.
        rewrite Eb.
        apply (proj2 (proj2 Ha) Ty_Nat (erase body)).
        + simpl. apply multi_refl.
        + exact Hv.
        + exact Hb.
      - subst t'.
        assert (Ea' : erase a' = a')
          by (apply (step_erase_id a a'); [exact Hsta | exact Ea]).
        assert (Hsta' : step (erase a) a') by (rewrite Ea; exact Hsta).
        assert (Ha' : R (Ty_Arrow T1 T2) xi bs a')
          by (apply (R_step (Ty_Arrow T1 T2) xi bs a a' (fun X _ => Hxi X) Hbs Ha); exact Hsta').
        exact (IHa a' Hsta b (SN_intro b Hredb) Ea' Eb Ha' Hb).
      - subst t'.
        assert (Eb' : erase b' = b')
          by (apply (step_erase_id b b'); [exact Hstb | exact Eb]).
        assert (Hstb' : step (erase b) b') by (rewrite Eb; exact Hstb).
        assert (Hb' : R T1 xi bs b')
          by (apply (R_step T1 xi bs b b' (fun X _ => Hxi X) Hbs Hb); exact Hstb').
        exact (IHb b' Hstb Ea Eb' Ha Hb').
    }
    assert (Eapp : erase (tm_app a b) = tm_app a b).
    { simpl. rewrite Ea, Eb. reflexivity. }
    assert (HsnApp : strongly_normalizing (tm_app a b)).
    { apply SN_intro. intros t' Hst.
      assert (Et' : erase t' = t')
        by (apply (step_erase_id (tm_app a b) t' Hst Eapp)).
      pose proof (R_sn T2 xi bs t' (fun X _ => Hxi X) Hbs (HstepR t' Hst)) as Hs.
      rewrite Et' in Hs. exact Hs. }
    apply (R_neutral T2 xi bs (tm_app a b) (fun X _ => Hxi X) Hbs).
    - rewrite Eapp. exact HsnApp.
    - rewrite Eapp. unfold neutral. intro Hvf. inversion Hvf.
    - intros t' Hst. rewrite Eapp in Hst.
      apply HstepR. exact Hst.
  }
  exact (Hmain e1 Hsn1 e2 Hsn2 E1 E2 HR1 HR2).
Qed.

Lemma R_tapp : forall T U xi bs e,
  erase e = e ->
  cand_xi xi -> cand_stack bs ->
  lc_ty_at 1 T -> locally_closed_ty U ->
  R (Ty_All T) xi bs e ->
  R (open_ty T U) xi bs (tm_tapp e U).
Proof.
  intros T U xi bs e Ee Hxi Hbs Hlc HU Hall.
  rewrite (R_open_ty T 0 U xi bs (tm_tapp e U) Hlc HU).
  change (R T xi ((fun s => R U xi bs s) :: bs) (tm_tapp e U)).
  assert (HcandD : cand (fun s => R U xi bs s)).
  { apply (cand_R U xi bs (fun X _ => Hxi X) Hbs). }
  assert (HcandStack : cand_stack ((fun s => R U xi bs s) :: bs)).
  { apply cand_stack_cons. split; [exact HcandD | exact Hbs]. }
  assert (Hsn : strongly_normalizing e).
  { pose proof (R_sn (Ty_All T) xi bs e (fun X _ => Hxi X) Hbs Hall) as H.
    rewrite Ee in H. exact H. }
  assert (Hmain : forall a, strongly_normalizing a -> erase a = a ->
      R (Ty_All T) xi bs a ->
      R T xi ((fun s => R U xi bs s) :: bs) (tm_tapp a U)).
  { intros a HsnA. induction HsnA as [a Hreda IHa].
    intros Ea HallA.
    assert (HstepR : forall t', step (tm_tapp a Ty_Nat) t' ->
        R T xi ((fun s => R U xi bs s) :: bs) t').
    { intros t' Hst.
      destruct (step_tapp_inv a Ty_Nat t' Hst) as [[body [Ha_eq Ht]] | [a' [Hsta Ht]]].
      - subst a. subst t'.
        assert (Eb : erase body = body).
        { simpl in Ea. injection Ea as Eb. exact Eb. }
        unfold open_tm_ty.
        rewrite (open_tm_ty_erased body Eb 0 Ty_Nat).
        apply (proj2 (proj2 HallA) body).
        + simpl. rewrite Eb. apply multi_refl.
        + exact HcandD.
      - subst t'.
        assert (Ea' : erase a' = a')
          by (apply (step_erase_id a a'); [exact Hsta | exact Ea]).
        assert (Hsta' : step (erase a) a') by (rewrite Ea; exact Hsta).
        assert (Hall' : R (Ty_All T) xi bs a')
          by (apply (R_step (Ty_All T) xi bs a a' (fun X _ => Hxi X) Hbs HallA); exact Hsta').
        pose proof (IHa a' Hsta Ea' Hall') as Hrec.
        assert (He : erase (tm_tapp a' U) = erase (tm_tapp a' Ty_Nat))
          by (simpl; reflexivity).
        exact (proj1 (R_erase_congr T xi ((fun s => R U xi bs s) :: bs)
          (tm_tapp a' U) (tm_tapp a' Ty_Nat) He) Hrec).
    }
    assert (Eapp : erase (tm_tapp a U) = tm_tapp a Ty_Nat).
    { simpl. rewrite Ea. reflexivity. }
    assert (EappNat : erase (tm_tapp a Ty_Nat) = tm_tapp a Ty_Nat).
    { simpl. rewrite Ea. reflexivity. }
    assert (HsnApp : strongly_normalizing (tm_tapp a Ty_Nat)).
    { apply SN_intro. intros t' Hst.
      assert (Et' : erase t' = t')
        by (apply (step_erase_id (tm_tapp a Ty_Nat) t' Hst EappNat)).
      pose proof (R_sn T xi ((fun s => R U xi bs s) :: bs) t'
        (fun X _ => Hxi X) HcandStack (HstepR t' Hst)) as Hs.
      rewrite Et' in Hs. exact Hs. }
    apply (R_neutral T xi ((fun s => R U xi bs s) :: bs) (tm_tapp a U)
      (fun X _ => Hxi X)).
    - exact HcandStack.
    - rewrite Eapp. exact HsnApp.
    - rewrite Eapp. unfold neutral. intro Hvf. inversion Hvf.
    - intros t' Hst. rewrite Eapp in Hst. apply HstepR. exact Hst.
  }
  exact (Hmain e Hsn Ee Hall).
Qed.

Lemma numeric_value_dec : forall n, {numeric_value n} + {~ numeric_value n}.
Proof.
  intro n. induction n.
  - right. intro H; inversion H.
  - right. intro H; inversion H.
  - right. intro H; inversion H.
  - right. intro H; inversion H.
  - right. intro H; inversion H.
  - right. intro H; inversion H.
  - left. constructor.
  - destruct IHn as [H | H].
    + left. constructor. assumption.
    + right. intro H'. inversion H'. contradiction.
  - right. intro H; inversion H.
Qed.

Lemma R_natrec_num : forall n, numeric_value n ->
  forall b, strongly_normalizing b ->
  forall s, strongly_normalizing s ->
  forall T xi bs,
  erase b = b -> erase s = s ->
  cand_xi xi -> cand_stack bs ->
  R T xi bs b -> R (Ty_Arrow Ty_Nat (Ty_Arrow T T)) xi bs s ->
  R T xi bs (tm_natrec n b s).
Proof.
  intros n Hn. induction Hn as [| m Hm IHm].
  - (* n = zero *)
    intros b Hsnb. induction Hsnb as [b Hredb IHb].
    intros s Hsns. induction Hsns as [s Hreds IHs].
    intros T xi bs Eb Es Hxi Hbs HRb HRs.
    assert (En : erase tm_zero = tm_zero) by reflexivity.
    assert (Enat : erase (tm_natrec tm_zero b s) = tm_natrec tm_zero b s).
    { simpl. rewrite Eb, Es. reflexivity. }
    assert (HstepR : forall t', step (tm_natrec tm_zero b s) t' -> R T xi bs t').
    { intros t' Hst.
      destruct (step_natrec_inv tm_zero b s t' Hst) as
        [[n' [Hstn Ht]] |
         [[Hnum [b' [Hstb Ht]]] |
          [[Hnum [Hvb [s' [Hsts Ht]]]] |
           [[Hnz [Hvb [Hvs Ht]]] |
            [m' [Hns [Hnum [Hvb [Hvs Ht]]]]]]]]].
      - subst t'. exfalso. exact (numeric_no_step tm_zero nv_zero n' Hstn).
      - subst t'.
        assert (Eb' : erase b' = b')
          by (apply (step_erase_id b b'); [exact Hstb | exact Eb]).
        assert (Hstb' : step (erase b) b') by (rewrite Eb; exact Hstb).
        assert (HRb' : R T xi bs b')
          by (apply (R_step T xi bs b b' (fun X _ => Hxi X) Hbs HRb); exact Hstb').
        exact (IHb b' Hstb s (SN_intro s Hreds) T xi bs Eb' Es Hxi Hbs HRb' HRs).
      - subst t'.
        assert (Es' : erase s' = s')
          by (apply (step_erase_id s s'); [exact Hsts | exact Es]).
        assert (Hsts' : step (erase s) s') by (rewrite Es; exact Hsts).
        assert (HRs' : R (Ty_Arrow Ty_Nat (Ty_Arrow T T)) xi bs s')
          by (apply (R_step (Ty_Arrow Ty_Nat (Ty_Arrow T T)) xi bs s s'
                (fun X _ => Hxi X) Hbs HRs); exact Hsts').
        exact (IHs s' Hsts T xi bs Eb Es' Hxi Hbs HRb HRs').
      - subst t'.
        exact HRb.
      - subst t'. exfalso. discriminate Hns.
    }
    assert (HsnRec : strongly_normalizing (tm_natrec tm_zero b s)).
    { apply SN_intro. intros t' Hst.
      assert (Et' : erase t' = t')
        by (apply (step_erase_id (tm_natrec tm_zero b s) t' Hst Enat)).
      pose proof (R_sn T xi bs t' (fun X _ => Hxi X) Hbs (HstepR t' Hst)) as Hs.
      rewrite Et' in Hs. exact Hs. }
    apply (R_neutral T xi bs (tm_natrec tm_zero b s) (fun X _ => Hxi X) Hbs).
    + rewrite Enat. exact HsnRec.
    + rewrite Enat. unfold neutral. intro Hvf. inversion Hvf.
    + intros t' Hst. rewrite Enat in Hst. apply HstepR. exact Hst.
  - (* n = succ m *)
    intros b Hsnb. induction Hsnb as [b Hredb IHb].
    intros s Hsns. induction Hsns as [s Hreds IHs].
    intros T xi bs Eb Es Hxi Hbs HRb HRs.
    assert (Enm : erase m = m) by (apply numeric_value_erase_eq; exact Hm).
    assert (En : erase (tm_succ m) = tm_succ m) by (simpl; rewrite Enm; reflexivity).
    assert (Enat : erase (tm_natrec (tm_succ m) b s) = tm_natrec (tm_succ m) b s).
    { simpl. rewrite Enm, Eb, Es. reflexivity. }
    assert (HstepR : forall t', step (tm_natrec (tm_succ m) b s) t' -> R T xi bs t').
    { intros t' Hst.
      destruct (step_natrec_inv (tm_succ m) b s t' Hst) as
        [[n' [Hstn Ht]] |
         [[Hnum [b' [Hstb Ht]]] |
          [[Hnum [Hvb [s' [Hsts Ht]]]] |
           [[Hnz [Hvb [Hvs Ht]]] |
            [m' [Hns [Hnum [Hvb [Hvs Ht]]]]]]]]].
      - subst t'. exfalso. exact (numeric_no_step (tm_succ m) (nv_succ m Hm) n' Hstn).
      - subst t'.
        assert (Eb' : erase b' = b')
          by (apply (step_erase_id b b'); [exact Hstb | exact Eb]).
        assert (Hstb' : step (erase b) b') by (rewrite Eb; exact Hstb).
        assert (HRb' : R T xi bs b')
          by (apply (R_step T xi bs b b' (fun X _ => Hxi X) Hbs HRb); exact Hstb').
        exact (IHb b' Hstb s (SN_intro s Hreds) T xi bs Eb' Es Hxi Hbs HRb' HRs).
      - subst t'.
        assert (Es' : erase s' = s')
          by (apply (step_erase_id s s'); [exact Hsts | exact Es]).
        assert (Hsts' : step (erase s) s') by (rewrite Es; exact Hsts).
        assert (HRs' : R (Ty_Arrow Ty_Nat (Ty_Arrow T T)) xi bs s')
          by (apply (R_step (Ty_Arrow Ty_Nat (Ty_Arrow T T)) xi bs s s'
                (fun X _ => Hxi X) Hbs HRs); exact Hsts').
        exact (IHs s' Hsts T xi bs Eb Es' Hxi Hbs HRb HRs').
      - subst t'. exfalso. discriminate Hnz.
      - subst t'. injection Hns as Hmm. subst m'.
        assert (Hsm : R (Ty_Arrow T T) xi bs (tm_app s m)).
        { apply (R_app Ty_Nat (Ty_Arrow T T) xi bs s m Es Enm Hxi Hbs HRs).
          apply R_nat_numeric. exact Hm. }
        assert (HrecM : R T xi bs (tm_natrec m b s)).
        { apply (IHm b (SN_intro b Hredb) s (SN_intro s Hreds)
            T xi bs Eb Es Hxi Hbs HRb HRs). }
        assert (Eapp1 : erase (tm_app s m) = tm_app s m).
        { simpl. rewrite Es, Enm. reflexivity. }
        assert (ErecM : erase (tm_natrec m b s) = tm_natrec m b s).
        { simpl. rewrite Enm, Eb, Es. reflexivity. }
        exact (R_app T T xi bs (tm_app s m) (tm_natrec m b s)
          Eapp1 ErecM Hxi Hbs Hsm HrecM).
    }
    assert (HsnRec : strongly_normalizing (tm_natrec (tm_succ m) b s)).
    { apply SN_intro. intros t' Hst.
      assert (Et' : erase t' = t')
        by (apply (step_erase_id (tm_natrec (tm_succ m) b s) t' Hst Enat)).
      pose proof (R_sn T xi bs t' (fun X _ => Hxi X) Hbs (HstepR t' Hst)) as Hs.
      rewrite Et' in Hs. exact Hs. }
    apply (R_neutral T xi bs (tm_natrec (tm_succ m) b s) (fun X _ => Hxi X) Hbs).
    + rewrite Enat. exact HsnRec.
    + rewrite Enat. unfold neutral. intro Hvf. inversion Hvf.
    + intros t' Hst. rewrite Enat in Hst. apply HstepR. exact Hst.
Qed.

Lemma R_natrec_gen : forall n,
  strongly_normalizing n ->
  forall b s T xi bs,
  erase n = n -> erase b = b -> erase s = s ->
  cand_xi xi -> cand_stack bs ->
  R Ty_Nat xi bs n -> R T xi bs b ->
  R (Ty_Arrow Ty_Nat (Ty_Arrow T T)) xi bs s ->
  R T xi bs (tm_natrec n b s).
Proof.
  intros n Hsn. induction Hsn as [n Hredn IHn].
  intros b s T xi bs En Eb Es Hxi Hbs HRn HRb HRs.
  assert (HsnB : strongly_normalizing b).
  { pose proof (R_sn T xi bs b (fun X _ => Hxi X) Hbs HRb) as H.
    rewrite Eb in H. exact H. }
  assert (HsnS : strongly_normalizing s).
  { pose proof (R_sn (Ty_Arrow Ty_Nat (Ty_Arrow T T)) xi bs s
      (fun X _ => Hxi X) Hbs HRs) as H.
    rewrite Es in H. exact H. }
  destruct (numeric_value_dec n) as [Hnum | Hnn].
  - apply (R_natrec_num n Hnum b HsnB s HsnS T xi bs Eb Es Hxi Hbs HRb HRs).
  - assert (Enat : erase (tm_natrec n b s) = tm_natrec n b s).
    { simpl. rewrite En, Eb, Es. reflexivity. }
    assert (HstepR : forall t', step (tm_natrec n b s) t' -> R T xi bs t').
    { intros t' Hst.
      destruct (step_natrec_inv n b s t' Hst) as
        [[n' [Hstn Ht]] |
         [[Hnum1 [b' [Hstb Ht]]] |
          [[Hnum2 [Hvb [s' [Hsts Ht]]]] |
           [[Hnz [Hvb [Hvs Ht]]] |
            [m' [Hns [Hnum3 [Hvb [Hvs Ht]]]]]]]]].
      - subst t'.
        assert (En' : erase n' = n')
          by (apply (step_erase_id n n'); [exact Hstn | exact En]).
        assert (Hstn' : step (erase n) n') by (rewrite En; exact Hstn).
        assert (HRn' : R Ty_Nat xi bs n')
          by (apply (R_step Ty_Nat xi bs n n' (fun X _ => Hxi X) Hbs HRn); exact Hstn').
        destruct (numeric_value_dec n') as [HnumN' | HnnN'].
        + apply (R_natrec_num n' HnumN' b HsnB s HsnS T xi bs Eb Es Hxi Hbs HRb HRs).
        + apply (IHn n' Hstn b s T xi bs En' Eb Es Hxi Hbs HRn' HRb HRs).
      - subst t'. exfalso. apply Hnn. exact Hnum1.
      - subst t'. exfalso. apply Hnn. exact Hnum2.
      - subst t'. exfalso. apply Hnn. rewrite Hnz. constructor.
      - subst t'. exfalso. apply Hnn. rewrite Hns. apply nv_succ. exact Hnum3.
    }
    assert (HsnRec : strongly_normalizing (tm_natrec n b s)).
    { apply SN_intro. intros t' Hst.
      assert (Et' : erase t' = t')
        by (apply (step_erase_id (tm_natrec n b s) t' Hst Enat)).
      pose proof (R_sn T xi bs t' (fun X _ => Hxi X) Hbs (HstepR t' Hst)) as Hs.
      rewrite Et' in Hs. exact Hs. }
    apply (R_neutral T xi bs (tm_natrec n b s) (fun X _ => Hxi X) Hbs).
    + rewrite Enat. exact HsnRec.
    + rewrite Enat. unfold neutral. intro Hvf. inversion Hvf.
    + intros t' Hst. rewrite Enat in Hst. apply HstepR. exact Hst.
Qed.

(* ===================================================================== *)
(* Syntactic lemmas for the fundamental theorem.                         *)
(* ===================================================================== *)

Lemma subst_tm_open_rec : forall (sigma : atom -> tm) t u,
  (forall x, locally_closed_tm (sigma x)) ->
  forall k, subst_tm sigma (open_tm_rec k u t) =
            open_tm_rec k (subst_tm sigma u) (subst_tm sigma t).
Proof.
  intros sigma t. induction t; intros u Hlc k; simpl; try reflexivity;
    try (f_equal; auto).
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. apply lc_open_id. apply Hlc.
Qed.

Lemma subst_tm_open : forall (sigma : atom -> tm) t u,
  (forall x, locally_closed_tm (sigma x)) ->
  subst_tm sigma (open_tm t u) =
  open_tm (subst_tm sigma t) (subst_tm sigma u).
Proof. intros; unfold open_tm; apply subst_tm_open_rec; assumption. Qed.

Lemma lc_tm_open_inv : forall K k u t,
  lc_tm_at K k (open_tm_rec k u t) -> lc_tm_at K (S k) t.
Proof.
  intros K k u t. revert K k u.
  induction t as [n | a | T0 t0 IH0 | t1 IH1 t2 IH2 | t0 IH0 | t0 IH0 T0 | | t0 IH0 | t1 IH1 t2 IH2 t3 IH3];
    intros K k u H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. apply lc_tm_bvar. lia.
    + inversion H; subst. apply lc_tm_bvar. lia.
  - constructor.
  - inversion H; subst. apply lc_tm_abs.
    + assumption.
    + apply IH0 with (k:=S k) (u:=u). assumption.
  - inversion H; subst. apply lc_tm_app;
      [apply IH1 with (k:=k) (u:=u) | apply IH2 with (k:=k) (u:=u)]; assumption.
  - inversion H; subst. apply lc_tm_tabs.
    apply IH0 with (K:=S K) (k:=k) (u:=u). assumption.
  - inversion H; subst. apply lc_tm_tapp.
    + apply IH0 with (k:=k) (u:=u). assumption.
    + assumption.
  - constructor.
  - inversion H; subst. apply lc_tm_succ. apply IH0 with (k:=k) (u:=u). assumption.
  - inversion H; subst. apply lc_tm_rec.
    + apply IH1 with (k:=k) (u:=u). assumption.
    + apply IH2 with (k:=k) (u:=u). assumption.
    + apply IH3 with (k:=k) (u:=u). assumption.
Qed.

Lemma lc_tm_open_ty_inv : forall K k t U,
  lc_tm_at K k (open_tm_ty_rec K U t) -> lc_tm_at (S K) k t.
Proof.
  intros K k t U. revert K k U.
  induction t as [n | a | T0 t0 IH0 | t1 IH1 t2 IH2 | t0 IH0 | t0 IH0 T0 | | t0 IH0 | t1 IH1 t2 IH2 t3 IH3];
    intros K k U H; simpl in H.
  - apply lc_tm_mono with (K:=K) (k:=k); [assumption | lia | lia].
  - constructor.
  - inversion H; subst. apply lc_tm_abs.
    + apply (lc_ty_open_rec_inv K T0 U). assumption.
    + apply IH0 with (U:=U). assumption.
  - inversion H; subst. apply lc_tm_app.
    + apply IH1 with (U:=U). assumption.
    + apply IH2 with (U:=U). assumption.
  - inversion H; subst. apply lc_tm_tabs.
    apply IH0 with (K:=S K) (U:=U). assumption.
  - inversion H; subst. apply lc_tm_tapp.
    + apply IH0 with (U:=U). assumption.
    + apply (lc_ty_open_rec_inv K T0 U). assumption.
  - constructor.
  - inversion H; subst. apply lc_tm_succ. apply IH0 with (U:=U). assumption.
  - inversion H; subst. apply lc_tm_rec.
    + apply IH1 with (U:=U). assumption.
    + apply IH2 with (U:=U). assumption.
    + apply IH3 with (U:=U). assumption.
Qed.

Lemma lc_subst_tm : forall K k t,
  lc_tm_at K k t ->
  forall (sigma : atom -> tm),
  (forall x, locally_closed_tm (sigma x)) ->
  lc_tm_at K k (subst_tm sigma t).
Proof.
  intros K k t. revert K k.
  induction t as [n | a | T0 t0 IH0 | t1 IH1 t2 IH2 | t0 IH0 | t0 IH0 T0 | | t0 IH0 | t1 IH1 t2 IH2 t3 IH3];
    intros K k H sigma Hlc; simpl.
  - inversion H; subst. constructor. assumption.
  - apply lc_tm_mono with (K:=0) (k:=0); [apply Hlc | lia | lia].
  - inversion H; subst. apply lc_tm_abs.
    + assumption.
    + apply IH0 with (K:=K) (k:=S k); assumption.
  - inversion H; subst. apply lc_tm_app.
    + apply IH1 with (K:=K) (k:=k); assumption.
    + apply IH2 with (K:=K) (k:=k); assumption.
  - inversion H; subst. apply lc_tm_tabs.
    apply IH0 with (K:=S K) (k:=k); assumption.
  - inversion H; subst. apply lc_tm_tapp.
    + apply IH0 with (K:=K) (k:=k); assumption.
    + assumption.
  - constructor.
  - inversion H; subst. apply lc_tm_succ. apply IH0 with (K:=K) (k:=k); assumption.
  - inversion H; subst. apply lc_tm_rec.
    + apply IH1 with (K:=K) (k:=k); assumption.
    + apply IH2 with (K:=K) (k:=k); assumption.
    + apply IH3 with (K:=K) (k:=k); assumption.
Qed.

Lemma wf_lc_ty : forall Delta T, wf_ty Delta T -> lc_ty_at 0 T.
Proof.
  intros Delta T H. induction H as
    [Delta X Hin | Delta T1 T2 H1 IH1 H2 IH2 | L Delta T Hbody IHbody | Delta].
  - constructor.
  - apply lc_ty_arrow; assumption.
  - apply lc_ty_all. apply lc_ty_open_rec_inv with (U:=Ty_FVar (fresh L)).
    apply (IHbody (fresh L) (fresh_notin L)).
  - constructor.
Qed.

Lemma has_type_lc_ty : forall Delta Gamma t T,
  has_type Delta Gamma t T -> lc_ty_at 0 T.
Proof.
  intros Delta Gamma t T H. induction H as
    [Delta Gamma x T Hlookup Hwf
    | L Delta Gamma T1 t2 T2 Hwf Hbody IHbody
    | Delta Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
    | L Delta Gamma t T Hbody IHbody
    | Delta Gamma t T U H1 IH1 Hwf
    | Delta Gamma
    | Delta Gamma n H1 IH1
    | Delta Gamma n b s T Hn IHn Hb IHb Hs IHs].
  - exact (wf_lc_ty Delta T Hwf).
  - apply lc_ty_arrow.
    + exact (wf_lc_ty Delta T1 Hwf).
    + apply (IHbody (fresh L) (fresh_notin L)).
  - inversion IH1; subst. assumption.
  - apply lc_ty_all. apply lc_ty_open_rec_inv with (U:=Ty_FVar (fresh L)).
    apply (IHbody (fresh L) (fresh_notin L)).
  - inversion IH1; subst. apply lc_ty_open.
    + assumption.
    + exact (wf_lc_ty Delta U Hwf).
  - constructor.
  - constructor.
  - exact IHb.
Qed.

Lemma has_type_lc_tm : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T H. induction H as
    [Delta Gamma x T Hlookup Hwf
    | L Delta Gamma T1 t2 T2 Hwf Hbody IHbody
    | Delta Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
    | L Delta Gamma t T Hbody IHbody
    | Delta Gamma t T U H1 IH1 Hwf
    | Delta Gamma
    | Delta Gamma n H1 IH1
    | Delta Gamma n b s T Hn IHn Hb IHb Hs IHs].
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + exact (wf_lc_ty Delta T1 Hwf).
    + apply (lc_tm_open_inv 0 0 (tm_fvar (fresh L)) t2).
      apply (IHbody (fresh L) (fresh_notin L)).
  - apply lc_tm_app; assumption.
  - apply lc_tm_tabs.
    apply (lc_tm_open_ty_inv 0 0 t (Ty_FVar (fresh L))).
    apply (IHbody (fresh L) (fresh_notin L)).
  - apply lc_tm_tapp.
    + assumption.
    + exact (wf_lc_ty Delta U Hwf).
  - apply lc_tm_zero.
  - apply lc_tm_succ. assumption.
  - apply lc_tm_rec; assumption.
Qed.

(* Free type variables of a context. *)
Definition fv_context (Gamma : context) : list atom :=
  flat_map (fun p => fv_ty (snd p)) Gamma.

Lemma lookup_context_in_map : forall x Gamma Ty,
  lookup_context x Gamma = Some Ty -> In Ty (map snd Gamma).
Proof.
  intros x Gamma. induction Gamma as [| [y T] Gamma IH]; intros Ty H.
  - simpl in H. discriminate.
  - simpl in H. destruct (Nat.eqb x y) eqn:E.
    + injection H as HT. subst. left. reflexivity.
    + right. apply IH. exact H.
Qed.

Lemma In_fv_context : forall Gamma X,
  In X (fv_context Gamma) <-> exists Ty, In Ty (map snd Gamma) /\ In X (fv_ty Ty).
Proof.
  intros Gamma. induction Gamma as [| [y T] Gamma IH]; intros X.
  - simpl. split.
    + intros [].
    + intros [Ty [Hin _]]. simpl in Hin. contradiction.
  - simpl. split.
    + intros H. apply in_app_iff in H. destruct H as [H | H].
      * exists T. split; [left; reflexivity | exact H].
      * apply IH in H. destruct H as [Ty [Hin Hfv]].
        exists Ty. split; [right; exact Hin | exact Hfv].
    + intros [Ty [[HTy | HTy] Hfv]].
      * subst Ty. apply in_app_iff. left. exact Hfv.
      * apply in_app_iff. right. apply (proj2 (IH X)).
        exists Ty. split; assumption.
Qed.

Lemma lc_ty_all_inv : forall k T, lc_ty_at k (Ty_All T) -> lc_ty_at (S k) T.
Proof. intros k T H; inversion H; subst; assumption. Qed.

Lemma SN_erase_fwd : forall t,
  strongly_normalizing (erase t) -> strongly_normalizing t.
Proof.
  intros t H. remember (erase t) as e eqn:E. revert t E.
  induction H as [e0 Hrede IHe].
  intros t E. apply SN_intro. intros t' Hst.
  pose proof (step_erase t t' Hst) as Hst'.
  subst e0.
  exact (IHe (erase t') Hst' t' eq_refl).
Qed.

Definition sem_ctx (Gamma : context) (xi : atom -> Rel) (bs : list Rel)
  (rho : atom -> tm) : Prop :=
  forall x T, lookup_context x Gamma = Some T -> R T xi bs (rho x).

Theorem fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall xi bs rho,
  cand_xi xi ->
  cand_stack bs ->
  (forall x, locally_closed_tm (rho x)) ->
  sem_ctx Gamma xi bs rho ->
  R T xi bs (subst_tm rho t).
Proof.
  intros Delta Gamma t T H. induction H as
    [D1 G1 x TV Hlookup Hwf
    | L1 D2 G2 T1 t2 T2 Hwf Hbody IHbody
    | D3 G3 t1 t2 T1b T2b H1 IH1 H2 IH2
    | L2 D4 G4 tt TT HbodyT IHbodyT
    | D5 G5 ta Ta Ua H1t IH1t Hwft
    | D6 G6
    | D7 G7 nn H1n IH1n
    | D8 G8 nn2 bb ss TT2 Hn IHn Hb IHb Hs IHs];
    intros xi bs rho Hxi Hbs Hlcr Hsem.
  - (* Var *) simpl. apply Hsem. exact Hlookup.
  - (* Abs *)
    assert (Hgoal : R (Ty_Arrow T1 T2) xi bs
        (tm_abs Ty_Nat (erase (subst_tm rho t2)))).
    { apply R_abs.
      - apply erase_idem.
      - intros v Hv HRv.
        set (x := fresh (L1 ++ fv_tm t2)).
        assert (HxL : ~ In x L1).
        { intro Hin. apply (fresh_notin (L1 ++ fv_tm t2)).
          apply in_app_iff. left. exact Hin. }
        assert (Hxfv : ~ In x (fv_tm t2)).
        { intro Hin. apply (fresh_notin (L1 ++ fv_tm t2)).
          apply in_app_iff. right. exact Hin. }
        set (rho' := extend_sigma x v rho).
        assert (Hlc' : forall y, locally_closed_tm (rho' y)).
        { intro y. unfold rho', extend_sigma.
          destruct (Nat.eqb y x); [apply value_lc; exact Hv | apply Hlcr]. }
        assert (Hsem' : sem_ctx (update G2 x T1) xi bs rho').
        { unfold sem_ctx. intros y Ty Hlook.
          unfold update in Hlook. simpl in Hlook.
          destruct (Nat.eqb y x) eqn:E.
          - apply Nat.eqb_eq in E. subst y. injection Hlook as HTy. subst Ty.
            unfold rho', extend_sigma. rewrite Nat.eqb_refl. exact HRv.
          - apply Nat.eqb_neq in E.
            unfold rho', extend_sigma.
            destruct (Nat.eqb y x) eqn:E2.
            + apply Nat.eqb_eq in E2. exfalso. exact (E E2).
            + apply Hsem. exact Hlook. }
        pose proof (IHbody x HxL xi bs rho' Hxi Hbs Hlc' Hsem') as Hres.
        assert (Heq : erase (subst_tm rho' (open_tm t2 (tm_fvar x))) =
                      erase (open_tm (erase (subst_tm rho t2)) v)).
        { rewrite erase_subst_tm.
          rewrite erase_open_tm.
          simpl.
          set (sig := fun y => erase (rho' y)).
          assert (Hsig : forall y, locally_closed_tm (sig y)).
          { intro y. unfold sig. apply lc_erase with (K:=0) (k:=0). apply Hlc'. }
          rewrite (subst_tm_open sig (erase t2) (tm_fvar x) Hsig).
          assert (Hsub : subst_tm sig (erase t2) =
                         subst_tm (fun y => erase (rho y)) (erase t2)).
          { apply subst_tm_ext. intros y Hy.
            assert (Hy' : In y (fv_tm t2))
              by (rewrite <- fv_erase; exact Hy).
            assert (Hyx : y <> x) by (intro E; subst; exact (Hxfv Hy')).
            unfold sig, rho', extend_sigma.
            destruct (Nat.eqb y x) eqn:E2; simpl.
            - apply Nat.eqb_eq in E2. exfalso. exact (Hyx E2).
            - reflexivity. }
          rewrite Hsub.
          rewrite <- erase_subst_tm.
          unfold sig, rho', extend_sigma. simpl.
          rewrite Nat.eqb_refl. simpl.
          rewrite erase_open_tm. rewrite erase_idem.
          reflexivity. }
        exact (proj1 (R_erase_congr T2 xi bs
          (subst_tm rho' (open_tm t2 (tm_fvar x)))
          (open_tm (erase (subst_tm rho t2)) v) Heq) Hres). }
    apply (proj2 (R_erase_eq (Ty_Arrow T1 T2) xi bs
      (tm_abs T1 (subst_tm rho t2)))).
    simpl. exact Hgoal.
  - (* App *)
    pose proof (IH1 xi bs rho Hxi Hbs Hlcr Hsem) as HR1.
    pose proof (IH2 xi bs rho Hxi Hbs Hlcr Hsem) as HR2.
    set (e1 := erase (subst_tm rho t1)).
    set (e2 := erase (subst_tm rho t2)).
    assert (He1 : erase e1 = e1) by (unfold e1; apply erase_idem).
    assert (He2 : erase e2 = e2) by (unfold e2; apply erase_idem).
    assert (HR1' : R (Ty_Arrow T1b T2b) xi bs e1).
    { unfold e1. apply (proj1 (R_erase_eq (Ty_Arrow T1b T2b) xi bs
        (subst_tm rho t1))). exact HR1. }
    assert (HR2' : R T1b xi bs e2).
    { unfold e2. apply (proj1 (R_erase_eq T1b xi bs
        (subst_tm rho t2))). exact HR2. }
    pose proof (R_app T1b T2b xi bs e1 e2 He1 He2 Hxi Hbs HR1' HR2') as Happ.
    apply (proj2 (R_erase_eq T2b xi bs
      (tm_app (subst_tm rho t1) (subst_tm rho t2)))).
    unfold e1, e2 in Happ. simpl. exact Happ.
  - (* TAbs *)
    assert (HlcT : lc_ty_at 1 TT).
    { apply lc_ty_open_rec_inv with (k:=0) (U:=Ty_FVar (fresh L2)).
      exact (has_type_lc_ty (fresh L2 :: D4) G4
        (open_tm_ty tt (Ty_FVar (fresh L2))) (open_ty TT (Ty_FVar (fresh L2)))
        (HbodyT (fresh L2) (fresh_notin L2))). }
    assert (Hgoal : R (Ty_All TT) xi bs (tm_tabs (erase (subst_tm rho tt)))).
    { apply R_tabs.
      - apply erase_idem.
      - intros C Hcand.
        set (X := fresh (L2 ++ fv_ty TT ++ fv_context G4)).
        assert (HXL : ~ In X L2).
        { intro Hin. apply (fresh_notin (L2 ++ fv_ty TT ++ fv_context G4)).
          apply in_app_iff. left. exact Hin. }
        assert (HXT : ~ In X (fv_ty TT)).
        { intro Hin. apply (fresh_notin (L2 ++ fv_ty TT ++ fv_context G4)).
          apply in_app_iff. right. apply in_app_iff. left. exact Hin. }
        assert (HXG : ~ In X (fv_context G4)).
        { intro Hin. apply (fresh_notin (L2 ++ fv_ty TT ++ fv_context G4)).
          apply in_app_iff. right. apply in_app_iff. right. exact Hin. }
        set (xi' := fun Y => if Nat.eqb Y X then C else xi Y).
        assert (Hcxi' : cand_xi xi').
        { intro Y. unfold xi'. destruct (Nat.eqb Y X); [exact Hcand | apply Hxi]. }
        assert (Hsem' : sem_ctx G4 xi' bs rho).
        { unfold sem_ctx. intros y Ty Hlook.
          assert (Hag : forall Z, In Z (fv_ty Ty) ->
              forall t, xi Z t <-> xi' Z t).
          { intros Z HZ t.
            assert (ZX : Z <> X).
            { intro E. subst Z. apply HXG.
              apply (proj2 (In_fv_context G4 X)).
              exists Ty. split; [apply lookup_context_in_map with (x:=y); exact Hlook | exact HZ]. }
            split; intro HRZ.
            + revert HRZ. unfold xi'. destruct (Nat.eqb Z X) eqn:E.
              * apply Nat.eqb_eq in E. exfalso. exact (ZX E).
              * intro HRZ. apply (proj1 (proj2 (proj2 (proj2 (Hxi Z))) t)). exact HRZ.
            + revert HRZ. unfold xi'. destruct (Nat.eqb Z X) eqn:E.
              * apply Nat.eqb_eq in E. exfalso. exact (ZX E).
              * intro HRZ. apply (proj2 (proj2 (proj2 (proj2 (Hxi Z))) t)). exact HRZ. }
          apply (proj1 (R_agree_xi Ty xi xi' bs Hag (rho y))).
          apply Hsem. exact Hlook. }
        pose proof (IHbodyT X HXL xi' bs rho Hcxi' Hbs Hlcr Hsem') as Hres.
        assert (Heq : erase (subst_tm rho (open_tm_ty tt (Ty_FVar X))) =
                      erase (subst_tm rho tt)).
        { rewrite !erase_subst_tm. rewrite erase_open_tm_ty. reflexivity. }
        assert (Hmid : R (open_ty TT (Ty_FVar X)) xi' bs (subst_tm rho tt)).
        { exact (proj1 (R_erase_congr (open_ty TT (Ty_FVar X)) xi' bs
            (subst_tm rho (open_tm_ty tt (Ty_FVar X))) (subst_tm rho tt) Heq) Hres). }
        assert (Hres' : R (open_ty TT (Ty_FVar X)) xi' bs (erase (subst_tm rho tt))).
        { apply (proj1 (R_erase_eq (open_ty TT (Ty_FVar X)) xi' bs (subst_tm rho tt))).
          exact Hmid. }
        pose proof (proj1 (R_open_ty TT 0 (Ty_FVar X) xi' bs (erase (subst_tm rho tt))
          HlcT (lc_ty_fvar 0 X)) Hres') as Hopen.
        change (R TT xi' ((fun s => R (Ty_FVar X) xi' bs s) :: bs)
          (erase (subst_tm rho tt))) in Hopen.
        assert (Hwrap : R TT xi' ((fun s => C (erase s)) :: bs) (erase (subst_tm rho tt))).
        { apply (proj1 (R_stack_congr TT xi'
            ((fun s => R (Ty_FVar X) xi' bs s) :: bs)
            ((fun s => C (erase s)) :: bs) _ (erase (subst_tm rho tt)))).
          intros [| i] s0; simpl.
          - unfold xi'. rewrite Nat.eqb_refl. reflexivity.
          - apply iff_refl. }
        assert (Hagree : forall i s0,
          nth_rel i ((fun s => C (erase s)) :: bs) s0 <->
          nth_rel i (C :: bs) s0).
        { intros [| i] s0; simpl.
          - split; intro HC.
            + apply (proj2 (proj2 (proj2 (proj2 Hcand)) s0)); exact HC.
            + apply (proj1 (proj2 (proj2 (proj2 Hcand)) s0)); exact HC.
          - apply iff_refl. }
        assert (Hwrap2 : R TT xi' (C :: bs) (erase (subst_tm rho tt))).
        { apply (proj1 (R_stack_congr TT xi'
            ((fun s => C (erase s)) :: bs) (C :: bs) Hagree
            (erase (subst_tm rho tt)))). exact Hwrap. }
        apply (proj1 (R_agree_xi TT xi' xi bs _ (erase (subst_tm rho tt)))).
        + intros Z HZ. split; intro HRZ.
          * unfold xi'. destruct (Nat.eqb Z X) eqn:E.
            -- apply Nat.eqb_eq in E. exfalso. apply HXT. subst. exact HZ.
            -- exact HRZ.
          * unfold xi'. destruct (Nat.eqb Z X) eqn:E.
            -- apply Nat.eqb_eq in E. exfalso. apply HXT. subst. exact HZ.
            -- exact HRZ.
        + exact Hwrap2. }
    apply (proj2 (R_erase_eq (Ty_All TT) xi bs (tm_tabs (subst_tm rho tt)))).
    simpl. exact Hgoal.
  - (* TApp *)
    pose proof (IH1t xi bs rho Hxi Hbs Hlcr Hsem) as Hall.
    assert (HlcT : lc_ty_at 1 Ta).
    { apply lc_ty_all_inv with (k:=0).
      exact (has_type_lc_ty D5 G5 ta (Ty_All Ta) H1t). }
    assert (HU : locally_closed_ty Ua) by (apply wf_lc_ty; exact Hwft).
    set (e := erase (subst_tm rho ta)).
    assert (He : erase e = e) by (unfold e; apply erase_idem).
    assert (Hall' : R (Ty_All Ta) xi bs e).
    { unfold e. apply (proj1 (R_erase_eq (Ty_All Ta) xi bs (subst_tm rho ta))). exact Hall. }
    pose proof (R_tapp Ta Ua xi bs e He Hxi Hbs HlcT HU Hall') as Htap.
    assert (HtapNat : R (open_ty Ta Ua) xi bs (tm_tapp e Ty_Nat)).
    { assert (Heq : erase (tm_tapp e Ua) = erase (tm_tapp e Ty_Nat))
        by (simpl; rewrite He; reflexivity).
      exact (proj1 (R_erase_congr (open_ty Ta Ua) xi bs
        (tm_tapp e Ua) (tm_tapp e Ty_Nat) Heq) Htap). }
    assert (Heq2 : erase (tm_tapp (subst_tm rho ta) Ua) =
                   erase (tm_tapp e Ty_Nat)).
    { unfold e. simpl. rewrite erase_idem. reflexivity. }
    exact (proj2 (R_erase_congr (open_ty Ta Ua) xi bs
      (tm_tapp (subst_tm rho ta) Ua) (tm_tapp e Ty_Nat) Heq2) HtapNat).
  - (* Zero *) simpl. apply SN_zero.
  - (* Succ *) simpl. apply SN_succ.
    exact (IH1n xi bs rho Hxi Hbs Hlcr Hsem).
  - (* Rec *)
    simpl.
    pose proof (IHn xi bs rho Hxi Hbs Hlcr Hsem) as HRn.
    pose proof (IHb xi bs rho Hxi Hbs Hlcr Hsem) as HRb.
    pose proof (IHs xi bs rho Hxi Hbs Hlcr Hsem) as HRs.
    set (en := erase (subst_tm rho nn2)).
    set (eb := erase (subst_tm rho bb)).
    set (es := erase (subst_tm rho ss)).
    assert (Hsn : strongly_normalizing en).
    { unfold en. apply (R_sn Ty_Nat xi bs (subst_tm rho nn2)
        (fun X _ => Hxi X) Hbs HRn). }
    assert (HRn' : R Ty_Nat xi bs en).
    { unfold en. apply (proj1 (R_erase_eq Ty_Nat xi bs (subst_tm rho nn2))). exact HRn. }
    assert (HRb' : R TT2 xi bs eb).
    { unfold eb. apply (proj1 (R_erase_eq TT2 xi bs (subst_tm rho bb))). exact HRb. }
    assert (HRs' : R (Ty_Arrow Ty_Nat (Ty_Arrow TT2 TT2)) xi bs es).
    { unfold es. apply (proj1 (R_erase_eq (Ty_Arrow Ty_Nat (Ty_Arrow TT2 TT2))
        xi bs (subst_tm rho ss))). exact HRs. }
    pose proof (R_natrec_gen en Hsn eb es TT2 xi bs
      (erase_idem en) (erase_idem eb) (erase_idem es) Hxi Hbs HRn' HRb' HRs') as Hrec.
    apply (proj2 (R_erase_congr TT2 xi bs
      (tm_natrec (subst_tm rho nn2) (subst_tm rho bb) (subst_tm rho ss))
      (tm_natrec en eb es))).
    + unfold en, eb, es. simpl. rewrite !erase_idem. reflexivity.
    + exact Hrec.
Qed.

End SystemFNormalizationRecursionHardTask.
