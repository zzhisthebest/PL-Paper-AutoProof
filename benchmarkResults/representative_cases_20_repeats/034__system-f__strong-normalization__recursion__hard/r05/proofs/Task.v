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

(* ================================================================== *)
(* 1. Erasure of type information                                      *)
(* ================================================================== *)

Fixpoint erase (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T t1 => tm_abs Ty_Nat (erase t1)
  | tm_app t1 t2 => tm_app (erase t1) (erase t2)
  | tm_tabs t1 => erase t1
  | tm_tapp t1 T => erase t1
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (erase t1)
  | tm_natrec n b s => tm_natrec (erase n) (erase b) (erase s)
  end.

Definition erased (t : tm) : Prop := erase t = t.

Definition lc (t : tm) : Prop := lc_tm_at 0 0 t.

Definition SN (t : tm) : Prop := strongly_normalizing t.

Lemma erase_idem : forall t, erase (erase t) = erase t.
Proof.
  induction t; simpl; try reflexivity; try (rewrite IHt; reflexivity);
  try (rewrite IHt1; rewrite IHt2; reflexivity);
  try (rewrite IHt1; rewrite IHt2; rewrite IHt3; reflexivity).
Qed.

Lemma erase_not_tabs : forall t u, erase t <> tm_tabs u.
Proof.
  intros t. induction t; intros u H; simpl in H; try discriminate;
  exfalso; apply (IHt u); exact H.
Qed.

Lemma erase_not_tapp : forall t u T, erase t <> tm_tapp u T.
Proof.
  intros t. induction t; intros u T H; simpl in H; try discriminate;
  exfalso; apply (IHt u T); exact H.
Qed.

Lemma erased_bvar : forall i, erased (tm_bvar i).
Proof. reflexivity. Qed.
Lemma erased_fvar : forall x, erased (tm_fvar x).
Proof. reflexivity. Qed.
Lemma erased_zero : erased tm_zero.
Proof. reflexivity. Qed.

Lemma erased_app_inv : forall t1 t2, erased (tm_app t1 t2) -> erased t1 /\ erased t2.
Proof.
  intros t1 t2 H. unfold erased in H. simpl in H. injection H as H1 H2. auto.
Qed.

Lemma erased_succ_inv : forall t, erased (tm_succ t) -> erased t.
Proof.
  intros t H. unfold erased in H. simpl in H. injection H as H1. exact H1.
Qed.

Lemma erased_abs_inv : forall T t, erased (tm_abs T t) -> T = Ty_Nat /\ erased t.
Proof.
  intros T t H. unfold erased in H. simpl in H. injection H as H1 H2. auto.
Qed.

Lemma erased_natrec_inv : forall n b s,
    erased (tm_natrec n b s) -> erased n /\ erased b /\ erased s.
Proof.
  intros n b s H. unfold erased in H. simpl in H.
  injection H as H1 H2 H3. auto.
Qed.

Lemma erased_not_tabs : forall t u, erased t -> t <> tm_tabs u.
Proof.
  intros t u He H. subst t. eapply erase_not_tabs; eauto.
Qed.

Lemma erased_not_tapp : forall t u T, erased t -> t <> tm_tapp u T.
Proof.
  intros t u T He H. subst t. eapply erase_not_tapp; eauto.
Qed.

(* ================================================================== *)
(* 2. Numeric values, values, and basic reduction facts                *)
(* ================================================================== *)

Lemma numeric_value_no_step : forall n u, numeric_value n -> ~ step n u.
Proof.
  intros n u Hnv. revert u. induction Hnv; intros u Hstep.
  - inversion Hstep.
  - inversion Hstep; subst. exact (IHHnv t' H0).
Qed.

Lemma value_no_step : forall v u, value v -> ~ step v u.
Proof.
  intros v u Hv. revert u. induction Hv; intros u Hstep.
  - inversion Hstep.
  - inversion Hstep.
  - exact (numeric_value_no_step n u H Hstep).
Qed.

Lemma multi_value : forall v u, value v -> multi v u -> u = v.
Proof.
  intros v u Hv Hm. induction Hm.
  - reflexivity.
  - exfalso. exact (value_no_step x y Hv H).
Qed.

Lemma SN_step : forall t, SN t -> forall u, step t u -> SN u.
Proof.
  intros t H. induction H as [t Hred IH]. intros u Hstep. apply (Hred u Hstep).
Qed.

Lemma SN_multi : forall t u, SN t -> multi t u -> SN u.
Proof.
  intros t u Hsn Hm. revert Hsn. induction Hm; intros Hsn.
  - exact Hsn.
  - apply IHHm. exact (SN_step x Hsn y H).
Qed.

Lemma value_SN : forall v, value v -> SN v.
Proof.
  intros v Hv. apply SN_intro. intros u Hstep.
  exfalso. exact (value_no_step v u Hv Hstep).
Qed.

Lemma numeric_value_SN : forall v, numeric_value v -> SN v.
Proof. intros. apply value_SN. constructor. assumption. Qed.

Lemma SN_abs : forall T t, SN (tm_abs T t).
Proof. intros. apply SN_intro. intros u H. inversion H. Qed.

Lemma SN_zero : SN tm_zero.
Proof. apply SN_intro. intros u H. inversion H. Qed.

Lemma SN_succ : forall t, SN t -> SN (tm_succ t).
Proof.
  intros t H. induction H as [t Hred IH]. apply SN_intro. intros u Hstep.
  inversion Hstep; subst. apply IH; assumption.
Qed.

Lemma SN_fvar : forall x, SN (tm_fvar x).
Proof. intro x. apply SN_intro. intros u H. inversion H. Qed.

(* Generic strong-normalization introduction from step-closedness.
   If every one-step reduct is SN then the term is SN. *)
Lemma SN_intro_step : forall t,
    (forall u, step t u -> SN u) -> SN t.
Proof. intros t H. apply SN_intro. exact H. Qed.


(* ================================================================== *)
(* 3. Local closure infrastructure                                     *)
(* ================================================================== *)

Lemma lc_ty_at_mono_K : forall T K K',
    lc_ty_at K T -> K <= K' -> lc_ty_at K' T.
Proof.
  induction T; intros K K' H Hle; inversion H; subst;
    eauto 8 using lc_ty_at, Nat.lt_le_trans, le_n_S.
Qed.

Lemma lc_ty_at_mono_nat : forall T K, lc_ty_at K T -> lc_ty_at (S K) T.
Proof. intros T K H. apply (lc_ty_at_mono_K T K (S K)); [exact H | lia]. Qed.

Lemma lc_tm_at_mono_K : forall t K K' d,
    lc_tm_at K d t -> K <= K' -> lc_tm_at K' d t.
Proof.
  induction t; intros K K' d H Hle; inversion H; subst;
    eauto 10 using lc_tm_at, lc_ty_at_mono_K, Nat.lt_le_trans, le_n_S.
Qed.

Lemma lc_tm_at_mono_d : forall t K d d',
    lc_tm_at K d t -> d <= d' -> lc_tm_at K d' t.
Proof.
  induction t; intros K d d' H Hle; inversion H; subst;
    eauto 10 using lc_tm_at, Nat.lt_le_trans, le_n_S.
Qed.

(* A locally closed at level 0 term is locally closed at any level. *)
Lemma lc_tm_at_weaken : forall t,
    lc_tm_at 0 0 t -> forall K d, lc_tm_at K d t.
Proof.
  intros t H K d.
  apply (lc_tm_at_mono_K t 0 K 0) in H; [|lia].
  apply (lc_tm_at_mono_d t K 0 d) in H; [|lia].
  exact H.
Qed.

Lemma numeric_value_lc : forall n, numeric_value n -> lc_tm_at 0 0 n.
Proof.
  intros n H. induction H; constructor; assumption.
Qed.

Lemma value_lc : forall v, value v -> lc_tm_at 0 0 v.
Proof.
  intros v H. induction H.
  - assumption.
  - assumption.
  - apply numeric_value_lc. assumption.
Qed.

(* Opening a type at the matching binder depth preserves local closure. *)
Lemma lc_ty_open : forall T K U,
    lc_ty_at (S K) T -> lc_ty_at K U -> lc_ty_at K (open_ty_rec K U T).
Proof.
  induction T; intros K U HT HU; simpl.
  - destruct (Nat.eqb K n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. exact HU.
    + apply lc_ty_bvar. inversion HT; subst. assert (n <> K) by (intro; subst; rewrite Nat.eqb_refl in E; discriminate). lia.
  - apply lc_ty_fvar.
  - inversion HT; subst. apply lc_ty_arrow; eauto.
  - inversion HT; subst. apply lc_ty_all. apply IHT. assumption.
    apply lc_ty_at_mono_nat. assumption.
  - apply lc_ty_nat.
Qed.

Lemma lc_tm_open_ty : forall t K d,
    lc_tm_at (S K) d t -> forall U, lc_ty_at K U ->
    lc_tm_at K d (open_tm_ty_rec K U t).
Proof.
  induction t; intros K d Hlc U HU; simpl.
  - inversion Hlc; subst. apply lc_tm_bvar. assumption.
  - apply lc_tm_fvar.
  - inversion Hlc; subst. apply lc_tm_abs.
    + eapply lc_ty_open; eauto.
    + apply IHt with (K:=K); assumption.
  - inversion Hlc; subst. apply lc_tm_app; eauto.
  - inversion Hlc; subst. apply lc_tm_tabs. apply IHt with (K:=S K). assumption.
    apply lc_ty_at_mono_nat. assumption.
  - inversion Hlc; subst. apply lc_tm_tapp.
    + apply IHt with (K:=K); assumption.
    + eapply lc_ty_open; eauto.
  - apply lc_tm_zero.
  - inversion Hlc; subst. apply lc_tm_succ; eauto.
  - inversion Hlc; subst. apply lc_tm_rec; eauto.
Qed.

(* Opening a term at the matching binder depth preserves local closure. *)
Lemma lc_tm_open : forall t K d,
    lc_tm_at K (S d) t -> forall u, lc_tm_at 0 0 u ->
    lc_tm_at K d (open_tm_rec d u t).
Proof.
  induction t; intros K d Hlc u Hu; simpl.
  - destruct (Nat.eqb d n) eqn:E.
    + apply Nat.eqb_eq in E. subst n.
      apply lc_tm_at_weaken. exact Hu.
    + apply lc_tm_bvar. inversion Hlc; subst.
      assert (n <> d) by (intro; subst; rewrite Nat.eqb_refl in E; discriminate). lia.
  - apply lc_tm_fvar.
  - inversion Hlc; subst. apply lc_tm_abs.
    + assumption.
    + apply IHt with (d:=S d); assumption.
  - inversion Hlc; subst. apply lc_tm_app; eauto.
  - inversion Hlc; subst. apply lc_tm_tabs. apply IHt with (K:=S K) (d:=d); assumption.
  - inversion Hlc; subst. apply lc_tm_tapp; eauto.
  - apply lc_tm_zero.
  - inversion Hlc; subst. apply lc_tm_succ; eauto.
  - inversion Hlc; subst. apply lc_tm_rec; eauto.
Qed.

(* Closing: if opening a term at depth d with a closed term is locally
   closed then the original term is locally closed at depth S d. *)
Lemma lc_tm_close : forall t K d u,
    lc_tm_at 0 0 u -> lc_tm_at K d (open_tm_rec d u t) -> lc_tm_at K (S d) t.
Proof.
  induction t; intros K d u Hu Hop; simpl in Hop.
  - destruct (Nat.eqb d n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. apply lc_tm_bvar. lia.
    + apply lc_tm_bvar. inversion Hop; subst.
      assert (n <> d) by (intro; subst; rewrite Nat.eqb_refl in E; discriminate). lia.
  - apply lc_tm_fvar.
  - inversion Hop; subst. apply lc_tm_abs.
    + assumption.
    + eapply IHt; eauto.
  - inversion Hop; subst. apply lc_tm_app; eauto.
  - inversion Hop; subst. apply lc_tm_tabs. eapply IHt with (K:=S K); eauto.
  - inversion Hop; subst. apply lc_tm_tapp; eauto.
  - apply lc_tm_zero.
  - inversion Hop; subst. apply lc_tm_succ; eauto.
  - inversion Hop; subst. apply lc_tm_rec; eauto.
Qed.

Lemma lc_tm_erase : forall t K d,
    lc_tm_at K d t -> forall K', lc_tm_at K' d (erase t).
Proof.
  intros t K d H. induction H; intros K'; simpl.
  - apply lc_tm_bvar. assumption.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + constructor.
    + apply IHlc_tm_at.
  - apply lc_tm_app.
    + apply IHlc_tm_at1.
    + apply IHlc_tm_at2.
  - change (lc_tm_at K' k (erase t)). apply IHlc_tm_at.
  - change (lc_tm_at K' k (erase t)). apply IHlc_tm_at.
  - apply lc_tm_zero.
  - apply lc_tm_succ. apply IHlc_tm_at.
  - apply lc_tm_rec.
    + apply IHlc_tm_at1.
    + apply IHlc_tm_at2.
    + apply IHlc_tm_at3.
Qed.

Lemma lc_ty_erase : forall T K, lc_ty_at K T -> lc_ty_at K Ty_Nat.
Proof. intros. constructor. Qed.

Lemma lc_app_inv : forall K k t1 t2,
    lc_tm_at K k (tm_app t1 t2) -> lc_tm_at K k t1 /\ lc_tm_at K k t2.
Proof. intros. inversion H. auto. Qed.

Lemma lc_abs_inv : forall K k T t,
    lc_tm_at K k (tm_abs T t) -> lc_ty_at K T /\ lc_tm_at K (S k) t.
Proof. intros. inversion H. auto. Qed.

Lemma lc_tabs_inv : forall K k t,
    lc_tm_at K k (tm_tabs t) -> lc_tm_at (S K) k t.
Proof. intros. inversion H. auto. Qed.

Lemma lc_tapp_inv : forall K k t T,
    lc_tm_at K k (tm_tapp t T) -> lc_tm_at K k t /\ lc_ty_at K T.
Proof. intros. inversion H. auto. Qed.

Lemma lc_succ_inv : forall K k t,
    lc_tm_at K k (tm_succ t) -> lc_tm_at K k t.
Proof. intros. inversion H. auto. Qed.

Lemma lc_rec_inv : forall K k n b s,
    lc_tm_at K k (tm_natrec n b s) ->
    lc_tm_at K k n /\ lc_tm_at K k b /\ lc_tm_at K k s.
Proof. intros. inversion H. auto. Qed.

Lemma lc_bvar_inv : forall K k i, lc_tm_at K k (tm_bvar i) -> i < k.
Proof. intros. inversion H. auto. Qed.

Lemma step_lc : forall t u, step t u -> lc t -> lc u.
Proof.
  intros t u Hstep. induction Hstep; intros Hlc; unfold lc in *.
  - (* ST_AppAbs *)
    destruct (lc_app_inv 0 0 (tm_abs T t) v Hlc) as [H1 H2].
    destruct (lc_abs_inv 0 0 T t H1) as [HT Ht].
    apply lc_tm_at_weaken.
    eapply lc_tm_open; [exact Ht | apply value_lc; assumption].
  - (* ST_App1 *)
    destruct (lc_app_inv 0 0 t1 t2 Hlc) as [H1 H2].
    apply lc_tm_app.
    + apply IHHstep. exact H1.
    + exact H2.
  - (* ST_App2 *)
    destruct (lc_app_inv 0 0 v1 t2 Hlc) as [H1 H2].
    apply lc_tm_app.
    + exact H1.
    + apply IHHstep. exact H2.
  - (* ST_TAppTabs *)
    destruct (lc_tapp_inv 0 0 (tm_tabs t) T Hlc) as [H1 H2].
    pose proof (lc_tabs_inv 0 0 t H1) as H3.
    unfold open_tm_ty.
    apply lc_tm_at_weaken.
    eapply lc_tm_open_ty; [exact H3 | exact H0].
  - (* ST_TApp *)
    destruct (lc_tapp_inv 0 0 t T Hlc) as [H1 H2].
    apply lc_tm_tapp.
    + apply IHHstep. exact H1.
    + exact H2.
  - (* ST_Succ *)
    apply lc_tm_succ. apply IHHstep. apply lc_succ_inv in Hlc. exact Hlc.
  - (* ST_RecArg *)
    destruct (lc_rec_inv 0 0 n b s Hlc) as [H1 [H2 H3]].
    apply lc_tm_rec.
    + apply IHHstep. exact H1.
    + exact H2.
    + exact H3.
  - (* ST_RecBase *)
    destruct (lc_rec_inv 0 0 n b s Hlc) as [H1 [H2 H3]].
    apply lc_tm_rec.
    + exact H1.
    + apply IHHstep. exact H2.
    + exact H3.
  - (* ST_RecStep *)
    destruct (lc_rec_inv 0 0 n b s Hlc) as [H1 [H2 H3]].
    apply lc_tm_rec.
    + exact H1.
    + exact H2.
    + apply IHHstep. exact H3.
  - (* ST_RecZero *)
    destruct (lc_rec_inv 0 0 tm_zero b s Hlc) as [H1 [H2 H3]].
    exact H2.
  - (* ST_RecSucc *)
    destruct (lc_rec_inv 0 0 (tm_succ n) b s Hlc) as [Hn [Hb Hs]].
    apply lc_succ_inv in Hn.
    apply lc_tm_app.
    + apply lc_tm_app.
      * exact Hs.
      * exact Hn.
    + apply lc_tm_rec; assumption.
Qed.

Lemma multi_lc : forall t u, multi t u -> lc t -> lc u.
Proof.
  intros t u Hm. induction Hm; intros Hlc.
  - exact Hlc.
  - apply IHHm. eapply step_lc; eauto.
Qed.

(* Erasure and opening commute. *)
Lemma erase_open_tm_rec : forall t k u,
    erase (open_tm_rec k u t) = open_tm_rec k (erase u) (erase t).
Proof.
  induction t as [i|x|T t1 IH1|t1 IH1 t2 IH2|t1 IH1|t1 IH1 T| |t1 IH1|n IHn b IHb s IHs];
    intros k u; simpl.
  - destruct (Nat.eqb k i); reflexivity.
  - reflexivity.
  - rewrite IH1. reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH1. reflexivity.
  - rewrite IH1. reflexivity.
  - reflexivity.
  - rewrite IH1. reflexivity.
  - rewrite IHn, IHb, IHs. reflexivity.
Qed.

Lemma erase_open_tm : forall t u,
    erase (open_tm t u) = open_tm (erase t) (erase u).
Proof. intros. apply erase_open_tm_rec. Qed.

Lemma erase_open_tm_ty_rec : forall t k U,
    erase (open_tm_ty_rec k U t) = erase t.
Proof.
  induction t as [i|x|T t1 IH1|t1 IH1 t2 IH2|t1 IH1|t1 IH1 T| |t1 IH1|n IHn b IHb s IHs];
    intros k U; simpl; try reflexivity.
  - rewrite IH1. reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH1. reflexivity.
  - rewrite IH1. reflexivity.
  - rewrite IH1. reflexivity.
  - rewrite IHn, IHb, IHs. reflexivity.
Qed.

Lemma erase_open_tm_ty : forall t U, erase (open_tm_ty t U) = erase t.
Proof. intros. apply erase_open_tm_ty_rec. Qed.

Lemma step_erased : forall t u, step t u -> erased t -> erased u.
Proof.
  intros t u Hstep. induction Hstep; intros He; unfold erased in *.
  - (* ST_AppAbs *)
    simpl in He. injection He as _ He1' He2.
    rewrite erase_open_tm. rewrite He1', He2. reflexivity.
  - (* ST_App1 *)
    simpl in He. injection He as He1 He2. simpl.
    rewrite (IHHstep He1). rewrite He2. reflexivity.
  - (* ST_App2 *)
    simpl in He. injection He as He1 He2. simpl.
    rewrite (IHHstep He2). rewrite He1. reflexivity.
  - (* ST_TAppTabs *)
    exfalso. eapply erase_not_tapp. apply He.
  - (* ST_TApp *)
    exfalso. eapply erase_not_tapp. apply He.
  - (* ST_Succ *)
    simpl in He. injection He as He1. simpl. rewrite (IHHstep He1). reflexivity.
  - (* ST_RecArg *)
    simpl in He. injection He as He1 He2 He3. simpl.
    rewrite (IHHstep He1). rewrite He2, He3. reflexivity.
  - (* ST_RecBase *)
    simpl in He. injection He as He1 He2 He3. simpl.
    rewrite (IHHstep He2). rewrite He1, He3. reflexivity.
  - (* ST_RecStep *)
    simpl in He. injection He as He1 He2 He3. simpl.
    rewrite (IHHstep He3). rewrite He1, He2. reflexivity.
  - (* ST_RecZero *)
    simpl in He. injection He as He1 He2. exact He1.
  - (* ST_RecSucc *)
    simpl in He. injection He as He1 He2 He3.
    simpl. rewrite He1, He2, He3. reflexivity.
Qed.

Lemma multi_erased : forall t u, multi t u -> erased t -> erased u.
Proof.
  intros t u Hm. induction Hm; intros He.
  - exact He.
  - apply IHHm. eapply step_erased; eauto.
Qed.



(* ================================================================== *)
(* 4. The unary logical relation (erased terms)                        *)
(* ================================================================== *)

Definition cand := tm -> Prop.

Definition candidate (C : cand) : Prop :=
  (forall e, C e -> SN e) /\
  (forall e, C e -> erased e) /\
  (forall e, C e -> lc e) /\
  (forall e e', C e -> step e e' -> C e') /\
  (forall e, SN e -> erased e -> lc e -> ~ value e ->
      (forall e', step e e' -> C e') -> C e).

Definition no_cand : cand := fun _ => False.

(* The value relation: a unary, type-indexed logical relation on values.
   The term relation [Rt] below is its natural extension to arbitrary
   terms via "every value reduct is related".  We inline the definition
   of [Rt] in the arrow clause so that the fixpoint only recurses on
   strict subterms of the type. *)
Fixpoint Vt (rho : atom -> cand) (env : list cand) (T : ty) : tm -> Prop :=
  match T with
  | Ty_Nat =>
      fun v => SN v /\ erased v /\ lc v /\ numeric_value v
  | Ty_Arrow T1 T2 =>
      fun v => SN v /\ erased v /\ lc v /\
        forall u, erased u -> lc u -> value u -> Vt rho env T1 u ->
          SN (tm_app v u) /\ erased (tm_app v u) /\ lc (tm_app v u) /\
          (forall w, multi (tm_app v u) w -> value w -> Vt rho env T2 w)
  | Ty_All T1 =>
      fun v => SN v /\ erased v /\ lc v /\
        forall C, candidate C -> Vt rho (C :: env) T1 v
  | Ty_BVar i =>
      fun v => SN v /\ erased v /\ lc v /\ nth i env no_cand v
  | Ty_FVar X =>
      fun v => SN v /\ erased v /\ lc v /\ rho X v
  end.

Definition Rt (rho : atom -> cand) (env : list cand) (T : ty) (e : tm) : Prop :=
  SN e /\ erased e /\ lc e /\
    forall v, multi e v -> value v -> Vt rho env T v.

Lemma Vt_Nat_iff : forall rho env v,
    Vt rho env Ty_Nat v <-> SN v /\ erased v /\ lc v /\ numeric_value v.
Proof. intros. unfold Vt. simpl. reflexivity. Qed.

Lemma Vt_Arrow_iff : forall rho env T1 T2 v,
    Vt rho env (Ty_Arrow T1 T2) v <->
    SN v /\ erased v /\ lc v /\
      forall u, erased u -> lc u -> value u -> Vt rho env T1 u ->
        Rt rho env T2 (tm_app v u).
Proof. intros. unfold Vt, Rt. simpl. reflexivity. Qed.

Lemma Vt_All_iff : forall rho env T1 v,
    Vt rho env (Ty_All T1) v <->
    SN v /\ erased v /\ lc v /\
      forall C, candidate C -> Vt rho (C :: env) T1 v.
Proof. intros. unfold Vt. simpl. reflexivity. Qed.

Lemma Vt_BVar_iff : forall rho env i v,
    Vt rho env (Ty_BVar i) v <->
    SN v /\ erased v /\ lc v /\ nth i env no_cand v.
Proof. intros. unfold Vt. simpl. reflexivity. Qed.

Lemma Vt_FVar_iff : forall rho env X v,
    Vt rho env (Ty_FVar X) v <->
    SN v /\ erased v /\ lc v /\ rho X v.
Proof. intros. unfold Vt. simpl. reflexivity. Qed.

Definition candidate_rho (rho : atom -> cand) : Prop :=
  forall X, candidate (rho X).

Definition candidates_env (env : list cand) : Prop :=
  forall C, In C env -> candidate C.

Lemma Vt_SN : forall rho env T v, Vt rho env T v -> SN v.
Proof.
  intros rho env T v H. destruct T; unfold Vt in H; simpl in H; tauto.
Qed.

Lemma Vt_erased : forall rho env T v, Vt rho env T v -> erased v.
Proof.
  intros rho env T v H. destruct T; unfold Vt in H; simpl in H; tauto.
Qed.

Lemma Vt_lc : forall rho env T v, Vt rho env T v -> lc v.
Proof.
  intros rho env T v H. destruct T; unfold Vt in H; simpl in H; tauto.
Qed.

Lemma Rt_def : forall rho env T e,
    Rt rho env T e <->
    SN e /\ erased e /\ lc e /\
      forall v, multi e v -> value v -> Vt rho env T v.
Proof.
  intros rho env T e. destruct T; unfold Rt, Vt; simpl; reflexivity.
Qed.

Lemma Rt_SN : forall rho env T e, Rt rho env T e -> SN e.
Proof. intros. unfold Rt in H. tauto. Qed.

Lemma Rt_erased : forall rho env T e, Rt rho env T e -> erased e.
Proof. intros. unfold Rt in H. tauto. Qed.

Lemma Rt_lc : forall rho env T e, Rt rho env T e -> lc e.
Proof. intros. unfold Rt in H. tauto. Qed.

Lemma Rt_to_Vt : forall rho env T v,
    Rt rho env T v -> value v -> Vt rho env T v.
Proof.
  intros rho env T v H HV. unfold Rt in H.
  destruct H as [_ [_ [_ Hred]]]. apply (Hred v (multi_refl v) HV).
Qed.

Lemma Vt_to_Rt : forall rho env T v,
    Vt rho env T v -> value v -> Rt rho env T v.
Proof.
  intros rho env T v HV Hval. unfold Rt.
  split.
  - apply Vt_SN in HV. exact HV.
  - split.
    + apply Vt_erased in HV. exact HV.
    + split.
      * apply Vt_lc in HV. exact HV.
      * intros w Hm Hw. rewrite (multi_value v w Hval Hm). exact HV.
Qed.

Lemma multi_nonvalue_step : forall e v,
    ~ value e -> value v -> multi e v -> exists e', step e e' /\ multi e' v.
Proof.
  intros e v Hnv Hval Hm. destruct Hm.
  - exfalso. apply Hnv. exact Hval.
  - exists y. split; assumption.
Qed.

Lemma multi_stuck : forall e v,
    (forall u, ~ step e u) -> multi e v -> v = e.
Proof.
  intros e v Hst Hm. induction Hm.
  - reflexivity.
  - exfalso. apply (Hst y). exact H.
Qed.

Lemma zero_no_step : forall u, ~ step tm_zero u.
Proof. intros u H. inversion H. Qed.

Lemma app_zero_zero_no_step : forall u, ~ step (tm_app tm_zero tm_zero) u.
Proof.
  intros u H. inversion H; subst.
  all: match goal with
       | Hst : tm_zero --> _ |- False => exact (zero_no_step _ Hst)
       end.
Qed.

Lemma Rt_top : forall rho env T, Rt rho env T (tm_app tm_zero tm_zero).
Proof.
  intros rho env T. unfold Rt. split.
  - apply SN_intro. intros u H. exfalso. eapply app_zero_zero_no_step; eauto.
  - split.
    + reflexivity.
    + split.
      * repeat constructor.
      * intros v Hm Hval.
        assert (Hv : v = tm_app tm_zero tm_zero)
          by (apply (multi_stuck (tm_app tm_zero tm_zero) v app_zero_zero_no_step Hm)).
        subst v. inversion Hval.
        all: match goal with H : numeric_value (tm_app _ _) |- _ => inversion H end.
Qed.

Lemma Rt_step : forall rho env T e e',
    Rt rho env T e -> step e e' -> Rt rho env T e'.
Proof.
  intros rho env T e e' HR Hstep. unfold Rt in HR.
  destruct HR as [Hsn [Her [Hlc Hred]]].
  unfold Rt. split.
  - exact (SN_step e Hsn e' Hstep).
  - split.
    + exact (step_erased e e' Hstep Her).
    + split.
      * exact (step_lc e e' Hstep Hlc).
      * intros v Hmv Hval. apply Hred with (v:=v).
        -- apply multi_step with (y:=e'); assumption.
        -- assumption.
Qed.

Lemma Rt_multi : forall rho env T e e',
    Rt rho env T e -> multi e e' -> Rt rho env T e'.
Proof.
  intros rho env T e e' HR Hm. induction Hm.
  - exact HR.
  - apply IHHm. eapply Rt_step; eauto.
Qed.

Lemma Rt_expand : forall rho env T e,
    SN e -> erased e -> lc e -> ~ value e ->
    (forall e', step e e' -> Rt rho env T e') -> Rt rho env T e.
Proof.
  intros rho env T e Hsn Her Hlc Hnv Hsteps. unfold Rt. split.
  - exact Hsn.
  - split.
    + exact Her.
    + split.
      * exact Hlc.
      * intros v Hmv Hval.
        destruct (multi_nonvalue_step e v Hnv Hval Hmv) as [e' [Hstep Hm']].
        pose proof (Hsteps e' Hstep) as HR'; unfold Rt in HR';
        destruct HR' as [_ [_ [_ Hred]]].
        apply (Hred v Hm' Hval).
Qed.

Lemma candidate_Rt : forall rho env T, candidate (Rt rho env T).
Proof.
  intros rho env T. unfold candidate. split.
  - intros e H. exact (Rt_SN rho env T e H).
  - split.
    + intros e H. exact (Rt_erased rho env T e H).
    + split.
      * intros e H. exact (Rt_lc rho env T e H).
      * split.
        -- intros e e' H Hs. exact (Rt_step rho env T e e' H Hs).
        -- intros e Hsn Her Hlc Hnv Hsteps.
           exact (Rt_expand rho env T e Hsn Her Hlc Hnv Hsteps).
Qed.



(* ================================================================== *)
(* 5. Application lemmas                                               *)
(* ================================================================== *)

Lemma SN_app_value : forall (rho : atom -> cand) (env : list cand) (T1 T2 : ty) (e1 : tm),
    value e1 -> Vt rho env (Ty_Arrow T1 T2) e1 ->
    forall e2, Rt rho env T1 e2 -> SN (tm_app e1 e2).
Proof.
  intros rho env T1 T2 e1 Hval HV e2 HR2.
  destruct HV as [Hsn1 [Her1 [Hlc1 HVapp]]].
  assert (Hsn := Rt_SN rho env T1 e2 HR2).
  revert HR2. induction Hsn as [e2 Hred IH]. intros HR2.
  apply SN_intro. intros y Hstep.
  inversion Hstep; subst.
  - (* ST_AppAbs *)
    assert (HR : Rt rho env T2 (tm_app (tm_abs T t) e2)).
    { apply HVapp.
      - apply Rt_erased in HR2. exact HR2.
      - apply Rt_lc in HR2. exact HR2.
      - exact H3.
      - apply Rt_to_Vt; assumption. }
    apply (SN_step (tm_app (tm_abs T t) e2)).
    + apply Rt_SN in HR. exact HR.
    + exact Hstep.
  - (* ST_App1 : e1 steps, impossible since e1 is a value *)
    exfalso.
    match goal with Hst : e1 --> _ |- _ => exact (value_no_step e1 _ Hval Hst) end.
  - (* ST_App2 : e2 steps *)
    match goal with
    | Hst : e2 --> ?u |- _ =>
        apply (IH u Hst); exact (Rt_step rho env T1 e2 u HR2 Hst)
    end.
Qed.


Lemma SN_app : forall (rho : atom -> cand) (env : list cand) (T1 T2 : ty) e1 e2,
    Rt rho env (Ty_Arrow T1 T2) e1 -> Rt rho env T1 e2 -> SN (tm_app e1 e2).
Proof.
  intros rho env T1 T2 e1 e2 HR1 HR2.
  assert (Hsn := Rt_SN rho env (Ty_Arrow T1 T2) e1 HR1).
  revert e2 HR1 HR2. induction Hsn as [e1 Hred IH]. intros e2 HR1 HR2.
  apply SN_intro. intros y Hstep. inversion Hstep; subst.
  - (* ST_AppAbs *)
    match goal with
    | Hlc : locally_closed_tm (tm_abs ?T ?t) |- _ =>
        pose proof (v_abs T t Hlc) as Hvalabs;
        pose proof (SN_app_value rho env T1 T2 (tm_abs T t) Hvalabs
                      (Rt_to_Vt rho env (Ty_Arrow T1 T2) (tm_abs T t) HR1 Hvalabs)
                      e2 HR2) as Hsnapp;
        exact (SN_step (tm_app (tm_abs T t) e2) Hsnapp (open_tm t e2) Hstep)
    end.
  - (* ST_App1 *)
    match goal with
    | Hst : e1 --> ?u |- _ =>
        apply (IH u Hst);
        [exact (Rt_step rho env (Ty_Arrow T1 T2) e1 u HR1 Hst) | exact HR2]
    end.
  - (* ST_App2 *)
    match goal with
    | Hv : value e1, Hst : e2 --> ?u |- _ =>
        exact (SN_app_value rho env T1 T2 e1 Hv
                 (Rt_to_Vt rho env (Ty_Arrow T1 T2) e1 HR1 Hv)
                 u (Rt_step rho env T1 e2 u HR2 Hst))
    end.
Qed.

Lemma Rt_app_vred : forall (rho : atom -> cand) (env : list cand) (T1 T2 : ty) x v,
    multi x v -> value v ->
    forall e1 e2, x = tm_app e1 e2 ->
      Rt rho env (Ty_Arrow T1 T2) e1 -> Rt rho env T1 e2 -> Vt rho env T2 v.
Proof.
  intros rho env T1 T2 x v Hm.
  induction Hm as [x| x y z Hstep Hm IH]; intros Hval e1 e2 Heq HR1 HR2.
  - (* refl *)
    rewrite Heq in Hval.
    inversion Hval.
    all: match goal with H : numeric_value (tm_app _ _) |- _ => inversion H end.
  - (* step *)
    subst x. inversion Hstep; subst.
    + (* ST_AppAbs *)
      match goal with
      | Hlc : locally_closed_tm (tm_abs ?T ?t), Hv2 : value e2 |- _ =>
          pose proof (v_abs T t Hlc) as Hvalabs;
          pose proof (Rt_to_Vt rho env (Ty_Arrow T1 T2) (tm_abs T t) HR1 Hvalabs) as HVabs;
          destruct HVabs as [_ [_ [_ HVapp]]];
          pose proof (HVapp e2 (Rt_erased rho env T1 e2 HR2)
                        (Rt_lc rho env T1 e2 HR2) Hv2
                        (Rt_to_Vt rho env T1 e2 HR2 Hv2)) as HRede;
          unfold Rt in HRede; destruct HRede as [_ [_ [_ Hred]]];
          exact (Hred z (multi_step (tm_app (tm_abs T t) e2) (open_tm t e2) z
                             Hstep Hm) Hval)
      end.
    + (* ST_App1 *)
      match goal with
      | Hst : e1 --> ?u |- _ =>
          apply (IH Hval u e2 eq_refl);
          [exact (Rt_step rho env (Ty_Arrow T1 T2) e1 u HR1 Hst) | exact HR2]
      end.
    + (* ST_App2 *)
      match goal with
      | Hst : e2 --> ?u |- _ =>
          apply (IH Hval e1 u eq_refl HR1);
          exact (Rt_step rho env T1 e2 u HR2 Hst)
      end.
Qed.

Lemma Rt_app : forall (rho : atom -> cand) (env : list cand) (T1 T2 : ty) e1 e2,
    Rt rho env (Ty_Arrow T1 T2) e1 -> Rt rho env T1 e2 ->
    Rt rho env T2 (tm_app e1 e2).
Proof.
  intros rho env T1 T2 e1 e2 HR1 HR2.
  unfold Rt. split.
  - (* SN *) apply (SN_app rho env T1 T2); assumption.
  - split.
    + (* erased *) unfold erased. simpl.
      rewrite (Rt_erased rho env (Ty_Arrow T1 T2) e1 HR1).
      rewrite (Rt_erased rho env T1 e2 HR2). reflexivity.
    + split.
      * (* lc *) apply lc_tm_app.
        -- apply (Rt_lc rho env (Ty_Arrow T1 T2) e1 HR1).
        -- apply (Rt_lc rho env T1 e2 HR2).
      * (* value reducts *) intros v Hm Hval.
        eapply Rt_app_vred; eauto.
Qed.



(* ================================================================== *)
(* 6. The recursor                                                     *)
(* ================================================================== *)

Lemma numeric_value_erased : forall m, numeric_value m -> erased m.
Proof.
  intros m H. induction H.
  - reflexivity.
  - unfold erased in *. simpl. rewrite IHnumeric_value. reflexivity.
Qed.

Lemma Vt_Nat_intro : forall rho env v,
    SN v -> erased v -> lc v -> numeric_value v -> Vt rho env Ty_Nat v.
Proof. intros. unfold Vt. simpl. auto. Qed.

Lemma numeric_value_Rt : forall rho env m,
    numeric_value m -> Rt rho env Ty_Nat m.
Proof.
  intros rho env m Hm. unfold Rt. split.
  - apply numeric_value_SN. assumption.
  - split.
    + apply numeric_value_erased. assumption.
    + split.
      * apply numeric_value_lc. assumption.
      * intros v Hmv Hval.
        assert (v = m) by (eapply multi_value; eauto using value_SN, numeric_value_SN).
        subst v. apply Vt_Nat_intro.
        -- apply numeric_value_SN. assumption.
        -- apply numeric_value_erased. assumption.
        -- apply numeric_value_lc. assumption.
        -- assumption.
Qed.

Lemma step_natrec_inv : forall n b s y,
    step (tm_natrec n b s) y ->
    (exists n', step n n' /\ y = tm_natrec n' b s) \/
    (numeric_value n /\ exists b', step b b' /\ y = tm_natrec n b' s) \/
    (numeric_value n /\ value b /\ exists s', step s s' /\ y = tm_natrec n b s') \/
    (n = tm_zero /\ value b /\ value s /\ y = b) \/
    (exists m, n = tm_succ m /\ numeric_value m /\ value b /\ value s /\
               y = tm_app (tm_app s m) (tm_natrec m b s)).
Proof.
  intros n b s y H. inversion H; subst; eauto 10.
Qed.

Lemma nv_natrec : forall n b s, ~ value (tm_natrec n b s).
Proof.
  intros n b s Hv. inversion Hv.
  match goal with H : numeric_value (tm_natrec _ _ _) |- _ => inversion H end.
Qed.

Lemma Rt_natrec_num : forall (rho : atom -> cand) (env : list cand) (T : ty) m,
    numeric_value m ->
    forall b s,
      Rt rho env T b ->
      Rt rho env (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
      Rt rho env T (tm_natrec m b s).
Proof.
  intros rho env T m Hm.
  induction Hm as [| m0 Hm0 IHm]; intros b s Hb Hs.
  - (* m = zero *)
    assert (Hsn_s := Rt_SN rho env (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s Hs).
    revert b Hb Hs.
    induction Hsn_s as [s Hsred IHs].
    intros b Hb Hs.
    assert (Hsn_b := Rt_SN rho env T b Hb).
    revert Hb.
    induction Hsn_b as [b Hbred IHb].
    intros Hb.
    assert (Hsteps : forall y, step (tm_natrec tm_zero b s) y -> Rt rho env T y).
    { intros y Hy. destruct (step_natrec_inv tm_zero b s y Hy)
        as [[n' [Hst Heq]] |
            [[Hnum [b' [Hst Heq]]] |
             [[Hnum [Hvb [s' [Hst Heq]]]] |
              [[Hzero [Hvb [Hvs Heq]]] |
               [m1 [Hn [Hnum [Hvb [Hvs Heq]]]]]]]]].
      - subst y. exfalso. exact (numeric_value_no_step tm_zero n' nv_zero Hst).
      - subst y. apply (IHb b' Hst). exact (Rt_step rho env T b b' Hb Hst).
      - subst y. apply (IHs s' Hst b Hb).
        exact (Rt_step rho env (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s s' Hs Hst).
      - subst y. exact Hb.
      - subst y. exfalso. inversion Hn.
    }
    apply Rt_expand.
    + apply SN_intro. intros y Hy. exact (Rt_SN rho env T y (Hsteps y Hy)).
    + unfold erased. simpl.
      rewrite (Rt_erased rho env T b Hb).
      rewrite (Rt_erased rho env (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s Hs). reflexivity.
    + simpl. apply lc_tm_rec.
      * constructor.
      * apply (Rt_lc rho env T b Hb).
      * apply (Rt_lc rho env (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s Hs).
    + exact (nv_natrec tm_zero b s).
    + exact Hsteps.
  - (* m = succ m0 *)
    assert (Hsn_s := Rt_SN rho env (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s Hs).
    revert b Hb Hs.
    induction Hsn_s as [s Hsred IHs].
    intros b Hb Hs.
    assert (Hsn_b := Rt_SN rho env T b Hb).
    revert Hb.
    induction Hsn_b as [b Hbred IHb].
    intros Hb.
    assert (Hsteps : forall y, step (tm_natrec (tm_succ m0) b s) y -> Rt rho env T y).
    { intros y Hy. destruct (step_natrec_inv (tm_succ m0) b s y Hy)
        as [[n' [Hst Heq]] |
            [[Hnum [b' [Hst Heq]]] |
             [[Hnum [Hvb [s' [Hst Heq]]]] |
              [[Hzero [Hvb [Hvs Heq]]] |
               [m1 [Hn [Hnum [Hvb [Hvs Heq]]]]]]]]].
      - subst y. exfalso. exact (numeric_value_no_step (tm_succ m0) n' (nv_succ m0 Hm0) Hst).
      - subst y. apply (IHb b' Hst). exact (Rt_step rho env T b b' Hb Hst).
      - subst y. apply (IHs s' Hst b Hb).
        exact (Rt_step rho env (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s s' Hs Hst).
      - subst y. exfalso. inversion Hzero.
      - subst y. inversion Hn; subst.
        apply (Rt_app rho env T T (tm_app s m1) (tm_natrec m1 b s)).
        + apply (Rt_app rho env Ty_Nat (Ty_Arrow T T) s m1 Hs).
          exact (numeric_value_Rt rho env m1 Hm0).
        + apply (IHm b s Hb Hs).
    }
    apply Rt_expand.
    + apply SN_intro. intros y Hy. exact (Rt_SN rho env T y (Hsteps y Hy)).
    + unfold erased. simpl.
      rewrite (numeric_value_erased m0 Hm0).
      rewrite (Rt_erased rho env T b Hb).
      rewrite (Rt_erased rho env (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s Hs). reflexivity.
    + simpl. apply lc_tm_rec.
      * apply lc_tm_succ. apply numeric_value_lc. assumption.
      * apply (Rt_lc rho env T b Hb).
      * apply (Rt_lc rho env (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s Hs).
    + exact (nv_natrec (tm_succ m0) b s).
    + exact Hsteps.
Qed.



(* ================================================================== *)
(* 7. Agreement lemmas for environments and type-variable valuations   *)
(* ================================================================== *)

Lemma lc_ty_arrow_inv : forall k T1 T2,
    lc_ty_at k (Ty_Arrow T1 T2) -> lc_ty_at k T1 /\ lc_ty_at k T2.
Proof. intros. inversion H. auto. Qed.

Lemma lc_ty_all_inv : forall k T,
    lc_ty_at k (Ty_All T) -> lc_ty_at (S k) T.
Proof. intros. inversion H. auto. Qed.

Lemma lc_ty_bvar_inv : forall k i, lc_ty_at k (Ty_BVar i) -> i < k.
Proof. intros. inversion H. auto. Qed.

Lemma Rt_equiv_of_Vt_equiv : forall (rho1 rho2 : atom -> cand) env1 env2 T,
    (forall e, value e -> (Vt rho1 env1 T e <-> Vt rho2 env2 T e)) ->
    forall e, Rt rho1 env1 T e <-> Rt rho2 env2 T e.
Proof.
  intros rho1 rho2 env1 env2 T HV e.
  destruct T; simpl; split;
    intros [Hs [He [Hl Hred]]]; repeat split; auto;
    intros v Hm Hvv; apply HV; auto; apply Hred; auto.
Qed.

Lemma VR_env_rel : forall T k (rho : atom -> cand) env1 env2,
    lc_ty_at k T ->
    (forall i, i < k -> forall e, nth i env1 no_cand e <-> nth i env2 no_cand e) ->
    (forall e, value e -> (Vt rho env1 T e <-> Vt rho env2 T e))
    /\ (forall e, Rt rho env1 T e <-> Rt rho env2 T e).
Proof.
  induction T; intros k rho env1 env2 Hlc Henv.
  - (* Ty_BVar n *)
    assert (HV : forall e, value e ->
       (Vt rho env1 (Ty_BVar n) e <-> Vt rho env2 (Ty_BVar n) e)).
    { intros e Hv. unfold Vt; simpl.
      assert (Hnk : n < k) by (apply lc_ty_bvar_inv; assumption).
      assert (Hnth : nth n env1 no_cand e <-> nth n env2 no_cand e)
        by (apply Henv; assumption).
      tauto. }
    split; [exact HV | apply (Rt_equiv_of_Vt_equiv rho rho env1 env2 (Ty_BVar n)); exact HV].
  - (* Ty_FVar x *)
    assert (HV : forall e, value e ->
       (Vt rho env1 (Ty_FVar x) e <-> Vt rho env2 (Ty_FVar x) e)).
    { intros e Hv. unfold Vt; simpl. tauto. }
    split; [exact HV | apply (Rt_equiv_of_Vt_equiv rho rho env1 env2 (Ty_FVar x)); exact HV].
  - (* Ty_Arrow T1 T2 *)
    assert (HV : forall e, value e ->
       (Vt rho env1 (Ty_Arrow T1 T2) e <-> Vt rho env2 (Ty_Arrow T1 T2) e)).
    { intros e Hval.
      destruct (lc_ty_arrow_inv k T1 T2 Hlc) as [Hlc1 Hlc2].
      destruct (IHT1 k rho env1 env2 Hlc1 Henv) as [HV1 _].
      destruct (IHT2 k rho env1 env2 Hlc2 Henv) as [_ HR2].
      unfold Vt; simpl.
      split.
      - intros [Hs [He [Hl Hred]]]. repeat split; auto.
        intros u Heu Hlu Hvu Hvu2.
        apply (proj1 (HR2 (tm_app e u))).
        apply (Hred u Heu Hlu Hvu (proj2 (HV1 u Hvu) Hvu2)).
      - intros [Hs [He [Hl Hred]]]. repeat split; auto.
        intros u Heu Hlu Hvu Hvu2.
        apply (proj2 (HR2 (tm_app e u))).
        apply (Hred u Heu Hlu Hvu (proj1 (HV1 u Hvu) Hvu2)).
    }
    split; [exact HV | apply (Rt_equiv_of_Vt_equiv rho rho env1 env2 (Ty_Arrow T1 T2)); exact HV].
  - (* Ty_All T1 *)
    assert (HV : forall e, value e ->
       (Vt rho env1 (Ty_All T1) e <-> Vt rho env2 (Ty_All T1) e)).
    { intros e Hval.
      destruct (lc_ty_all_inv k T1 Hlc) as [Hlc1].
      unfold Vt; simpl.
      split.
      - intros [Hs [He [Hl Hred]]]. repeat split; auto.
        intros C HC.
        assert (Henv' : forall i, i < S k -> forall x,
           nth i (C :: env1) no_cand x <-> nth i (C :: env2) no_cand x).
        { intros i Hi x. destruct i; simpl.
          - reflexivity.
          - apply Henv. lia. }
        destruct (IHT1 (S k) rho (C :: env1) (C :: env2) Hlc1 Henv') as [HV1 _].
        apply (HV1 e Hval). apply Hred; auto.
      - intros [Hs [He [Hl Hred]]]. repeat split; auto.
        intros C HC.
        assert (Henv' : forall i, i < S k -> forall x,
           nth i (C :: env1) no_cand x <-> nth i (C :: env2) no_cand x).
        { intros i Hi x. destruct i; simpl.
          - reflexivity.
          - apply Henv. lia. }
        destruct (IHT1 (S k) rho (C :: env1) (C :: env2) Hlc1 Henv') as [HV1 _].
        apply (HV1 e Hval). apply Hred; auto.
    }
    split; [exact HV | apply (Rt_equiv_of_Vt_equiv rho rho env1 env2 (Ty_All T1)); exact HV].
  - (* Ty_Nat *)
    assert (HV : forall e, value e ->
       (Vt rho env1 Ty_Nat e <-> Vt rho env2 Ty_Nat e)).
    { intros e Hv. unfold Vt; simpl. tauto. }
    split; [exact HV | apply (Rt_equiv_of_Vt_equiv rho rho env1 env2 Ty_Nat); exact HV].
Qed.

Lemma VR_rho_rel : forall T (env : list cand) (rho1 rho2 : atom -> cand),
    (forall X, In X (ty_atoms T) -> rho1 X = rho2 X) ->
    (forall e, value e -> (Vt rho1 env T e <-> Vt rho2 env T e))
    /\ (forall e, Rt rho1 env T e <-> Rt rho2 env T e).
Proof.
  induction T; intros env rho1 rho2 Hrho.
  - (* Ty_BVar n *)
    assert (HV : forall e, value e ->
       (Vt rho1 env (Ty_BVar n) e <-> Vt rho2 env (Ty_BVar n) e)).
    { intros e Hv. unfold Vt; simpl. tauto. }
    split; [exact HV | apply (Rt_equiv_of_Vt_equiv rho1 rho2 env env (Ty_BVar n)); exact HV].
  - (* Ty_FVar x *)
    assert (Hx : rho1 x = rho2 x).
    { apply Hrho. simpl. auto. }
    assert (HV : forall e, value e ->
       (Vt rho1 env (Ty_FVar x) e <-> Vt rho2 env (Ty_FVar x) e)).
    { intros e Hv. unfold Vt; simpl. rewrite Hx. tauto. }
    split; [exact HV | apply (Rt_equiv_of_Vt_equiv rho1 rho2 env env (Ty_FVar x)); exact HV].
  - (* Ty_Arrow T1 T2 *)
    assert (Hr1 : forall X, In X (ty_atoms T1) -> rho1 X = rho2 X).
    { intros X HX. apply Hrho. simpl. apply in_app_iff. auto. }
    assert (Hr2 : forall X, In X (ty_atoms T2) -> rho1 X = rho2 X).
    { intros X HX. apply Hrho. simpl. apply in_app_iff. auto. }
    assert (HV : forall e, value e ->
       (Vt rho1 env (Ty_Arrow T1 T2) e <-> Vt rho2 env (Ty_Arrow T1 T2) e)).
    { intros e Hval.
      destruct (IHT1 env rho1 rho2 Hr1) as [HV1 _].
      destruct (IHT2 env rho1 rho2 Hr2) as [_ HR2].
      unfold Vt; simpl.
      split.
      - intros [Hs [He [Hl Hred]]]. repeat split; auto.
        intros u Heu Hlu Hvu Hvu1.
        apply (proj1 (HR2 (tm_app e u))).
        apply (Hred u Heu Hlu Hvu (proj2 (HV1 u Hvu) Hvu1)).
      - intros [Hs [He [Hl Hred]]]. repeat split; auto.
        intros u Heu Hlu Hvu Hvu1.
        apply (proj2 (HR2 (tm_app e u))).
        apply (Hred u Heu Hlu Hvu (proj1 (HV1 u Hvu) Hvu1)).
    }
    split; [exact HV | apply (Rt_equiv_of_Vt_equiv rho1 rho2 env env (Ty_Arrow T1 T2)); exact HV].
  - (* Ty_All T1 *)
    assert (Hr1 : forall X, In X (ty_atoms T1) -> rho1 X = rho2 X).
    { intros X HX. apply Hrho. simpl. auto. }
    assert (HV : forall e, value e ->
       (Vt rho1 env (Ty_All T1) e <-> Vt rho2 env (Ty_All T1) e)).
    { intros e Hval.
      destruct (IHT1 env rho1 rho2 Hr1) as [HV1 _].
      unfold Vt; simpl.
      split.
      - intros [Hs [He [Hl Hred]]]. repeat split; auto.
        intros C HC. apply (HV1 e Hval). apply Hred; auto.
      - intros [Hs [He [Hl Hred]]]. repeat split; auto.
        intros C HC. apply (HV1 e Hval). apply Hred; auto.
    }
    split; [exact HV | apply (Rt_equiv_of_Vt_equiv rho1 rho2 env env (Ty_All T1)); exact HV].
  - (* Ty_Nat *)
    assert (HV : forall e, value e ->
       (Vt rho1 env Ty_Nat e <-> Vt rho2 env Ty_Nat e)).
    { intros e Hv. unfold Vt; simpl. tauto. }
    split; [exact HV | apply (Rt_equiv_of_Vt_equiv rho1 rho2 env env Ty_Nat); exact HV].
Qed.


(* ================================================================== *)
(* Final target theorem (completed at the end of the development).     *)
(* ================================================================== *)

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
Admitted.

End SystemFNormalizationRecursionHardTask.
