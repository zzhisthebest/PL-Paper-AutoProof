(** STLC call-by-value strong-normalization benchmark task. *)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Relations.Relation_Definitions.
From Stdlib Require Import Lia.
Import ListNotations.

Module STLCCBVNormalizationTask.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
      R x y ->
      multi R y z ->
      multi R x z.

(** Language syntax, using locally nameless binders. *)

Definition atom := nat.

Inductive ty : Type :=
  | Ty_Bool : ty
  | Ty_Arrow : ty -> ty -> ty.

Inductive tm : Type :=
  | tm_bvar : nat -> tm
  | tm_fvar : atom -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : ty -> tm -> tm
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm.

Declare Scope stlc_scope.
Delimit Scope stlc_scope with stlc.
Open Scope stlc_scope.

Declare Custom Entry stlc_ty.
Declare Custom Entry stlc_tm.

Notation "<{{ x }}>" := x (x custom stlc_ty).
Notation "x" := x
  (in custom stlc_ty at level 0, x constr at level 0) : stlc_scope.
Notation "'Bool'" := Ty_Bool
  (in custom stlc_ty at level 0) : stlc_scope.
Notation "S -> T" := (Ty_Arrow S T)
  (in custom stlc_ty at level 99, right associativity) : stlc_scope.
Notation "$( t )" := t
  (in custom stlc_ty at level 0, t constr) : stlc_scope.
Notation "( T )" := T
  (in custom stlc_ty at level 0, T custom stlc_ty) : stlc_scope.

Notation "<{ e }>" := e
  (e custom stlc_tm at level 200) : stlc_scope.
Notation "$( x )" := x
  (in custom stlc_tm at level 0, x constr, only parsing) : stlc_scope.
Notation "x" := x
  (in custom stlc_tm at level 0, x constr at level 0) : stlc_scope.
Notation "'bvar' n" := (tm_bvar n)
  (in custom stlc_tm at level 0, n constr at level 0) : stlc_scope.
Notation "'fvar' x" := (tm_fvar x)
  (in custom stlc_tm at level 0, x constr at level 0) : stlc_scope.
Notation "'true'" := tm_true
  (in custom stlc_tm at level 0) : stlc_scope.
Notation "'false'" := tm_false
  (in custom stlc_tm at level 0) : stlc_scope.
Notation "( x )" := x
  (in custom stlc_tm at level 0, x custom stlc_tm) : stlc_scope.
Notation "x y" := (tm_app x y)
  (in custom stlc_tm at level 10, left associativity) : stlc_scope.
Notation "'lambda' ':' T ',' t" := (tm_abs T t)
  (in custom stlc_tm at level 200,
   T custom stlc_ty,
   t custom stlc_tm at level 200,
   left associativity) : stlc_scope.
Notation "'if' t1 'then' t2 'else' t3" :=
  (tm_if t1 t2 t3)
  (in custom stlc_tm at level 200,
   t1 custom stlc_tm,
   t2 custom stlc_tm,
   t3 custom stlc_tm at level 200,
   left associativity) : stlc_scope.

(** Opening and local closure. *)

Fixpoint open_rec (k : nat) (u : tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => if Nat.eqb k i then u else tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_app t1 t2 => tm_app (open_rec k u t1) (open_rec k u t2)
  | tm_abs T t1 => tm_abs T (open_rec (S k) u t1)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 =>
      tm_if (open_rec k u t1) (open_rec k u t2) (open_rec k u t3)
  end.

Definition open (t u : tm) : tm := open_rec 0 u t.

Inductive lc_at : nat -> tm -> Prop :=
  | lc_bvar : forall k i,
      i < k ->
      lc_at k (tm_bvar i)
  | lc_fvar : forall k x,
      lc_at k (tm_fvar x)
  | lc_app : forall k t1 t2,
      lc_at k t1 ->
      lc_at k t2 ->
      lc_at k (tm_app t1 t2)
  | lc_abs : forall k T t1,
      lc_at (S k) t1 ->
      lc_at k (tm_abs T t1)
  | lc_true : forall k,
      lc_at k tm_true
  | lc_false : forall k,
      lc_at k tm_false
  | lc_if : forall k t1 t2 t3,
      lc_at k t1 ->
      lc_at k t2 ->
      lc_at k t3 ->
      lc_at k (tm_if t1 t2 t3).

Definition locally_closed (t : tm) : Prop := lc_at 0 t.

Lemma lc_weaken : forall k t, lc_at k t -> lc_at (S k) t.
Proof.
  intros k t H; induction H; constructor; try assumption; lia.
Qed.

Lemma lc_open_rec : forall k t u,
    lc_at (S k) t -> lc_at k u -> lc_at k (open_rec k u t).
Proof.
  intros k t; revert k; induction t; intros k u Ht Hu; simpl.
  - inversion Ht; subst. destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst; exact Hu.
    + apply lc_bvar. apply Nat.eqb_neq in E; lia.
  - constructor.
  - inversion Ht; subst. constructor; eauto.
  - inversion Ht; subst. constructor. eapply IHt; eauto. apply lc_weaken; exact Hu.
  - constructor.
  - constructor.
  - inversion Ht; subst. constructor; eauto.
Qed.

Lemma open_lc : forall t u,
    lc_at 1 t -> locally_closed u -> locally_closed (open t u).
Proof.
  intros t u Ht Hu; unfold open, locally_closed.
  eapply lc_open_rec; eauto.
Qed.

Lemma lc_open_fvar_inv : forall k t x,
    lc_at k (open_rec k (tm_fvar x) t) -> lc_at (S k) t.
Proof.
  intros k t; revert k; induction t; intros k x H; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply lc_bvar. apply Nat.eqb_eq in E; lia.
    + inversion H; subst. apply lc_bvar. apply Nat.eqb_neq in E; lia.
  - constructor.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor. eapply IHt; eauto.
  - constructor.
  - constructor.
  - inversion H; subst. constructor; eauto.
Qed.

Fixpoint list_max (L : list atom) : nat :=
  match L with
  | nil => 0
  | x :: xs => Nat.max x (list_max xs)
  end.

Lemma in_list_max : forall L x, In x L -> x <= list_max L.
Proof.
  induction L as [|a L IH]; simpl; intros x Hin; [contradiction|].
  destruct Hin as [->|Hin].
  - apply Nat.le_max_l.
  - eapply Nat.le_trans; [eapply IH; eauto|apply Nat.le_max_r].
Qed.

Lemma fresh_atom : forall L : list atom, exists x, ~ In x L.
Proof.
  intros L. exists (S (list_max L)). intro Hin.
  pose proof (in_list_max L (S (list_max L)) Hin); lia.
Qed.

Lemma open_rec_noop : forall m k t u,
    m <= k -> lc_at m t -> open_rec k u t = t.
Proof.
  intros m k t u Hmk Hlc; revert k Hmk.
  induction Hlc; intros j Hmj; simpl.
  - destruct (Nat.eqb j i) eqn:E.
    + apply Nat.eqb_eq in E; lia.
    + reflexivity.
  - reflexivity.
  - rewrite (IHHlc1 j Hmj), (IHHlc2 j Hmj); reflexivity.
  - f_equal. apply IHHlc. lia.
  - reflexivity.
  - reflexivity.
  - rewrite (IHHlc1 j Hmj), (IHHlc2 j Hmj), (IHHlc3 j Hmj); reflexivity.
Qed.


Definition term_subst := atom -> tm.


Fixpoint subst (sigma : term_subst) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_app t1 t2 => tm_app (subst sigma t1) (subst sigma t2)
  | tm_abs T t1 => tm_abs T (subst sigma t1)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (subst sigma t1) (subst sigma t2) (subst sigma t3)
  end.

Lemma subst_open_rec : forall sigma k t u,
    (forall x, locally_closed (sigma x)) ->
    subst sigma (open_rec k u t) = open_rec k (subst sigma u) (subst sigma t).
Proof.
  intros sigma k t; revert k; induction t; intros k u Hclosed; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - unfold locally_closed in Hclosed. rewrite (open_rec_noop 0 k (sigma a) (subst sigma u) (Nat.le_0_l k) (Hclosed a)); reflexivity.
  - rewrite (IHt1 k u Hclosed), (IHt2 k u Hclosed); reflexivity.
  - rewrite (IHt (S k) u Hclosed); reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite (IHt1 k u Hclosed), (IHt2 k u Hclosed), (IHt3 k u Hclosed); reflexivity.
Qed.

Lemma subst_open_fvar : forall sigma x t,
    (forall y, locally_closed (sigma y)) ->
    subst sigma (open t (tm_fvar x)) = open (subst sigma t) (sigma x).
Proof.
  intros sigma x t Hclosed; unfold open; rewrite subst_open_rec by exact Hclosed.
  simpl; reflexivity.
Qed.

Definition subst_update (sigma : term_subst) (x : atom) (u : tm) : term_subst :=
  fun y => if Nat.eqb y x then u else sigma y.

Fixpoint fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_app t1 t2 => fv t1 ++ fv t2
  | tm_abs _ t1 => fv t1
  | tm_true | tm_false => []
  | tm_if t1 t2 t3 => fv t1 ++ fv t2 ++ fv t3
  end.

Lemma subst_update_fresh : forall sigma x u t,
    ~ In x (fv t) -> subst (subst_update sigma x u) t = subst sigma t.
Proof.
  intros sigma x u t; induction t; simpl; intros Hfresh; try reflexivity.
  - destruct (Nat.eqb a x) eqn:E.
    + apply Nat.eqb_eq in E; subst. exfalso; apply Hfresh; simpl; auto.
    + unfold subst_update; simpl; rewrite E; reflexivity.
  - assert (H1 : ~ In x (fv t1)) by (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (H2 : ~ In x (fv t2)) by (intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
    rewrite (IHt1 H1), (IHt2 H2); reflexivity.
  - rewrite IHt; [reflexivity|exact Hfresh].
  - rewrite IHt1, IHt2, IHt3; try reflexivity.
    + intro Hin; apply Hfresh; apply in_or_app; right; apply in_or_app; right; exact Hin.
    + intro Hin; apply Hfresh; apply in_or_app; right; apply in_or_app; left; exact Hin.
    + intro Hin; apply Hfresh; apply in_or_app; left; exact Hin.
Qed.

Lemma subst_open_update : forall sigma x u t,
    (forall y, locally_closed (sigma y)) -> locally_closed u ->
    ~ In x (fv t) ->
    subst (subst_update sigma x u) (open t (tm_fvar x)) = open (subst sigma t) u.
Proof.
  intros sigma x u t Hclosed Hu Hfresh. rewrite subst_open_fvar.
  - rewrite subst_update_fresh by exact Hfresh.
    unfold subst_update; rewrite Nat.eqb_refl; reflexivity.
  - intro y; unfold subst_update; destruct (Nat.eqb y x); [exact Hu|apply Hclosed].
Qed.

Lemma lc_at_weaken_many : forall k t, locally_closed t -> lc_at k t.
Proof.
  induction k; intros t H; [exact H|apply lc_weaken; apply IHk; exact H].
Qed.

Lemma subst_preserves_lc : forall k t,
    lc_at k t -> forall sigma, (forall x, locally_closed (sigma x)) ->
      lc_at k (subst sigma t).
Proof.
  intros k t Hlc; induction Hlc; intros sigma Hsigma; simpl.
  - constructor; assumption.
  - apply lc_at_weaken_many; apply Hsigma.
  - constructor; eauto.
  - constructor; eauto.
  - constructor.
  - constructor.
  - constructor; eauto.
Qed.


(** Call-by-value operational semantics. *)

Inductive value : tm -> Prop :=
  | v_abs : forall T t,
      locally_closed (tm_abs T t) ->
      value (tm_abs T t)
  | v_true :
      value tm_true
  | v_false :
      value tm_false.

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall T t v,
      locally_closed (tm_abs T t) ->
      value v ->
      tm_app (tm_abs T t) v --> open t v
  | ST_App1 : forall t1 t1' t2,
      t1 --> t1' ->
      locally_closed t2 ->
      tm_app t1 t2 --> tm_app t1' t2
  | ST_App2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      tm_app v1 t2 --> tm_app v1 t2'
  | ST_IfTrue : forall t1 t2,
      locally_closed t1 ->
      locally_closed t2 ->
      tm_if tm_true t1 t2 --> t1
  | ST_IfFalse : forall t1 t2,
      locally_closed t1 ->
      locally_closed t2 ->
      tm_if tm_false t1 t2 --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      locally_closed t2 ->
      locally_closed t3 ->
      tm_if t1 t2 t3 --> tm_if t1' t2 t3
where "t '-->' t'" := (step t t').

Lemma value_lc : forall v, value v -> locally_closed v.
Proof. intros v H; inversion H; subst; assumption || constructor. Qed.

Lemma lc_step : forall t t', locally_closed t -> t --> t' -> locally_closed t'.
Proof.
  intros t t' Hlc Hstep; induction Hstep.
  - inversion Hlc; subst. eapply open_lc; [inversion H; assumption|eapply value_lc; eassumption].
  - inversion Hlc; subst. apply lc_app; [eapply IHHstep; eassumption|assumption].
  - inversion Hlc; subst. apply lc_app; [assumption|eapply IHHstep; eassumption].
  - assumption.
  - assumption.
  - inversion Hlc; subst. apply lc_if; [eapply IHHstep; eassumption|assumption|assumption].
Qed.

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

(** Typing rules. *)

Definition context := atom -> option ty.

Definition empty : context := fun _ => None.

Definition update (Gamma : context) (x : atom) (T : ty) : context :=
  fun y => if Nat.eqb x y then Some T else Gamma y.

Notation "x '|->' v ';' m" := (update m x v)
  (in custom stlc_tm at level 0,
   x constr at level 0,
   v custom stlc_ty,
   right associativity) : stlc_scope.
Notation "x '|->' v" := (update empty x v)
  (in custom stlc_tm at level 0,
   x constr at level 0,
   v custom stlc_ty) : stlc_scope.
Notation "'empty'" := empty
  (in custom stlc_tm) : stlc_scope.

Reserved Notation "<{ Gamma '|--' t '\in' T }>"
  (at level 0,
   Gamma custom stlc_tm at level 200,
   t custom stlc_tm,
   T custom stlc_ty).

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      <{ Gamma |-- fvar x \in T }>
  | T_Abs : forall (L : list atom) Gamma T1 T2 t1,
      (forall x, ~ In x L ->
        <{ x |-> T1 ; Gamma |-- $(open t1 (tm_fvar x)) \in T2 }>) ->
      <{ Gamma |-- lambda : T1, $(t1) \in T1 -> T2 }>
  | T_App : forall Gamma t1 t2 T1 T2,
      <{ Gamma |-- $(t1) \in T1 -> T2 }> ->
      <{ Gamma |-- $(t2) \in T1 }> ->
      <{ Gamma |-- $(tm_app t1 t2) \in T2 }>
  | T_True : forall Gamma,
      <{ Gamma |-- true \in Bool }>
  | T_False : forall Gamma,
      <{ Gamma |-- false \in Bool }>
  | T_If : forall Gamma t1 t2 t3 T,
      <{ Gamma |-- $(t1) \in Bool }> ->
      <{ Gamma |-- $(t2) \in T }> ->
      <{ Gamma |-- $(t3) \in T }> ->
      <{ Gamma |-- $(tm_if t1 t2 t3) \in T }>
where "<{ Gamma '|--' t '\in' T }>" := (has_type Gamma t T)
  : stlc_scope.

Lemma typing_lc : forall Gamma t T, has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T Hty.
  induction Hty as
    [Gamma x T Hlookup
    |L Gamma T1 T2 t1 Hbody IHbody
    |Gamma t1 t2 T1 T2 Hfun IHfun Harg IHarg
    |Gamma
    |Gamma
    |Gamma t1 t2 t3 T Hcond IHcond Hthen IHthen Helse IHelse].
  - constructor.
  - destruct (fresh_atom L) as [x Hx].
    pose proof (IHbody x Hx) as Hlcopen.
    apply lc_open_fvar_inv in Hlcopen.
    exact (lc_abs 0 T1 t1 Hlcopen).
  - constructor; assumption.
  - constructor.
  - constructor.
  - constructor; assumption.
Qed.


(** Target theorem: strong normalization for the supplied CBV relation. *)

Inductive strongly_normalizing : tm -> Prop :=
  | SN_intro : forall t,
      (forall t', t --> t' -> strongly_normalizing t') ->
      strongly_normalizing t.

(* Unary computability predicate.  At function types it asks that applying
   the term to any computable argument is computable at the result type. *)
Fixpoint computable (T : ty) (t : tm) : Prop :=
  match T with
  | Ty_Bool => locally_closed t /\ strongly_normalizing t
  | Ty_Arrow A B =>
      locally_closed t /\ strongly_normalizing t /\
      (forall u, computable A u -> computable B (tm_app t u))
  end.

Lemma computable_lc : forall T t, computable T t -> locally_closed t.
Proof. intros T t H; destruct T; simpl in H; tauto. Qed.

Lemma computable_sn : forall T t, computable T t -> strongly_normalizing t.
Proof. intros T t H; destruct T; simpl in H; tauto. Qed.

Lemma sn_step : forall t t', strongly_normalizing t -> t --> t' -> strongly_normalizing t'.
Proof. intros t t' Hsn Hstep; inversion Hsn; eauto. Qed.

Lemma sn_no_step : forall t, (forall t', ~ t --> t') -> strongly_normalizing t.
Proof. intros t H; constructor; intros t' Hs; exfalso; eapply H; eauto. Qed.

Lemma sn_abs : forall T t, locally_closed (tm_abs T t) -> strongly_normalizing (tm_abs T t).
Proof. intros T t Hlc; apply sn_no_step; intros t' Hstep; inversion Hstep. Qed.

Lemma sn_true : strongly_normalizing tm_true.
Proof. apply sn_no_step; intros t H; inversion H. Qed.

Lemma sn_false : strongly_normalizing tm_false.
Proof. apply sn_no_step; intros t H; inversion H. Qed.

Lemma computable_step : forall T t t',
    computable T t -> t --> t' -> computable T t'.
Proof.
  induction T as [|A IHA B IHB]; intros t t' Hcomp Hstep; simpl in *.
  - destruct Hcomp as [Hlc Hsn]. split; [eapply lc_step|eapply sn_step]; eauto.
  - destruct Hcomp as [Hlc [Hsn Happ]].
    split.
    + eapply lc_step; eauto.
    + split.
      * eapply sn_step; eauto.
      * intros u Hu. specialize (Happ u Hu).
        eapply IHB; [exact Happ|]. apply ST_App1; [exact Hstep|apply computable_lc with A; exact Hu].
Qed.

Lemma computable_expand_nonvalue : forall T t,
    locally_closed t -> ~ value t ->
    (forall t', t --> t' -> computable T t') -> computable T t.
Proof.
  induction T as [|A IHA B IHB]; intros t Hlc Hnv Hred; simpl.
  - split; [exact Hlc|]. constructor. intros t' Hstep. apply (Hred t' Hstep).
  - split; [exact Hlc|]. split.
    + constructor. intros t' Hstep. destruct (Hred t' Hstep) as [_ [Hsn _]]. exact Hsn.
    + intros u Hu. eapply IHB.
      * apply lc_app; [exact Hlc|apply computable_lc with A; exact Hu].
      * intro Hv; inversion Hv.
      * intros r Hstep.
        inversion Hstep; subst.
        -- exfalso; apply Hnv. apply v_abs; assumption.
        -- destruct (Hred t1' ltac:(eassumption)) as [_ [_ Happ]]. apply Happ; exact Hu.
        -- exfalso; apply Hnv; assumption.
Qed.

Lemma computable_abs_app : forall A B T body,
    locally_closed (tm_abs T body) ->
    (forall u, computable A u -> computable B (open body u)) ->
    forall u, strongly_normalizing u -> computable A u ->
      computable B (tm_app (tm_abs T body) u).
Proof.
  intros A B T body Habs Hbody u Hsn Hu.
  revert Hu. induction Hsn as [u Hnext IH]. intros Hu.
  eapply computable_expand_nonvalue.
  - apply lc_app; [exact Habs|apply computable_lc with A; exact Hu].
  - intro Hv; inversion Hv.
  - intros r Hstep. inversion Hstep; subst.
    + apply Hbody; exact Hu.
    + inversion H1.
    + eapply IH.
      * eassumption.
      * eapply computable_step; eassumption.
Qed.

Lemma computable_if : forall T c t1 t2,
    computable Ty_Bool c -> computable T t1 -> computable T t2 ->
    computable T (tm_if c t1 t2).
Proof.
  intros T c t1 t2 Hc Hthen Helse.
  destruct Hc as [Hclc Hsn]. revert Hclc.
  induction Hsn as [c Hnext IH]; intros Hclc.
  eapply computable_expand_nonvalue.
  - apply lc_if; [exact Hclc|apply computable_lc with T; exact Hthen|apply computable_lc with T; exact Helse].
  - intro Hv; inversion Hv.
  - intros r Hstep. inversion Hstep; subst.
    + exact Hthen.
    + exact Helse.
    + eapply IH.
      * exact H2.
      * apply computable_lc with Ty_Bool.
        eapply computable_step; [split; [exact Hclc|exact (SN_intro c Hnext)]|exact H2].
Qed.

Definition env_ok (Gamma : context) (sigma : term_subst) : Prop :=
  (forall y, locally_closed (sigma y)) /\
  (forall x T, Gamma x = Some T -> computable T (sigma x)).

Lemma env_ok_update : forall Gamma sigma x A u,
    env_ok Gamma sigma -> computable A u ->
    env_ok (update Gamma x A) (subst_update sigma x u).
Proof.
  intros Gamma sigma x A u [Hclosed Henv] Hu. split.
  - intros y. unfold subst_update. destruct (Nat.eqb y x); [apply computable_lc with A; exact Hu|apply Hclosed].
  - intros y T Hlookup. unfold update in Hlookup. unfold subst_update.
    destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E; subst y. simpl in Hlookup. inversion Hlookup; subst T.
      rewrite Nat.eqb_refl; exact Hu.
    + assert (E' : Nat.eqb y x = false).
      { apply Nat.eqb_neq; intro Heq; apply Nat.eqb_neq in E; apply E; symmetry; exact Heq. }
      rewrite E'. eapply Henv; exact Hlookup.
Qed.

Lemma fresh_for_abs : forall L t, exists x, ~ In x L /\ ~ In x (fv t).
Proof.
  intros L t. destruct (fresh_atom (L ++ fv t)) as [x Hx]. exists x; split.
  - intro Hin; apply Hx; apply in_or_app; left; exact Hin.
  - intro Hin; apply Hx; apply in_or_app; right; exact Hin.
Qed.

Lemma fundamental : forall Gamma t T,
    has_type Gamma t T -> forall sigma, env_ok Gamma sigma ->
      computable T (subst sigma t).
Proof.
  intros Gamma t T Hty.
  induction Hty as
    [Gamma x T Hlookup
    |L Gamma T1 T2 t1 Hbody IHbody
    |Gamma t1 t2 T1 T2 Hfun IHfun Harg IHarg
    |Gamma
    |Gamma
    |Gamma t1 t2 t3 T Hcond IHcond Hthen IHthen Helse IHelse];
    intros sigma Henv; simpl.
  - destruct Henv as [_ Hrel]. eapply Hrel; eassumption.
  - destruct Henv as [Hclosed Hrel].
    assert (Hbody_lc : lc_at 1 t1).
    { destruct (fresh_atom L) as [x Hx].
      apply lc_open_fvar_inv with (x:=x).
      eapply typing_lc. apply Hbody; exact Hx. }
    assert (Habs_lc : locally_closed (tm_abs T1 (subst sigma t1))).
    { unfold locally_closed. apply lc_abs. eapply subst_preserves_lc; eauto. }
    split; [exact Habs_lc|]. split; [apply sn_abs; exact Habs_lc|].
    intros u Hu.
    assert (HbodyAll : forall u0, computable T1 u0 ->
        computable T2 (open (subst sigma t1) u0)).
    { intros u0 Hu0. destruct (fresh_for_abs L t1) as [x [HxL HxFV]].
      pose proof (IHbody x HxL (subst_update sigma x u0)
        (env_ok_update Gamma sigma x T1 u0 (conj Hclosed Hrel) Hu0)) as Hinst.
      rewrite <- (subst_open_update sigma x u0 t1 Hclosed
        (computable_lc T1 u0 Hu0) HxFV); exact Hinst. }
    exact (computable_abs_app T1 T2 T1 (subst sigma t1) Habs_lc HbodyAll
      u (computable_sn T1 u Hu) Hu).
  - destruct (IHfun sigma Henv) as [_ [_ Happly]].
    apply Happly. apply IHarg; exact Henv.
  - split; [constructor|apply sn_true].
  - split; [constructor|apply sn_false].
  - eapply computable_if; [apply IHcond|apply IHthen|apply IHelse]; exact Henv.
Qed.

Lemma subst_identity : forall t,
    subst (fun x => tm_fvar x) t = t.
Proof. intros t; induction t; simpl; try rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3; reflexivity. Qed.


Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  pose proof (fundamental empty t T Hty (fun x => tm_fvar x)) as Hfund.
  assert (Henv : env_ok empty (fun x => tm_fvar x)).
  { split; [intro x; constructor|]. intros x U Hlookup; discriminate. }
  specialize (Hfund Henv).
  rewrite subst_identity in Hfund.
  apply computable_sn with T; exact Hfund.
Qed.

End STLCCBVNormalizationTask.
