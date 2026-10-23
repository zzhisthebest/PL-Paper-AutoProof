(** STLC call-by-value strong-normalization benchmark task. *)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Relations.Relation_Definitions.
From Stdlib Require Import Lia.

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

(** Target theorem: strong normalization for the supplied CBV relation. *)

Inductive strongly_normalizing : tm -> Prop :=
  | SN_intro : forall t,
      (forall t', t --> t' -> strongly_normalizing t') ->
      strongly_normalizing t.

(** ** Auxiliary definitions for the logical relation. *)

(** Free-variable substitution.  In the locally nameless representation,
    [fvars] are the free variables and [bvars] are the bound ones, so
    substitution acts on [fvars] and leaves [bvars] untouched. *)

Fixpoint subst (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_app t1 t2 => tm_app (subst sigma t1) (subst sigma t2)
  | tm_abs T t1 => tm_abs T (subst sigma t1)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (subst sigma t1) (subst sigma t2) (subst sigma t3)
  end.

(** Free variables of a term. *)

Fixpoint fvs (t : tm) : list atom :=
  match t with
  | tm_bvar _ => nil
  | tm_fvar x => x :: nil
  | tm_app t1 t2 => fvs t1 ++ fvs t2
  | tm_abs _ t1 => fvs t1
  | tm_true => nil
  | tm_false => nil
  | tm_if t1 t2 t3 => fvs t1 ++ fvs t2 ++ fvs t3
  end.

(** The unary, type-indexed logical relation.  At every type we require
    strong normalization and local closure; at arrow types we also
    require that application to any related value is related. *)

Fixpoint sem (T : ty) (t : tm) : Prop :=
  match T with
  | Ty_Bool => strongly_normalizing t /\ locally_closed t
  | Ty_Arrow T1 T2 =>
      strongly_normalizing t /\ locally_closed t /\
      (forall v, value v -> sem T1 v -> sem T2 (tm_app t v))
  end.

(** Interpretations of term-variable contexts and substitutions. *)

Definition env_lc (sigma : atom -> tm) : Prop :=
  forall x, locally_closed (sigma x).

Definition env_rel (Gamma : context) (sigma : atom -> tm) : Prop :=
  forall x T, Gamma x = Some T -> sem T (sigma x).

(** ** Fresh atoms. *)

Fixpoint max_list (L : list nat) : nat :=
  match L with
  | nil => 0
  | a :: L' => Nat.max a (max_list L')
  end.

Lemma in_max_list : forall L a, In a L -> a <= max_list L.
Proof.
  induction L as [| b L IH]; intros a Hin.
  - inversion Hin.
  - simpl in Hin. simpl. destruct Hin as [-> | Hin].
    + apply Nat.le_max_l.
    + apply Nat.le_trans with (max_list L);
        [apply IH; exact Hin | apply Nat.le_max_r].
Qed.

Lemma fresh_atom : forall L : list atom, exists x, ~ In x L.
Proof.
  intros L. exists (S (max_list L)). intros Hin.
  pose proof (in_max_list L (S (max_list L)) Hin). lia.
Qed.

(** ** Elementary properties of local closure. *)

Lemma lc_at_S : forall k t, lc_at k t -> lc_at (S k) t.
Proof.
  intros k t H. induction H.
  - apply lc_bvar. lia.
  - apply lc_fvar.
  - apply lc_app; assumption.
  - apply lc_abs. assumption.
  - apply lc_true.
  - apply lc_false.
  - apply lc_if; assumption.
Qed.

Lemma lc_at_mono : forall k k' t, k <= k' -> lc_at k t -> lc_at k' t.
Proof.
  intros k k' t Hle Ht. induction Hle.
  - exact Ht.
  - apply lc_at_S. exact IHHle.
Qed.

Lemma locally_closed_lc_at : forall t k, locally_closed t -> lc_at k t.
Proof.
  intros t k H. apply (lc_at_mono 0 k t); [apply Nat.le_0_l | exact H].
Qed.

Lemma lc_bvar_inv : forall k i, lc_at k (tm_bvar i) -> i < k.
Proof. intros k i H. inversion H. assumption. Qed.

Lemma lc_fvar_inv : forall k x, lc_at k (tm_fvar x) -> True.
Proof. intros. exact I. Qed.

Lemma lc_app_inv : forall k t1 t2,
  lc_at k (tm_app t1 t2) -> lc_at k t1 /\ lc_at k t2.
Proof. intros k t1 t2 H. inversion H. split; assumption. Qed.

Lemma lc_abs_inv : forall k T t1,
  lc_at k (tm_abs T t1) -> lc_at (S k) t1.
Proof. intros k T t1 H. inversion H. assumption. Qed.

Lemma lc_if_inv : forall k t1 t2 t3,
  lc_at k (tm_if t1 t2 t3) -> lc_at k t1 /\ lc_at k t2 /\ lc_at k t3.
Proof. intros k t1 t2 t3 H. inversion H. repeat split; assumption. Qed.

(** Opening a locally closed term with a locally closed argument
    preserves local closure, and conversely. *)

Lemma open_rec_lc : forall t k u, lc_at k t -> open_rec k u t = t.
Proof.
  induction t as [n | a | t1 IH1 t2 IH2 | T t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
    intros k u H; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. apply lc_bvar_inv in H. lia.
    + reflexivity.
  - reflexivity.
  - destruct (lc_app_inv k t1 t2 H) as [H1 H2].
    rewrite (IH1 k u H1), (IH2 k u H2). reflexivity.
  - rewrite (IH1 (S k) u (lc_abs_inv k T t1 H)). reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct (lc_if_inv k t1 t2 t3 H) as [H1 [H2 H3]].
    rewrite (IH1 k u H1), (IH2 k u H2), (IH3 k u H3). reflexivity.
Qed.

Lemma lc_open_rec : forall t k u,
  lc_at (S k) t -> lc_at k u -> lc_at k (open_rec k u t).
Proof.
  induction t as [n | a | t1 IH1 t2 IH2 | T t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
    intros k u Ht Hu; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. exact Hu.
    + apply Nat.eqb_neq in E.
      apply lc_bvar. apply lc_bvar_inv in Ht. lia.
  - apply lc_fvar.
  - destruct (lc_app_inv (S k) t1 t2 Ht) as [H1 H2].
    apply lc_app; [apply (IH1 k u H1 Hu) | apply (IH2 k u H2 Hu)].
  - apply lc_abs. apply (IH1 (S k) u (lc_abs_inv (S k) T t1 Ht) (lc_at_S k u Hu)).
  - apply lc_true.
  - apply lc_false.
  - destruct (lc_if_inv (S k) t1 t2 t3 Ht) as [H1 [H2 H3]].
    apply lc_if; [apply (IH1 k u H1 Hu) | apply (IH2 k u H2 Hu) | apply (IH3 k u H3 Hu)].
Qed.

Lemma lc_open_rec_inv : forall t k u,
  lc_at k (open_rec k u t) -> lc_at k u -> lc_at (S k) t.
Proof.
  induction t as [n | a | t1 IH1 t2 IH2 | T t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
    intros k u Hopen Hu; simpl in Hopen.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. apply lc_bvar. lia.
    + apply lc_bvar. apply lc_bvar_inv in Hopen. lia.
  - apply lc_fvar.
  - destruct (lc_app_inv k (open_rec k u t1) (open_rec k u t2) Hopen) as [H1 H2].
    apply lc_app; [apply (IH1 k u H1 Hu) | apply (IH2 k u H2 Hu)].
  - apply lc_abs.
    apply (IH1 (S k) u (lc_abs_inv k T (open_rec (S k) u t1) Hopen) (lc_at_S k u Hu)).
  - apply lc_true.
  - apply lc_false.
  - destruct (lc_if_inv k (open_rec k u t1) (open_rec k u t2) (open_rec k u t3)
                Hopen) as [H1 [H2 H3]].
    apply lc_if; [apply (IH1 k u H1 Hu) | apply (IH2 k u H2 Hu) | apply (IH3 k u H3 Hu)].
Qed.

(** ** Interaction of substitution and opening. *)

Lemma subst_id : forall t, subst (fun x => tm_fvar x) t = t.
Proof. induction t; simpl; congruence. Qed.

Lemma subst_open_rec : forall t k sigma v x,
  (forall y, locally_closed (sigma y)) ->
  ~ In x (fvs t) ->
  subst (fun y => if Nat.eqb x y then v else sigma y) (open_rec k (tm_fvar x) t)
  = open_rec k v (subst sigma t).
Proof.
  induction t as [n | a | t1 IH1 t2 IH2 | T t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
    intros k sigma v x Hlc Hfresh; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n.
      simpl. repeat rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - simpl in Hfresh. destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E. subst a. exfalso. apply Hfresh. simpl. auto.
    + rewrite (open_rec_lc (sigma a) k v (locally_closed_lc_at (sigma a) k (Hlc a))).
      reflexivity.
  - simpl in Hfresh. rewrite in_app_iff in Hfresh.
    assert (Hf1 : ~ In x (fvs t1)) by (intro H; apply Hfresh; left; exact H).
    assert (Hf2 : ~ In x (fvs t2)) by (intro H; apply Hfresh; right; exact H).
    rewrite (IH1 k sigma v x Hlc Hf1), (IH2 k sigma v x Hlc Hf2). reflexivity.
  - rewrite (IH1 (S k) sigma v x Hlc Hfresh). reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl in Hfresh. rewrite in_app_iff in Hfresh. rewrite in_app_iff in Hfresh.
    assert (Hf1 : ~ In x (fvs t1)) by (intro H; apply Hfresh; left; exact H).
    assert (Hf2 : ~ In x (fvs t2)) by (intro H; apply Hfresh; right; left; exact H).
    assert (Hf3 : ~ In x (fvs t3)) by (intro H; apply Hfresh; right; right; exact H).
    rewrite (IH1 k sigma v x Hlc Hf1), (IH2 k sigma v x Hlc Hf2),
            (IH3 k sigma v x Hlc Hf3). reflexivity.
Qed.

(** ** Basic facts about values and strong normalization. *)

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v H. destruct H as [T t Hlc | | ].
  - exact Hlc.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma value_no_step : forall v v', value v -> ~ step v v'.
Proof.
  intros v v' Hv Hst. destruct Hv as [T t Hlc | | ]; inversion Hst.
Qed.

Lemma abs_no_step : forall T t u, ~ step (tm_abs T t) u.
Proof. intros T t u H. inversion H. Qed.

Lemma SN_abs : forall T t, strongly_normalizing (tm_abs T t).
Proof. intros T t. apply SN_intro. intros u H. inversion H. Qed.

Lemma SN_true : strongly_normalizing tm_true.
Proof. apply SN_intro. intros u H. inversion H. Qed.

Lemma SN_false : strongly_normalizing tm_false.
Proof. apply SN_intro. intros u H. inversion H. Qed.

Lemma SN_fvar : forall x, strongly_normalizing (tm_fvar x).
Proof. intros x. apply SN_intro. intros u H. inversion H. Qed.

Lemma SN_step : forall t t',
  strongly_normalizing t -> step t t' -> strongly_normalizing t'.
Proof.
  intros t t' H Hst. destruct H as [t0 Hred]. apply (Hred t' Hst).
Qed.

(** Steps preserve local closure. *)

Lemma step_lc : forall t t', step t t' -> locally_closed t -> locally_closed t'.
Proof.
  intros t t' H.
  induction H as [T t v Hlcabs Hval
                 | t1 t1' t2 Hstep IH Hlc2
                 | v1 t2 t2' Hval Hstep IH
                 | t1 t2 Hlc1 Hlc2
                 | t1 t2 Hlc1 Hlc2
                 | t1 t1' t2 t3 Hstep IH Hlc2 Hlc3];
    intros Hlc.
  - (* ST_AppAbs *)
    destruct (lc_app_inv 0 (tm_abs T t) v Hlc) as [H1 H2].
    apply lc_open_rec.
    + apply lc_abs_inv in H1. exact H1.
    + apply value_lc. assumption.
  - (* ST_App1 *)
    destruct (lc_app_inv 0 t1 t2 Hlc) as [H1 H2].
    apply lc_app; [apply IH; exact H1 | exact H2].
  - (* ST_App2 *)
    destruct (lc_app_inv 0 v1 t2 Hlc) as [H1 H2].
    apply lc_app; [apply value_lc; assumption | apply IH; exact H2].
  - (* ST_IfTrue *) assumption.
  - (* ST_IfFalse *) assumption.
  - (* ST_If *)
    destruct (lc_if_inv 0 t1 t2 t3 Hlc) as [H1 [H2 H3]].
    apply lc_if; [apply IH; exact H1 | exact H2 | exact H3].
Qed.

(** ** Projections of the logical relation. *)

Lemma sem_sn : forall T t, sem T t -> strongly_normalizing t.
Proof.
  intros T t H. destruct T as [| T1 T2]; simpl in H; apply (proj1 H).
Qed.

Lemma sem_lc : forall T t, sem T t -> locally_closed t.
Proof.
  intros T t H. destruct T as [| T1 T2]; simpl in H.
  - apply (proj2 H).
  - apply (proj1 (proj2 H)).
Qed.

Lemma sem_app_clause : forall T1 T2 t,
  sem (Ty_Arrow T1 T2) t ->
  forall v, value v -> sem T1 v -> sem T2 (tm_app t v).
Proof.
  intros T1 T2 t H. simpl in H. apply (proj2 (proj2 H)).
Qed.

(** The logical relation is closed under reduction. *)

Lemma sem_step : forall T t t', sem T t -> step t t' -> sem T t'.
Proof.
  induction T as [| T1 IH1 T2 IH2]; intros t t' Hsem Hst.
  - destruct Hsem as [Hsn Hlc]. split.
    + apply (SN_step t t'); assumption.
    + apply (step_lc t t'); assumption.
  - destruct Hsem as [Hsn [Hlc Happ]]. split; [| split].
    + apply (SN_step t t'); assumption.
    + apply (step_lc t t'); assumption.
    + intros v Hv Hsemv.
      apply (IH2 (tm_app t v) (tm_app t' v)).
      * apply Happ; assumption.
      * apply ST_App1; [exact Hst | apply value_lc; exact Hv].
Qed.

(** Expansion for terms that are not values: if every one-step reduct
    is in the relation, then so is the term itself. *)

Lemma sem_expand : forall T t,
  ~ value t ->
  locally_closed t ->
  (forall t', step t t' -> sem T t') ->
  sem T t.
Proof.
  induction T as [| T1 IH1 T2 IH2]; intros t Hnv Hlc Hred.
  - split.
    + apply SN_intro. intros t' Hst.
      apply (sem_sn Ty_Bool t'). apply Hred. exact Hst.
    + exact Hlc.
  - split; [| split].
    + apply SN_intro. intros t' Hst.
      apply (sem_sn (Ty_Arrow T1 T2) t'). apply Hred. exact Hst.
    + exact Hlc.
    + intros v Hv Hsemv.
      apply (IH2 (tm_app t v)).
      * intro Hvapp. inversion Hvapp.
      * apply lc_app.
        -- exact Hlc.
        -- apply sem_lc with (T := T1). exact Hsemv.
      * intros t' Hst.
        inversion Hst as [T0 t0 v0 Hlcabs Hval
                        | a1 a1' a2 Hstep Hlc2
                        | b1 b2 b2' Hval Hstep
                        | i1 i2 Hc1 Hc2
                        | i1 i2 Hc1 Hc2
                        | i1 i1' i2 i3 Hs Hc2 Hc3]; subst.
        -- (* ST_AppAbs: impossible, since [t] would then be a value *)
           exfalso. apply Hnv. apply v_abs. exact Hlc.
        -- (* ST_App1 *)
           destruct (Hred a1' Hstep) as [Hsn [Hlc' Happ]].
           apply (Happ v Hv Hsemv).
        -- (* ST_App2: the function part is a value, contradicting [Hnv] *)
           exfalso. apply Hnv. exact Hval.
Qed.

(** Shape of values, used to split the application lemma. *)

Inductive val_shape : tm -> Prop :=
  | vs_abs : forall T t, val_shape (tm_abs T t)
  | vs_true : val_shape tm_true
  | vs_false : val_shape tm_false.

Lemma val_shape_dec : forall t, val_shape t \/ ~ val_shape t.
Proof.
  intros t. destruct t as [n | a | t1 t2 | T t1 | | | t1 t2 t3].
  - right. intro H. inversion H.
  - right. intro H. inversion H.
  - right. intro H. inversion H.
  - left. constructor.
  - left. constructor.
  - left. constructor.
  - right. intro H. inversion H.
Qed.

Lemma value_val_shape : forall t, value t -> val_shape t.
Proof. intros t H. destruct H as [T t0 Hlc | | ]; constructor. Qed.

Lemma val_shape_value : forall t, val_shape t -> locally_closed t -> value t.
Proof.
  intros t H Hlc. destruct H as [T t0 | | ].
  - apply v_abs. exact Hlc.
  - apply v_true.
  - apply v_false.
Qed.

(** Application: if [t] is related at an arrow type and [u] at the
    domain, then [t u] is related at the codomain.  Proven by a double
    induction on the strong normalization derivations. *)

Lemma sem_app_aux : forall t, strongly_normalizing t ->
  forall u, strongly_normalizing u ->
  forall T1 T2,
    sem (Ty_Arrow T1 T2) t -> sem T1 u -> sem T2 (tm_app t u).
Proof.
  intros t Hsn_t.
  induction Hsn_t as [t Hred_t IH_t].
  intros u Hsn_u.
  induction Hsn_u as [u Hred_u IH_u].
  intros T1 T2 Hsem_t Hsem_u.
  destruct (val_shape_dec u) as [Hshape | Hnshape].
  - (* [u] is a value: use the arrow clause directly. *)
    apply (sem_app_clause T1 T2 t Hsem_t u).
    + apply val_shape_value.
      * exact Hshape.
      * apply sem_lc with (T := T1). exact Hsem_u.
    + exact Hsem_u.
  - (* [u] is not a value: expand at the codomain. *)
    apply (sem_expand T2 (tm_app t u)).
    + intro Hv. inversion Hv.
    + apply lc_app.
      * apply sem_lc with (T := Ty_Arrow T1 T2). exact Hsem_t.
      * apply sem_lc with (T := T1). exact Hsem_u.
    + intros t' Hst.
      inversion Hst as [T0 t0 v0 Hlcabs Hval
                      | a1 a1' a2 Hstep Hlc2
                      | b1 b2 b2' Hval Hstep
                      | i1 i2 Hc1 Hc2
                      | i1 i2 Hc1 Hc2
                      | i1 i1' i2 i3 Hs Hc2 Hc3]; subst.
      * (* ST_AppAbs: [u] would be a value *)
        exfalso. apply Hnshape. apply value_val_shape. exact Hval.
      * (* ST_App1: the function steps *)
        apply (IH_t a1' Hstep u (sem_sn T1 u Hsem_u) T1 T2).
        -- apply (sem_step (Ty_Arrow T1 T2) t a1'). assumption. exact Hstep.
        -- exact Hsem_u.
      * (* ST_App2: the argument steps *)
        apply (IH_u b2' Hstep T1 T2 Hsem_t).
        apply (sem_step T1 u b2'). exact Hsem_u. exact Hstep.
Qed.

(** If-then-else respects the relation, by induction on the strong
    normalization derivation of the condition. *)

Lemma sem_if : forall b1, strongly_normalizing b1 ->
  forall T b2 b3,
    locally_closed b1 -> sem T b2 -> sem T b3 ->
    locally_closed b2 -> locally_closed b3 ->
    sem T (tm_if b1 b2 b3).
Proof.
  intros b1 Hsn. induction Hsn as [b1 Hred IH].
  intros T b2 b3 Hlc1 Hsem2 Hsem3 Hlc2 Hlc3.
  apply (sem_expand T (tm_if b1 b2 b3)).
  - intro Hv. inversion Hv.
  - apply lc_if; assumption.
  - intros t' Hst.
    inversion Hst as [T0 t0 v0 Hc0 Hv0
                    | a1 a1' a2 Hs Hc
                    | c1 c2 c3 Hv' Hs
                    | t1 t2 Hlc1' Hlc2'
                    | t1 t2 Hlc1' Hlc2'
                    | t1 t1' t2 t3 Hstep Hlc2' Hlc3']; subst.
    + exact Hsem2.
    + exact Hsem3.
    + apply (IH t1' Hstep T b2 b3).
      * apply (step_lc b1 t1'). exact Hstep. exact Hlc1.
      * exact Hsem2.
      * exact Hsem3.
      * exact Hlc2.
      * exact Hlc3.
Qed.

(** A free variable is related at every type. *)

Lemma sem_var : forall T x, sem T (tm_fvar x).
Proof.
  induction T as [| T1 IH1 T2 IH2]; intros x.
  - split.
    + apply SN_fvar.
    + apply lc_fvar.
  - split.
    + apply SN_fvar.
    + split.
      * apply lc_fvar.
      * intros v Hv Hsemv.
        apply (sem_expand T2 (tm_app (tm_fvar x) v)).
        -- intro Hvapp. inversion Hvapp.
        -- apply lc_app.
           ++ apply lc_fvar.
           ++ apply sem_lc with (T := T1). exact Hsemv.
        -- intros t' Hst.
           inversion Hst as [T0 t0 v0 Hc0 Hv0
                           | a1 a1' a2 Hs Hc
                           | b1 b2 b2' Hv' Hs
                           | i1 i2 Hc1 Hc2
                           | i1 i2 Hc1 Hc2
                           | i1 i1' i2 i3 Hs' Hc2 Hc3]; subst.
           ++ (* ST_App1: [fvar x] does not step *)
              inversion Hs.
           ++ (* ST_App2: [fvar x] is not a value *)
              inversion Hv'.
Qed.

(** ** Context interpretation lemmas. *)

Lemma env_rel_update : forall Gamma x T1 sigma v,
  env_rel Gamma sigma ->
  sem T1 v ->
  env_rel (update Gamma x T1) (fun y => if Nat.eqb x y then v else sigma y).
Proof.
  intros Gamma x T1 sigma v Henv Hv y T Hy.
  unfold update in Hy.
  destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. subst y.
    injection Hy as Hy'. subst T. simpl. exact Hv.
  - exact (Henv y T Hy).
Qed.

Lemma env_lc_update : forall x sigma v,
  env_lc sigma -> locally_closed v ->
  env_lc (fun y => if Nat.eqb x y then v else sigma y).
Proof.
  intros x sigma v Hlc Hv y.
  destruct (Nat.eqb x y); [exact Hv | apply Hlc].
Qed.

(** ** The fundamental theorem of the logical relation. *)

Theorem fundamental : forall Gamma t T,
  has_type Gamma t T ->
  forall sigma, env_lc sigma -> env_rel Gamma sigma -> sem T (subst sigma t).
Proof.
  intros Gamma t T H.
  induction H as [Gamma x T Hx
                | L Gamma T1 T2 t1 Hpre IHpre
                | Gamma t1 t2 T1 T2 Ht1 IHt1 Ht2 IHt2
                | Gamma
                | Gamma
                | Gamma t1 t2 t3 T Ht1 IHt1 Ht2 IHt2 Ht3 IHt3].
  - (* T_Var *)
    intros sigma Hlc Henv. simpl. apply (Henv x T Hx).
  - (* T_Abs *)
    intros sigma Hlc Henv. simpl.
    destruct (fresh_atom (L ++ fvs t1)) as [x Hx].
    assert (HxL : ~ In x L) by (intro Hc; apply Hx; rewrite in_app_iff; left; exact Hc).
    assert (Hxf : ~ In x (fvs t1)) by (intro Hc; apply Hx; rewrite in_app_iff; right; exact Hc).
    (* Local closure of the substituted body. *)
    assert (Hlc_body : lc_at 1 (subst sigma t1)).
    { set (sigma0 := fun y => if Nat.eqb x y then tm_fvar x else sigma y).
      assert (Hlc0 : env_lc sigma0).
      { intro y. unfold sigma0. destruct (Nat.eqb x y); [apply lc_fvar | apply Hlc]. }
      assert (Henv0 : env_rel (update Gamma x T1) sigma0).
      { apply env_rel_update.
        - exact Henv.
        - apply sem_var. }
      pose proof (sem_lc T2 (subst sigma0 (open t1 (tm_fvar x)))
                    (IHpre x HxL sigma0 Hlc0 Henv0)) as Hlcbody.
      assert (Heq : subst sigma0 (open t1 (tm_fvar x))
                    = open_rec 0 (tm_fvar x) (subst sigma t1)).
      { unfold sigma0. apply (subst_open_rec t1 0 sigma (tm_fvar x) x Hlc Hxf). }
      rewrite Heq in Hlcbody.
      apply (lc_open_rec_inv (subst sigma t1) 0 (tm_fvar x)).
      + exact Hlcbody.
      + apply lc_fvar. }
    split.
    + (* strong normalization *)
      apply SN_abs.
    + split.
      * (* local closure *)
        apply lc_abs. exact Hlc_body.
      * (* application clause *)
        intros v Hval Hsemv.
        apply (sem_expand T2 (tm_app (tm_abs T1 (subst sigma t1)) v)).
        -- intro Hv. inversion Hv.
        -- apply lc_app.
           ++ apply lc_abs. exact Hlc_body.
           ++ apply value_lc. exact Hval.
        -- intros t' Hst.
           inversion Hst as [T0 t0 v0 Hlcabs Hval0
                           | a1 a1' a2 Hstep Hlc2
                           | b1 b2 b2' Hval1 Hstep
                           | i1 i2 Hc1 Hc2
                           | i1 i2 Hc1 Hc2
                           | i1 i1' i2 i3 Hs Hc2 Hc3]; subst.
           ++ (* ST_AppAbs *)
              set (sigma_v := fun y => if Nat.eqb x y then v else sigma y).
              assert (Hlc_v : env_lc sigma_v).
              { intro y. unfold sigma_v. destruct (Nat.eqb x y);
                  [apply value_lc; exact Hval | apply Hlc]. }
              assert (Henv_v : env_rel (update Gamma x T1) sigma_v).
              { apply env_rel_update.
                - exact Henv.
                - exact Hsemv. }
              pose proof (IHpre x HxL sigma_v Hlc_v Henv_v) as Hsem_body.
              assert (Heq_v : subst sigma_v (open t1 (tm_fvar x))
                              = open_rec 0 v (subst sigma t1)).
              { unfold sigma_v. apply (subst_open_rec t1 0 sigma v x Hlc Hxf). }
              rewrite Heq_v in Hsem_body.
              exact Hsem_body.
           ++ (* ST_App1: an abstraction cannot step *)
              exfalso. apply (abs_no_step T1 (subst sigma t1) a1'). exact Hstep.
           ++ (* ST_App2: a value cannot step *)
              exfalso. apply (value_no_step v b2' Hval). exact Hstep.
  - (* T_App *)
    intros sigma Hlc Henv. simpl.
    apply (sem_app_aux (subst sigma t1)
             (sem_sn (Ty_Arrow T1 T2) (subst sigma t1) (IHt1 sigma Hlc Henv))
             (subst sigma t2)
             (sem_sn T1 (subst sigma t2) (IHt2 sigma Hlc Henv))
             T1 T2).
    + exact (IHt1 sigma Hlc Henv).
    + exact (IHt2 sigma Hlc Henv).
  - (* T_True *)
    intros sigma Hlc Henv. simpl. split.
    + apply SN_true.
    + apply lc_true.
  - (* T_False *)
    intros sigma Hlc Henv. simpl. split.
    + apply SN_false.
    + apply lc_false.
  - (* T_If *)
    intros sigma Hlc Henv. simpl.
    apply (sem_if (subst sigma t1)
             (sem_sn Ty_Bool (subst sigma t1) (IHt1 sigma Hlc Henv))
             T (subst sigma t2) (subst sigma t3)).
    + apply (sem_lc Ty_Bool). exact (IHt1 sigma Hlc Henv).
    + exact (IHt2 sigma Hlc Henv).
    + exact (IHt3 sigma Hlc Henv).
    + apply (sem_lc T). exact (IHt2 sigma Hlc Henv).
    + apply (sem_lc T). exact (IHt3 sigma Hlc Henv).
Qed.

(** The target theorem. *)

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T H.
  assert (Hlc : env_lc (fun x => tm_fvar x))
    by (intro x; apply lc_fvar).
  assert (Henv : env_rel empty (fun x => tm_fvar x)).
  { intros x T0 Hc. unfold empty in Hc. discriminate. }
  pose proof (fundamental empty t T H (fun x => tm_fvar x) Hlc Henv) as Hsem.
  rewrite subst_id in Hsem.
  apply (sem_sn T t). exact Hsem.
Qed.

End STLCCBVNormalizationTask.
