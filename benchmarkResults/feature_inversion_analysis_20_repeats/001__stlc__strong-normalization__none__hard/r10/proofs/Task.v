(** STLC call-by-value strong-normalization benchmark.
    No if-then-else, non-determinism, or recursion is included. *)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Relations.Relation_Definitions.
From Stdlib Require Import Lia.

Module STLCNormalizationNoneHardTask.

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
  | tm_false : tm.

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

(** Opening and local closure. *)

Fixpoint open_rec (k : nat) (u : tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => if Nat.eqb k i then u else tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_app t1 t2 => tm_app (open_rec k u t1) (open_rec k u t2)
  | tm_abs T t1 => tm_abs T (open_rec (S k) u t1)
  | tm_true => tm_true
  | tm_false => tm_false
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
      lc_at k tm_false.

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
where "<{ Gamma '|--' t '\in' T }>" := (has_type Gamma t T)
  : stlc_scope.

(** Target theorem: strong normalization for the supplied CBV relation. *)

Inductive strongly_normalizing : tm -> Prop :=
  | SN_intro : forall t,
      (forall t', t --> t' -> strongly_normalizing t') ->
      strongly_normalizing t.

(** * Auxiliary development: strong normalization via a logical relation *)

(** ** Free variables and freshness *)

Fixpoint fvars (t : tm) : list atom :=
  match t with
  | tm_bvar _ => nil
  | tm_fvar x => x :: nil
  | tm_app t1 t2 => fvars t1 ++ fvars t2
  | tm_abs _ t1 => fvars t1
  | tm_true => nil
  | tm_false => nil
  end.

Lemma In_le_fold_max : forall (L : list atom) (x : atom),
  In x L -> x <= fold_right Nat.max 0 L.
Proof.
  intros L. induction L as [| a L IH]; intros x Hx; simpl in *.
  - destruct Hx.
  - destruct Hx as [-> | Hx].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; exact Hx | apply Nat.le_max_r].
Qed.

Lemma fresh_atom : forall L : list atom, exists x : atom, ~ In x L.
Proof.
  intros L. exists (S (fold_right Nat.max 0 L)).
  intro Hx. pose proof (In_le_fold_max L _ Hx). lia.
Qed.

(** ** Local closure: basic lemmas *)

Lemma lc_bvar_inv : forall k i, lc_at k (tm_bvar i) -> i < k.
Proof. intros k i H. inversion H. assumption. Qed.

Lemma lc_app_inv : forall k t1 t2,
  lc_at k (tm_app t1 t2) -> lc_at k t1 /\ lc_at k t2.
Proof. intros k t1 t2 H. inversion H. split; assumption. Qed.

Lemma lc_abs_inv : forall k T t, lc_at k (tm_abs T t) -> lc_at (S k) t.
Proof. intros k T t H. inversion H. assumption. Qed.

Lemma lc_mono : forall n m t, n <= m -> lc_at n t -> lc_at m t.
Proof.
  intros n m t Hnm Hlc. revert m Hnm.
  induction Hlc as [k i Hlt | k x | k a b Ha IHa Hb IHb | k T b Hb IH | k | k];
    intros m Hnm.
  - apply lc_bvar. lia.
  - apply lc_fvar.
  - apply lc_app; [apply IHa | apply IHb]; lia.
  - apply lc_abs. apply IH. lia.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma lc_open : forall k t u,
  lc_at (S k) t -> lc_at k u -> lc_at k (open_rec k u t).
Proof.
  intros k t. revert k. induction t; intros k u Ht Hu; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. exact Hu.
    + apply lc_bvar. apply lc_bvar_inv in Ht.
      apply Nat.eqb_neq in E. lia.
  - apply lc_fvar.
  - destruct (lc_app_inv (S k) t1 t2 Ht) as [H1 H2].
    apply lc_app; [apply IHt1 | apply IHt2]; assumption.
  - apply lc_abs. apply IHt with (k := S k).
    + apply lc_abs_inv in Ht. exact Ht.
    + apply lc_mono with (n := k); [lia | exact Hu].
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma lc_open_fvar : forall k x t,
  lc_at (S k) t -> lc_at k (open_rec k (tm_fvar x) t).
Proof.
  intros k x t H. apply lc_open with (u := tm_fvar x); [exact H | apply lc_fvar].
Qed.

Lemma lc_open_fvar_inv : forall k x t,
  lc_at k (open_rec k (tm_fvar x) t) -> lc_at (S k) t.
Proof.
  intros k x t. revert k. induction t; intros k Hk; simpl in Hk.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. apply lc_bvar. lia.
    + apply lc_bvar. apply lc_bvar_inv in Hk. lia.
  - apply lc_fvar.
  - destruct (lc_app_inv k _ _ Hk) as [H1 H2].
    apply lc_app; [apply IHt1 | apply IHt2]; assumption.
  - apply lc_abs. apply IHt. apply lc_abs_inv in Hk. exact Hk.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma open_rec_lc : forall n t, lc_at n t -> forall u, open_rec n u t = t.
Proof.
  intros n t. revert n. induction t; intros k Hlc u; simpl.
  - apply lc_bvar_inv in Hlc.
    assert (E : (k =? n) = false) by (apply Nat.eqb_neq; lia).
    rewrite E. reflexivity.
  - reflexivity.
  - destruct (lc_app_inv k t1 t2 Hlc) as [H1 H2].
    rewrite (IHt1 k H1 u), (IHt2 k H2 u). reflexivity.
  - apply lc_abs_inv in Hlc. rewrite (IHt (S k) Hlc u). reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** ** Environments and simultaneous substitution *)

Definition env := atom -> tm.

Definition env_lc (sigma : env) : Prop :=
  forall x : atom, lc_at 0 (sigma x).

Definition env_update (sigma : env) (x : atom) (u : tm) : env :=
  fun y => if Nat.eqb x y then u else sigma y.

Fixpoint subst_env (sigma : env) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_app t1 t2 => tm_app (subst_env sigma t1) (subst_env sigma t2)
  | tm_abs T t1 => tm_abs T (subst_env sigma t1)
  | tm_true => tm_true
  | tm_false => tm_false
  end.

Lemma subst_env_lc : forall sigma t n,
  env_lc sigma ->
  (lc_at n (subst_env sigma t) <-> lc_at n t).
Proof.
  intros sigma t. induction t; intros k Hlc; simpl.
  - split; intro H; assumption.
  - split; intro H.
    + apply lc_fvar.
    + apply lc_mono with (n := 0); [lia | apply (Hlc a)].
  - split; intro H.
    + destruct (lc_app_inv k _ _ H) as [H1 H2].
      apply lc_app; [apply (proj1 (IHt1 k Hlc)) | apply (proj1 (IHt2 k Hlc))];
        assumption.
    + destruct (lc_app_inv k _ _ H) as [H1 H2].
      apply lc_app; [apply (proj2 (IHt1 k Hlc)) | apply (proj2 (IHt2 k Hlc))];
        assumption.
  - split; intro H.
    + apply lc_abs. apply (proj1 (IHt (S k) Hlc)).
      apply lc_abs_inv in H. exact H.
    + apply lc_abs. apply (proj2 (IHt (S k) Hlc)).
      apply lc_abs_inv in H. exact H.
  - split; intro H; apply lc_true.
  - split; intro H; apply lc_false.
Qed.

Lemma subst_env_open_rec : forall sigma x u t k,
  env_lc sigma ->
  ~ In x (fvars t) ->
  subst_env (env_update sigma x u) (open_rec k (tm_fvar x) t)
  = open_rec k u (subst_env sigma t).
Proof.
  intros sigma x u t. induction t; intros k Hlc Hfresh; simpl.
  - (* tm_bvar *)
    destruct (Nat.eqb k n) eqn:E.
    + simpl. unfold env_update. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - (* tm_fvar *)
    assert (Hne : x <> a).
    { intro Heq. apply Hfresh. subst a. simpl. left. reflexivity. }
    assert (Hlck : lc_at k (sigma a)).
    { apply lc_mono with (n := 0); [lia | apply (Hlc a)]. }
    rewrite (open_rec_lc k (sigma a) Hlck u).
    unfold env_update.
    assert (E : (x =? a) = false) by (apply Nat.eqb_neq; exact Hne).
    rewrite E. reflexivity.
  - (* tm_app *)
    rewrite (IHt1 k Hlc).
    2: { intro H; apply Hfresh. apply in_app_iff. left. exact H. }
    rewrite (IHt2 k Hlc).
    2: { intro H; apply Hfresh. apply in_app_iff. right. exact H. }
    reflexivity.
  - (* tm_abs *)
    rewrite (IHt (S k) Hlc). 2: { simpl in Hfresh; exact Hfresh. }
    reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma subst_env_id : forall t, subst_env (fun x : atom => tm_fvar x) t = t.
Proof.
  induction t; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** ** Values and single-step reduction *)

Lemma value_lc : forall v, value v -> lc_at 0 v.
Proof.
  intros v Hv. induction Hv as [T b Hlc | |].
  - exact Hlc.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma value_no_step : forall v t', value v -> step v t' -> False.
Proof.
  intros v t' Hv Hst. induction Hv; inversion Hst.
Qed.

Lemma abs_no_step : forall T t t', step (tm_abs T t) t' -> False.
Proof. intros T t t' H. inversion H. Qed.

Lemma step_lc : forall t t', step t t' -> lc_at 0 t -> lc_at 0 t'.
Proof.
  intros t t' Hst. induction Hst as
    [ T b v Hlca Hv
    | a a' b Hsa IH Hlcb
    | v1 b b' Hv1 Hsb IH ]; intros Hlc.
  - destruct (lc_app_inv 0 (tm_abs T b) v Hlc) as [H1 H2].
    apply lc_open; [apply lc_abs_inv in H1; exact H1 | exact H2].
  - destruct (lc_app_inv 0 a b Hlc) as [H1 H2].
    apply lc_app; [apply IH; exact H1 | exact H2].
  - destruct (lc_app_inv 0 v1 b Hlc) as [H1 H2].
    apply lc_app; [exact H1 | apply IH; exact H2].
Qed.

Lemma step_det : forall t t1 t2, step t t1 -> step t t2 -> t1 = t2.
Proof.
  intros t t1 t2 H1. revert t2.
  induction H1 as
    [ T b v Hlca Hv
    | a a' b Hsa IH Hlcb
    | v1 b b' Hv1 Hsb IH ]; intros t2 H2.
  - inversion H2 as [TA bA vA HlcaA HvA | u1 u1' w1 Hu1 Hlcu1 | z1 w2 w2' Hz1 Hw2]; subst.
    + reflexivity.
    + exfalso. exact (abs_no_step T b u1' Hu1).
    + exfalso. exact (value_no_step v w2' Hv Hw2).
  - inversion H2 as [TA bA vA HlcaA HvA | u1 u1' w1 Hu1 Hlcu1 | z1 w2 w2' Hz1 Hw2]; subst.
    + exfalso. exact (abs_no_step TA bA a' Hsa).
    + f_equal. apply IH. exact Hu1.
    + exfalso. exact (value_no_step a a' Hz1 Hsa).
  - inversion H2 as [TA bA vA HlcaA HvA | u1 u1' w1 Hu1 Hlcu1 | z1 w2 w2' Hz1 Hw2]; subst.
    + exfalso. exact (value_no_step b b' HvA Hsb).
    + exfalso. exact (value_no_step v1 u1' Hv1 Hu1).
    + f_equal. apply IH. exact Hw2.
Qed.

(** ** Strong normalisation basics *)

Lemma sn_step : forall t t', strongly_normalizing t -> step t t' ->
  strongly_normalizing t'.
Proof.
  intros t t' Hsn. induction Hsn as [u Hreds IH]. intros Hst.
  apply Hreds. exact Hst.
Qed.

Lemma sn_abs : forall T t, strongly_normalizing (tm_abs T t).
Proof.
  intros T t. apply SN_intro. intros t' Hst. exfalso.
  eapply abs_no_step; eassumption.
Qed.

Lemma sn_true : strongly_normalizing tm_true.
Proof.
  apply SN_intro. intros t' Hst. exfalso.
  eapply value_no_step; [apply v_true | exact Hst].
Qed.

Lemma sn_false : strongly_normalizing tm_false.
Proof.
  apply SN_intro. intros t' Hst. exfalso.
  eapply value_no_step; [apply v_false | exact Hst].
Qed.

(** ** Well-typed terms are locally closed *)

Lemma typing_lc : forall Gamma t T, has_type Gamma t T -> lc_at 0 t.
Proof.
  intros Gamma t T Hty.
  induction Hty as
    [ Gamma0 x T0 Heq
    | L Gamma0 T1 T2 t1 Hbody IHAbs
    | Gamma0 t1 t2 T1 T2 Ht1 IH1 Ht2 IH2
    | Gamma0
    | Gamma0 ].
  - apply lc_fvar.
  - apply lc_abs.
    destruct (fresh_atom L) as [x Hx].
    specialize (IHAbs x Hx).
    apply (lc_open_fvar_inv 0 x t1). exact IHAbs.
  - apply lc_app; assumption.
  - apply lc_true.
  - apply lc_false.
Qed.

(** ** The logical relation *)

Fixpoint LR (T : ty) (t : tm) : Prop :=
  match T with
  | Ty_Bool => lc_at 0 t /\ strongly_normalizing t
  | Ty_Arrow T1 T2 =>
      lc_at 0 t /\ strongly_normalizing t /\
      (forall u, LR T1 u -> LR T2 (tm_app t u))
  end.

Lemma LR_lc : forall T t, LR T t -> lc_at 0 t.
Proof. intros T t H. destruct T; simpl in H; apply (proj1 H). Qed.

Lemma LR_sn : forall T t, LR T t -> strongly_normalizing t.
Proof.
  intros T t H. destruct T; simpl in H;
    [apply (proj2 H) | apply (proj1 (proj2 H))].
Qed.

Lemma LR_app : forall T1 T2 t u,
  LR (Ty_Arrow T1 T2) t -> LR T1 u -> LR T2 (tm_app t u).
Proof.
  intros T1 T2 t u H Hu. simpl in H. apply (proj2 (proj2 H)). exact Hu.
Qed.

Definition env_ty (sigma : env) (Gamma : context) : Prop :=
  forall x T, Gamma x = Some T -> LR T (sigma x).

Definition env_ok (sigma : env) (Gamma : context) : Prop :=
  env_lc sigma /\ env_ty sigma Gamma.

(** ** Closure of the logical relation under reduction *)

Lemma LR_step : forall T t t', LR T t -> step t t' -> LR T t'.
Proof.
  intros T. induction T as [| T1 IHT1 T2 IHT2]; intros t t' Hlr Hst.
  - simpl in Hlr. simpl. destruct Hlr as [Hlc Hsn]. split.
    + apply step_lc with (t := t); assumption.
    + apply sn_step with (t := t); assumption.
  - simpl in Hlr. simpl. destruct Hlr as [Hlc [Hsn Happ]]. split.
    + apply step_lc with (t := t); assumption.
    + split.
      * apply sn_step with (t := t); assumption.
      * intros u Hu. apply (IHT2 (tm_app t u) (tm_app t' u)).
        -- apply Happ. exact Hu.
        -- apply ST_App1; [exact Hst | apply LR_lc with (T := T1); exact Hu].
Qed.

Lemma LR_step_back : forall T t t',
  lc_at 0 t -> step t t' -> LR T t' -> LR T t.
Proof.
  intros T. induction T as [| T1 IHT1 T2 IHT2]; intros t t' Hlc Hst Hlr.
  - simpl in Hlr. simpl. destruct Hlr as [Hlc' Hsn']. split.
    + exact Hlc.
    + apply SN_intro. intros z Hsz.
      assert (t' = z) by (exact (step_det t t' z Hst Hsz)).
      subst. exact Hsn'.
  - simpl in Hlr. simpl. destruct Hlr as [Hlc' [Hsn' Happ']]. split.
    + exact Hlc.
    + split.
      * apply SN_intro. intros z Hsz.
        assert (t' = z) by (exact (step_det t t' z Hst Hsz)).
        subst. exact Hsn'.
      * intros u Hu. apply (IHT2 (tm_app t u) (tm_app t' u)).
        -- apply lc_app; [exact Hlc | apply LR_lc with (T := T1); exact Hu].
        -- apply ST_App1; [exact Hst | apply LR_lc with (T := T1); exact Hu].
        -- apply Happ'. exact Hu.
Qed.

(** ** A neutral-introduction rule for the logical relation *)

Lemma LR_neutral_intro : forall T (t : tm),
  lc_at 0 t ->
  (forall t', step t t' -> LR T t') ->
  ~ value t ->
  LR T t.
Proof.
  intros T. induction T as [| T1 IHT1 T2 IHT2]; intros t Hlc Hreds Hnv.
  - simpl. split.
    + exact Hlc.
    + apply SN_intro. intros t' Hst.
      apply LR_sn with (T := Ty_Bool). apply Hreds. exact Hst.
  - simpl. split.
    + exact Hlc.
    + split.
      * apply SN_intro. intros t' Hst.
        apply LR_sn with (T := Ty_Arrow T1 T2). apply Hreds. exact Hst.
      * intros u Hu.
        apply (IHT2 (tm_app t u)).
        -- apply lc_app; [exact Hlc | apply LR_lc with (T := T1); exact Hu].
        -- intros t' Hst.
           inversion Hst as
             [ TA bA vA HlcaA HvA
             | a1 a1' b1 Hsa1 Hlcb1
             | z1 w2 w2' Hz1 Hw2 ]; subst.
           ++ exfalso. apply Hnv. apply v_abs. exact HlcaA.
           ++ apply LR_app with (T1 := T1).
              ** apply Hreds. exact Hsa1.
              ** exact Hu.
           ++ exfalso. apply Hnv. exact Hz1.
        -- intros Hv. inversion Hv.
Qed.

(** ** Application of an abstraction to any reducible argument *)

Lemma abs_app_LR : forall T1 T2 body,
  lc_at 1 body ->
  (forall u, LR T1 u -> LR T2 (open body u)) ->
  forall u, LR T1 u -> LR T2 (tm_app (tm_abs T1 body) u).
Proof.
  intros T1 T2 body Hlc Hbody.
  assert (Haux : forall u, strongly_normalizing u ->
                            LR T1 u -> LR T2 (tm_app (tm_abs T1 body) u)).
  { intros u Hsn. induction Hsn as [u Hstep IH]. intros Hu.
    apply LR_neutral_intro with (T := T2).
    - apply lc_app.
      + apply lc_abs. exact Hlc.
      + apply LR_lc with (T := T1). exact Hu.
    - intros t' Hst.
      inversion Hst as
        [ TA bA vA HlcaA HvA
        | a1 a1' b1 Hsa1 Hlcb1
        | z1 w2 w2' Hz1 Hw2 ]; subst.
      + apply Hbody. exact Hu.
      + exfalso. exact (abs_no_step T1 body a1' Hsa1).
      + apply IH.
        * exact Hw2.
        * apply LR_step with (T := T1) (t := u); assumption.
    - intros Hv. inversion Hv. }
  intros u Hu. apply Haux.
  - apply LR_sn with (T := T1). exact Hu.
  - exact Hu.
Qed.

(** ** The fundamental theorem *)

Lemma fundamental : forall Gamma t T,
  has_type Gamma t T ->
  forall sigma, env_ok sigma Gamma -> LR T (subst_env sigma t).
Proof.
  intros Gamma t T Hty.
  induction Hty as
    [ Gamma0 x T0 Heq
    | L Gamma0 T1 T2 t1 Hbody IHAbs
    | Gamma0 t1 t2 T1 T2 Ht1 IH1 Ht2 IH2
    | Gamma0
    | Gamma0 ].
  - (* T_Var *)
    intros sigma [Hlcs Htys]. simpl. exact (Htys x T0 Heq).
  - (* T_Abs *)
    intros sigma [Hlcs Htys]. simpl.
    destruct (fresh_atom (L ++ fvars t1)) as [x Hfresh].
    assert (HxL : ~ In x L).
    { intro H; apply Hfresh; apply in_app_iff; left; exact H. }
    assert (Hxf : ~ In x (fvars t1)).
    { intro H; apply Hfresh; apply in_app_iff; right; exact H. }
    assert (Hlc_body : lc_at 1 t1).
    { apply (lc_open_fvar_inv 0 x t1).
      apply typing_lc with (Gamma := update Gamma0 x T1) (T := T2).
      apply Hbody. exact HxL. }
    assert (Hlc_s : lc_at 1 (subst_env sigma t1)).
    { apply (proj2 (subst_env_lc sigma t1 1 Hlcs)). exact Hlc_body. }
    split.
    + apply lc_abs. exact Hlc_s.
    + split.
      * apply sn_abs.
      * intros u Hu.
        assert (HbodyLR : forall v, LR T1 v -> LR T2 (open (subst_env sigma t1) v)).
        { intros v Hv.
          assert (Hok0 : env_ok (env_update sigma x v) (update Gamma0 x T1)).
          { split.
            - intros y. unfold env_update.
              destruct (Nat.eqb x y) eqn:E.
              + apply LR_lc with (T := T1). exact Hv.
              + apply (Hlcs y).
            - intros y S Hy. unfold env_update.
              destruct (Nat.eqb x y) eqn:E.
              + unfold update in Hy. rewrite E in Hy. inversion Hy. subst S. exact Hv.
              + unfold update in Hy. rewrite E in Hy. apply Htys. exact Hy. }
          specialize (IHAbs x HxL (env_update sigma x v) Hok0).
          change (LR T2 (subst_env (env_update sigma x v)
                            (open_rec 0 (tm_fvar x) t1))) in IHAbs.
          rewrite (subst_env_open_rec sigma x v t1 0 Hlcs Hxf) in IHAbs.
          exact IHAbs. }
        exact (abs_app_LR T1 T2 (subst_env sigma t1) Hlc_s HbodyLR u Hu).
  - (* T_App *)
    intros sigma Hok. simpl.
    apply LR_app with (T1 := T1).
    + apply IH1. exact Hok.
    + apply IH2. exact Hok.
  - (* T_True *)
    intros sigma Hok. simpl. split; [apply lc_true | apply sn_true].
  - (* T_False *)
    intros sigma Hok. simpl. split; [apply lc_false | apply sn_false].
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  apply LR_sn with (T := T).
  rewrite <- subst_env_id.
  apply fundamental with (Gamma := empty).
  - exact Hty.
  - split.
    + intros x. apply lc_fvar.
    + intros x S H. simpl in H. discriminate H.
Qed.

End STLCNormalizationNoneHardTask.
