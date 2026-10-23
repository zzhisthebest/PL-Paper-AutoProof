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

(** ** Infrastructure: fresh atoms, free atoms, substitution. *)

Fixpoint max_list (L : list nat) : nat :=
  match L with
  | nil => 0
  | cons x xs => Nat.max x (max_list xs)
  end.

Definition fresh (L : list atom) : atom := S (max_list L).

Lemma max_list_ge : forall (L : list nat) (x : nat), In x L -> x <= max_list L.
Proof.
  induction L as [| a L IH]; intros x Hin.
  - inversion Hin.
  - simpl in Hin. destruct Hin as [-> | Hin].
    + apply Nat.le_max_l.
    + apply Nat.le_trans with (max_list L); [apply IH; exact Hin | apply Nat.le_max_r].
Qed.

Lemma fresh_notin : forall L, ~ In (fresh L) L.
Proof.
  intros L Hin. unfold fresh in Hin.
  pose proof (max_list_ge L (S (max_list L)) Hin) as Hle.
  exact (Nat.nle_succ_diag_l (max_list L) Hle).
Qed.

Fixpoint free_atom (x : atom) (t : tm) : Prop :=
  match t with
  | tm_bvar _ => False
  | tm_fvar y => x = y
  | tm_app t1 t2 => free_atom x t1 \/ free_atom x t2
  | tm_abs _ t1 => free_atom x t1
  | tm_true => False
  | tm_false => False
  end.

Fixpoint fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ => nil
  | tm_fvar y => cons y nil
  | tm_app t1 t2 => app (fv t1) (fv t2)
  | tm_abs _ t1 => fv t1
  | tm_true => nil
  | tm_false => nil
  end.

Lemma fv_spec : forall t x, In x (fv t) <-> free_atom x t.
Proof.
  induction t as [i | y | t1 IH1 t2 IH2 | T t1 IH | | ]; intros x; simpl.
  - split; intros H; [destruct H | destruct H].
  - split; intros H.
    + destruct H as [-> | H]; [reflexivity | destruct H].
    + subst x. left. reflexivity.
  - split.
    + intros H. apply in_app_or in H. destruct H as [H | H].
      * left. apply (proj1 (IH1 x)). exact H.
      * right. apply (proj1 (IH2 x)). exact H.
    + intros [H | H].
      * apply in_or_app. left. apply (proj2 (IH1 x)). exact H.
      * apply in_or_app. right. apply (proj2 (IH2 x)). exact H.
  - split; intros H.
    + apply (proj1 (IH x)). exact H.
    + apply (proj2 (IH x)). exact H.
  - split; intros H; destruct H.
  - split; intros H; destruct H.
Qed.

Lemma fresh_both : forall L t,
  ~ In (fresh (L ++ fv t)) L /\ ~ free_atom (fresh (L ++ fv t)) t.
Proof.
  intros L t.
  assert (Hnotin : ~ In (fresh (L ++ fv t)) (L ++ fv t)) by apply fresh_notin.
  split.
  - intro Hc. apply Hnotin. apply in_or_app. left. exact Hc.
  - intro Hc. apply Hnotin. apply in_or_app. right. apply fv_spec. exact Hc.
Qed.

Definition extend (sigma : atom -> tm) (x : atom) (v : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then v else sigma y.

Lemma extend_eq : forall sigma x v, extend sigma x v x = v.
Proof. intros. unfold extend. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma extend_neq : forall sigma x v y, x <> y -> extend sigma x v y = sigma y.
Proof.
  intros sigma x v y Hxy. unfold extend.
  assert (E : (x =? y) = false) by (apply Nat.eqb_neq; exact Hxy).
  rewrite E. reflexivity.
Qed.

Fixpoint tsubst (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_app t1 t2 => tm_app (tsubst sigma t1) (tsubst sigma t2)
  | tm_abs T t1 => tm_abs T (tsubst sigma t1)
  | tm_true => tm_true
  | tm_false => tm_false
  end.

Lemma tsubst_id : forall t, tsubst (fun x => tm_fvar x) t = t.
Proof.
  induction t as [i | y | t1 IH1 t2 IH2 | T t1 IH | | ]; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** ** Local closure lemmas *)

Lemma lc_at_abs_inv : forall k T t, lc_at k (tm_abs T t) -> lc_at (S k) t.
Proof. intros k T t H. inversion H; assumption. Qed.

Lemma lc_at_app_inv : forall k t1 t2, lc_at k (tm_app t1 t2) -> lc_at k t1 /\ lc_at k t2.
Proof. intros k t1 t2 H. inversion H; split; assumption. Qed.

Lemma lc_at_mono : forall t i j, i <= j -> lc_at i t -> lc_at j t.
Proof.
  induction t as [n | y | t1 IH1 t2 IH2 | T t1 IH | | ]; intros i j Hij Hlc.
  - inversion Hlc; subst. apply lc_bvar. lia.
  - apply lc_fvar.
  - apply lc_at_app_inv in Hlc. destruct Hlc as [H1 H2].
    apply lc_app; [apply (IH1 i j Hij H1) | apply (IH2 i j Hij H2)].
  - apply lc_at_abs_inv in Hlc. apply lc_abs. apply (IH (S i) (S j)); [lia | exact Hlc].
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma lc_at_open_rec_id : forall t n, lc_at n t -> forall k v, n <= k -> open_rec k v t = t.
Proof.
  induction t as [i | y | t1 IH1 t2 IH2 | T t1 IH | | ]; intros n Hlc k v Hnk; simpl.
  - inversion Hlc; subst. destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst i. exfalso. lia.
    + reflexivity.
  - reflexivity.
  - apply lc_at_app_inv in Hlc. destruct Hlc as [H1 H2].
    rewrite (IH1 n H1 k v Hnk), (IH2 n H2 k v Hnk). reflexivity.
  - apply lc_at_abs_inv in Hlc. rewrite (IH (S n) Hlc (S k) v); [reflexivity | lia].
  - reflexivity.
  - reflexivity.
Qed.

Lemma lc_at_0_open_rec : forall t, lc_at 0 t -> forall k v, open_rec k v t = t.
Proof. intros t H k v. apply (lc_at_open_rec_id t 0 H k v). lia. Qed.

Lemma lc_at_subst : forall t n sigma,
  lc_at n t -> (forall x, lc_at 0 (sigma x)) -> lc_at n (tsubst sigma t).
Proof.
  induction t as [i | y | t1 IH1 t2 IH2 | T t1 IH | | ]; intros n sigma Hlc Hsig; simpl.
  - inversion Hlc; subst. apply lc_bvar. assumption.
  - apply (lc_at_mono (sigma y) 0 n); [lia | apply Hsig].
  - apply lc_at_app_inv in Hlc. destruct Hlc as [H1 H2].
    apply lc_app; [apply (IH1 n sigma H1 Hsig) | apply (IH2 n sigma H2 Hsig)].
  - apply lc_at_abs_inv in Hlc. apply lc_abs. apply (IH (S n) sigma Hlc Hsig).
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma lc_at_open_rec_inv : forall t k u, lc_at k (open_rec k u t) -> lc_at (S k) t.
Proof.
  induction t as [n | y | t1 IH1 t2 IH2 | T t1 IH | | ]; intros k u H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. apply lc_bvar. lia.
    + inversion H; subst. apply lc_bvar. lia.
  - apply lc_fvar.
  - apply lc_at_app_inv in H. destruct H as [H1 H2].
    apply lc_app; [apply (IH1 k u H1) | apply (IH2 k u H2)].
  - apply lc_at_abs_inv in H. apply lc_abs. apply (IH (S k) u H).
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma lc_at_open_rec : forall t k u,
  lc_at (S k) t -> lc_at 0 u -> lc_at k (open_rec k u t).
Proof.
  induction t as [n | y | t1 IH1 t2 IH2 | T t1 IH | | ]; intros k u Ht Hu; simpl.
  - inversion Ht; subst. destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. apply (lc_at_mono u 0 k); [lia | exact Hu].
    + apply lc_bvar. apply Nat.eqb_neq in E. lia.
  - apply lc_fvar.
  - apply lc_at_app_inv in Ht. destruct Ht as [H1 H2].
    apply lc_app; [apply (IH1 k u H1 Hu) | apply (IH2 k u H2 Hu)].
  - apply lc_at_abs_inv in Ht. apply lc_abs. apply (IH (S k) u Ht Hu).
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma tsubst_open_rec_fvar : forall t k sigma x v,
  ~ free_atom x t ->
  (forall y, locally_closed (sigma y)) ->
  tsubst (extend sigma x v) (open_rec k (tm_fvar x) t) = open_rec k v (tsubst sigma t).
Proof.
  induction t as [i | y | t1 IH1 t2 IH2 | T t1 IH | | ]; intros k sigma x v Hfresh Hlc; simpl.
  - destruct (Nat.eqb k i) eqn:E.
    + simpl. apply extend_eq.
    + reflexivity.
  - simpl in Hfresh. simpl.
    rewrite (extend_neq sigma x v y Hfresh).
    rewrite (lc_at_0_open_rec (sigma y) (Hlc y) k v).
    reflexivity.
  - simpl in Hfresh.
    assert (Hf1 : ~ free_atom x t1) by (intro Hc; apply Hfresh; left; exact Hc).
    assert (Hf2 : ~ free_atom x t2) by (intro Hc; apply Hfresh; right; exact Hc).
    rewrite (IH1 k sigma x v Hf1 Hlc), (IH2 k sigma x v Hf2 Hlc). reflexivity.
  - simpl in Hfresh. rewrite (IH (S k) sigma x v Hfresh Hlc). reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma tsubst_open_fvar : forall t sigma x v,
  ~ free_atom x t ->
  (forall y, locally_closed (sigma y)) ->
  tsubst (extend sigma x v) (open t (tm_fvar x)) = open (tsubst sigma t) v.
Proof.
  intros t sigma x v Hfresh Hlc. unfold open.
  apply tsubst_open_rec_fvar; assumption.
Qed.

(** ** Values, steps, strong normalization: basic lemmas *)

Lemma abs_not_step : forall T body t', ~ (tm_abs T body --> t').
Proof. intros T body t' H. inversion H. Qed.

Lemma SN_abs : forall T body, strongly_normalizing (tm_abs T body).
Proof.
  intros T body. apply SN_intro. intros t' H.
  exfalso. exact (abs_not_step T body t' H).
Qed.

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v Hv. destruct Hv as [T t Hlc | | ].
  - exact Hlc.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma value_no_step : forall v v', value v -> step v v' -> False.
Proof.
  intros v v' Hv.
  destruct Hv as [T t Hlc | | ]; intros Hstep.
  - exact (abs_not_step T t v' Hstep).
  - inversion Hstep.
  - inversion Hstep.
Qed.

Lemma value_multistep : forall v v', multi step v v' -> value v -> v' = v.
Proof.
  intros v v' Hm. induction Hm as [x | x y z Hstep Hm IH]; intros Hv.
  - reflexivity.
  - exfalso. exact (value_no_step x y Hv Hstep).
Qed.

Lemma value_app : forall t1 t2, value (tm_app t1 t2) -> False.
Proof. intros t1 t2 Hv. inversion Hv. Qed.

Lemma SN_step : forall t t', strongly_normalizing t -> step t t' -> strongly_normalizing t'.
Proof.
  intros t t' Hsn Hstep.
  destruct Hsn as [t0 Hred].
  apply Hred. exact Hstep.
Qed.

Lemma SN_multistep : forall t t', multi step t t' -> strongly_normalizing t -> strongly_normalizing t'.
Proof.
  intros t t' Hm. induction Hm as [x | x y z Hstep Hm IH]; intros Hsn.
  - exact Hsn.
  - apply IH. exact (SN_step x y Hsn Hstep).
Qed.

Lemma lc_step : forall t t', step t t' -> locally_closed t -> locally_closed t'.
Proof.
  intros t t' Hstep.
  induction Hstep as [T t0 v Hlcabs Hval | t1 a' t2 Hst IHst Hlc2 | v1 t2 b' Hvala Hst2 IHst2].
  - intros Hlc0. simpl.
    apply lc_at_open_rec with (k := 0) (u := v).
    + exact (lc_at_abs_inv 0 T t0 Hlcabs).
    + apply value_lc. exact Hval.
  - intros Hlc0. apply lc_at_app_inv in Hlc0. destruct Hlc0 as [H1 H2].
    apply lc_app.
    + apply IHst. exact H1.
    + exact H2.
  - intros Hlc0. apply lc_at_app_inv in Hlc0. destruct Hlc0 as [H1 H2].
    apply lc_app.
    + apply value_lc. exact Hvala.
    + apply IHst2. exact H2.
Qed.

Lemma multi_app_l : forall t1 t1', multi step t1 t1' ->
  forall t2, locally_closed t2 -> multi step (tm_app t1 t2) (tm_app t1' t2).
Proof.
  intros t1 t1' Hm. induction Hm as [x | x y z Hstep Hm IH].
  - intros t2 Hlc. apply multi_refl.
  - intros t2 Hlc. apply multi_step with (tm_app y t2).
    + apply ST_App1; assumption.
    + apply IH. exact Hlc.
Qed.

Lemma multi_app_decomp : forall (t v : tm), multi step t v -> value v ->
  forall t1 t2, t = tm_app t1 t2 ->
  exists v1 v2, multi step t1 v1 /\ value v1 /\ multi step t2 v2 /\ value v2 /\
                multi step (tm_app v1 v2) v.
Proof.
  intros t v Hm. induction Hm as [x | x y z Hstep Hm IH]; intros Hv t1 t2 Heq.
  - subst x. apply value_app in Hv. destruct Hv.
  - subst x.
    inversion Hstep as [T0 t0 v0 Hlc0 Hval0 | a a' b Hst Hlcb | va b b' Hvala Hst2]; subst.
    + (* AppAbs: t1 = abs T0 t0, y = open t0 t2 *)
      exists (tm_abs T0 t0), t2.
      split; [apply multi_refl | split; [apply v_abs; exact Hlc0 | split; [apply multi_refl | split; [exact Hval0 | apply multi_step with (open t0 t2); assumption]]]].
    + (* App1: t1 --> a', y = app a' t2 *)
      destruct (IH Hv a' t2 eq_refl) as [v1 [v2 [Hm1 [Hval1 [Hm2 [Hval2 Hmapp]]]]]].
      exists v1, v2. split; [| split; [exact Hval1 | split; [exact Hm2 | split; [exact Hval2 | exact Hmapp]]]].
      apply multi_step with a'; assumption.
    + (* App2: y = app t1 b', t2 --> b' *)
      destruct (IH Hv t1 b' eq_refl) as [v1 [v2 [Hm1 [Hval1 [Hm2 [Hval2 Hmapp]]]]]].
      assert (Heq1 : v1 = t1).
      { apply value_multistep with (v := t1); [exact Hm1 | exact Hvala]. }
      subst v1.
      exists t1, v2. split; [apply multi_refl | split; [exact Hvala | split; [| split; [exact Hval2 | exact Hmapp]]]].
      apply multi_step with b'; assumption.
Qed.

Lemma app_multistep_value : forall t1 t2 v,
  multi step (tm_app t1 t2) v -> value v ->
  exists v1 v2, multi step t1 v1 /\ value v1 /\ multi step t2 v2 /\ value v2 /\
                multi step (tm_app v1 v2) v.
Proof.
  intros t1 t2 v Hm Hv.
  exact (multi_app_decomp (tm_app t1 t2) v Hm Hv t1 t2 eq_refl).
Qed.

Lemma multi_app_abs_decomp : forall (t v : tm), multi step t v -> value v ->
  forall T body u, t = tm_app (tm_abs T body) u ->
  exists v2, multi step u v2 /\ value v2 /\ multi step (open body v2) v.
Proof.
  intros t v Hm. induction Hm as [x | x y z Hstep Hm IH]; intros Hv T body u Heq.
  - subst x. apply value_app in Hv. destruct Hv.
  - subst x.
    inversion Hstep as [T0 t0 v0 Hlc0 Hval0 | a a' b Hst Hlcb | va b b' Hvala Hst2]; subst.
    + (* AppAbs *)
      exists u. split; [apply multi_refl | split; [exact Hval0 | exact Hm]].
    + (* App1: contradiction *)
      exfalso. exact (abs_not_step T body a' Hst).
    + (* App2 *)
      destruct (IH Hv T body b' eq_refl) as [v2 [Hm2 [Hval2 Hbody2]]].
      exists v2. split; [| split].
      * apply multi_step with b'; assumption.
      * exact Hval2.
      * exact Hbody2.
Qed.

Lemma app_abs_multistep_value : forall T body u v,
  multi step (tm_app (tm_abs T body) u) v -> value v ->
  exists v2, multi step u v2 /\ value v2 /\ multi step (open body v2) v.
Proof.
  intros T body u v Hm Hv.
  exact (multi_app_abs_decomp (tm_app (tm_abs T body) u) v Hm Hv T body u eq_refl).
Qed.

Lemma has_type_lc : forall Gamma t T, has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T H.
  induction H as [Gamma x T Hx | L Gamma T1 T2 t1 Hbody IH | Gamma t1 t2 T1 T2 H1 IH1 H2 IH2 | Gamma | Gamma].
  - apply lc_fvar.
  - apply lc_abs.
    destruct (fresh_both L t1) as [HnotL Hnotfree].
    apply (lc_at_open_rec_inv t1 0 (tm_fvar (fresh (L ++ fv t1)))).
    apply IH. exact HnotL.
  - apply lc_app; assumption.
  - apply lc_true.
  - apply lc_false.
Qed.

(** ** The logical relation *)

Fixpoint TermRel (Ty : ty) (t : tm) : Prop :=
  strongly_normalizing t /\
  locally_closed t /\
  match Ty with
  | Ty_Bool => True
  | Ty_Arrow T1 T2 =>
      (forall u : tm, TermRel T1 u -> strongly_normalizing (tm_app t u)) /\
      (forall v : tm, multi step t v -> value v ->
         forall u : tm, TermRel T1 u -> TermRel T2 (tm_app v u))
  end.

Definition ValRel (Ty : ty) (v : tm) : Prop :=
  match Ty with
  | Ty_Bool => True
  | Ty_Arrow T1 T2 => forall u : tm, TermRel T1 u -> TermRel T2 (tm_app v u)
  end.

Lemma TermRel_SN : forall Ty t, TermRel Ty t -> strongly_normalizing t.
Proof. intros Ty t H. destruct Ty; simpl in H; exact (proj1 H). Qed.

Lemma TermRel_lc : forall Ty t, TermRel Ty t -> locally_closed t.
Proof. intros Ty t H. destruct Ty; simpl in H; exact (proj1 (proj2 H)). Qed.

Lemma TermRel_app_SN : forall T1 T2 t u,
  TermRel (Ty_Arrow T1 T2) t -> TermRel T1 u -> strongly_normalizing (tm_app t u).
Proof.
  intros T1 T2 t u H Hu. simpl in H.
  exact (proj1 (proj2 (proj2 H)) u Hu).
Qed.

Lemma TermRel_value_red : forall Ty t v,
  TermRel Ty t -> multi step t v -> value v -> ValRel Ty v.
Proof.
  intros Ty t v H Hm Hv. destruct Ty as [| T1 T2]; simpl in *.
  - exact I.
  - exact (proj2 (proj2 (proj2 H)) v Hm Hv).
Qed.

Lemma TermRel_step : forall Ty t t',
  TermRel Ty t -> step t t' -> TermRel Ty t'.
Proof.
  intros Ty t t' H Hstep. destruct Ty as [| T1 T2]; simpl in *.
  - destruct H as [Hsn [Hlc _]]. split.
    + exact (SN_step t t' Hsn Hstep).
    + split.
      * exact (lc_step t t' Hstep Hlc).
      * exact I.
  - destruct H as [Hsn [Hlc [Happ Hval]]]. split; [| split; [| split]].
    + exact (SN_step t t' Hsn Hstep).
    + exact (lc_step t t' Hstep Hlc).
    + intros u Hu. apply (SN_step (tm_app t u)).
      * apply Happ. exact Hu.
      * apply ST_App1; [exact Hstep | apply TermRel_lc with (Ty := T1); exact Hu].
    + intros v Hm Hv.
      apply (Hval v).
      * exact (multi_step step t t' v Hstep Hm).
      * exact Hv.
Qed.

Lemma TermRel_multistep : forall Ty t t',
  multi step t t' -> TermRel Ty t -> TermRel Ty t'.
Proof.
  intros Ty t t' Hm. induction Hm as [x | x y z Hstep Hm IH]; intros H.
  - exact H.
  - apply IH. exact (TermRel_step Ty x y H Hstep).
Qed.

Lemma SN_app_of_value_reds : forall (R : tm -> Prop) f w,
  (forall x y, R x -> step x y -> R y) ->
  strongly_normalizing f ->
  R w ->
  (forall v, multi step f v -> value v -> forall x, R x -> strongly_normalizing (tm_app v x)) ->
  strongly_normalizing (tm_app f w).
Proof.
  intros R f w Rstep Hsn HRw Hcond.
  revert w HRw Hcond.
  induction Hsn as [f0 Hred IH].
  intros w HRw Hcond.
  apply SN_intro.
  intros t' Hstep.
  inversion Hstep as [T0 body v0 Hlc0 Hval0 | a a' b Hst Hlcb | va b b' Hvala Hst2]; subst.
  - (* AppAbs: f0 = abs T0 body, y = open body w *)
    apply (SN_step (tm_app (tm_abs T0 body) w) (open body w)).
    + apply Hcond.
      * apply multi_refl.
      * apply v_abs. exact Hlc0.
      * exact HRw.
    + apply ST_AppAbs; assumption.
  - (* App1: f0 --> a', t' = app a' w *)
    apply (IH a' Hst w HRw).
    intros v Hm Hv x HRx.
    apply (Hcond v).
    * apply multi_step with a'; assumption.
    * exact Hv.
    * exact HRx.
  - (* App2: value f0, w --> b', t' = app f0 b' *)
    apply (Hcond f0 (multi_refl step f0) Hvala b').
    apply Rstep with w; assumption.
Qed.

Lemma SN_app_abs : forall A body u,
  (forall v, TermRel A v -> strongly_normalizing (open body v)) ->
  TermRel A u ->
  strongly_normalizing (tm_app (tm_abs A body) u).
Proof.
  intros A body u Hbody Hu.
  assert (Hsn : strongly_normalizing u) by (apply (TermRel_SN A); exact Hu).
  revert Hu.
  induction Hsn as [u0 Hred IH].
  intros Hu.
  apply SN_intro.
  intros t' Hstep.
  inversion Hstep as [T0 t0 v0 Hlc0 Hval0 | a a' b Hst Hlcb | va b b' Hvala Hst2]; subst.
  - (* AppAbs *) apply Hbody. exact Hu.
  - (* App1 *) exfalso. exact (abs_not_step A body a' Hst).
  - (* App2 *) apply (IH b' Hst2). exact (TermRel_step A u0 b' Hu Hst2).
Qed.

Lemma TermRel_app_abs : forall A B body,
  locally_closed (tm_abs A body) ->
  (forall v, TermRel A v -> TermRel B (open body v)) ->
  forall u, TermRel A u -> TermRel B (tm_app (tm_abs A body) u).
Proof.
  intros A B body Hlc Hbody u Hu.
  destruct B as [| B1 B2].
  - (* B = Bool *)
    simpl. split.
    + apply (SN_app_abs A body).
      * intros v Hv. apply (TermRel_SN Ty_Bool). apply Hbody. exact Hv.
      * exact Hu.
    + split.
      * apply lc_app; [exact Hlc | apply (TermRel_lc A); exact Hu].
      * exact I.
  - (* B = B1 -> B2 *)
    simpl.
    assert (Hsnapp : strongly_normalizing (tm_app (tm_abs A body) u)).
    { apply (SN_app_abs A body).
      - intros v Hv. apply (TermRel_SN (Ty_Arrow B1 B2)). apply Hbody. exact Hv.
      - exact Hu. }
    assert (Hlcapp : locally_closed (tm_app (tm_abs A body) u)).
    { apply lc_app; [exact Hlc | apply (TermRel_lc A); exact Hu]. }
    split; [exact Hsnapp | split; [exact Hlcapp | split]].
    + intros w Hw.
      apply SN_app_of_value_reds with (R := TermRel B1) (w := w).
      * intros x y Hx Hs. exact (TermRel_step B1 x y Hx Hs).
      * exact Hsnapp.
      * exact Hw.
      * intros v Hm Hval x Hx.
        destruct (app_abs_multistep_value A body u v Hm Hval) as [v2 [Hm2 [Hval2 Hbody2]]].
        pose proof (Hbody v2 (TermRel_multistep A u v2 Hm2 Hu)) as HT.
        pose proof (TermRel_app_SN B1 B2 (open body v2) x HT Hx) as Hsnx.
        pose proof (multi_app_l (open body v2) v Hbody2 x (TermRel_lc B1 x Hx)) as Hmx.
        exact (SN_multistep (tm_app (open body v2) x) (tm_app v x) Hmx Hsnx).
    + intros v Hm Hval w Hw.
      destruct (app_abs_multistep_value A body u v Hm Hval) as [v2 [Hm2 [Hval2 Hbody2]]].
      pose proof (Hbody v2 (TermRel_multistep A u v2 Hm2 Hu)) as HT.
      exact (TermRel_value_red (Ty_Arrow B1 B2) (open body v2) v HT Hbody2 Hval w Hw).
Qed.

Definition env_sat (sigma : atom -> tm) (Gamma : context) : Prop :=
  (forall x, locally_closed (sigma x)) /\
  (forall x T, Gamma x = Some T -> TermRel T (sigma x)).

Definition sem_ty (Gamma : context) (t : tm) (Ty : ty) : Prop :=
  forall sigma, env_sat sigma Gamma -> TermRel Ty (tsubst sigma t).

Theorem fundamental : forall Gamma t Ty, has_type Gamma t Ty -> sem_ty Gamma t Ty.
Proof.
  intros Gamma t Ty H.
  induction H as [Gamma x T Hx | L Gamma T1 T2 t1 Hbody_ty IH | Gamma t1 t2 T1 T2 H1 IH1 H2 IH2 | Gamma | Gamma].
  - (* T_Var *)
    intros sigma [Hlc_sigma Hsat]. simpl. apply Hsat. exact Hx.
  - (* T_Abs *)
    intros sigma [Hlc_sigma Hsat].
    simpl.
    destruct (fresh_both L t1) as [HnotL Hnotfree].
    assert (Hbody_sem : forall v, TermRel T1 v -> TermRel T2 (open (tsubst sigma t1) v)).
    { intros v Hv.
      assert (Henv : env_sat (extend sigma (fresh (L ++ fv t1)) v)
                            (update Gamma (fresh (L ++ fv t1)) T1)).
      { split.
        - intros y. unfold extend.
          destruct (Nat.eqb (fresh (L ++ fv t1)) y) eqn:E.
          + exact (TermRel_lc T1 v Hv).
          + apply Hlc_sigma.
        - intros y T0 Hy. unfold extend.
          destruct (Nat.eqb (fresh (L ++ fv t1)) y) eqn:E.
          + apply Nat.eqb_eq in E. subst y.
            unfold update in Hy. rewrite Nat.eqb_refl in Hy.
            injection Hy as HT. subst T0. exact Hv.
          + unfold update in Hy. rewrite E in Hy.
            apply Hsat. exact Hy. }
      specialize (IH (fresh (L ++ fv t1)) HnotL (extend sigma (fresh (L ++ fv t1)) v) Henv).
      rewrite (tsubst_open_fvar t1 sigma (fresh (L ++ fv t1)) v Hnotfree Hlc_sigma) in IH.
      exact IH. }
    assert (Hlcabs : locally_closed (tm_abs T1 (tsubst sigma t1))).
    { apply lc_abs.
      apply lc_at_subst with (n := 1) (sigma := sigma).
      - apply (lc_at_open_rec_inv t1 0 (tm_fvar (fresh (L ++ fv t1)))).
        exact (has_type_lc (update Gamma (fresh (L ++ fv t1)) T1)
                           (open t1 (tm_fvar (fresh (L ++ fv t1)))) T2
                           (Hbody_ty (fresh (L ++ fv t1)) HnotL)).
      - exact Hlc_sigma. }
    split; [| split; [| split]].
    + apply SN_abs.
    + exact Hlcabs.
    + intros u Hu.
      apply (SN_app_abs T1 (tsubst sigma t1)).
      * intros v Hv. apply (TermRel_SN T2). apply Hbody_sem. exact Hv.
      * exact Hu.
    + intros v Hm Hval w Hw.
      assert (Heq : v = tm_abs T1 (tsubst sigma t1)).
      { apply value_multistep with (v := tm_abs T1 (tsubst sigma t1)).
        - exact Hm.
        - apply v_abs. exact Hlcabs. }
      subst v.
      apply TermRel_app_abs with (A := T1) (body := tsubst sigma t1).
      * exact Hlcabs.
      * intros v0 Hv0. apply Hbody_sem. exact Hv0.
      * exact Hw.
  - (* T_App *)
    intros sigma [Hlc_sigma Hsat].
    simpl.
    pose proof (IH1 sigma (conj Hlc_sigma Hsat)) as HT1.
    pose proof (IH2 sigma (conj Hlc_sigma Hsat)) as HT2.
    destruct T2 as [| B1 B2].
    + (* Bool *)
      simpl. split.
      * apply (TermRel_app_SN T1 Ty_Bool); assumption.
      * split.
        -- apply lc_app;
           [apply TermRel_lc with (Ty := Ty_Arrow T1 Ty_Bool); exact HT1
           | apply TermRel_lc with (Ty := T1); exact HT2].
        -- exact I.
    + (* Arrow *)
      simpl.
      assert (Hsnapp : strongly_normalizing (tm_app (tsubst sigma t1) (tsubst sigma t2)))
        by (apply (TermRel_app_SN T1 (Ty_Arrow B1 B2)); assumption).
      assert (Hlcapp : locally_closed (tm_app (tsubst sigma t1) (tsubst sigma t2)))
        by (apply lc_app;
            [apply TermRel_lc with (Ty := Ty_Arrow T1 (Ty_Arrow B1 B2)); exact HT1
            | apply TermRel_lc with (Ty := T1); exact HT2]).
      split; [exact Hsnapp | split; [exact Hlcapp | split]].
      * intros w Hw.
        apply SN_app_of_value_reds with (R := TermRel B1) (w := w).
        -- intros x y Hx Hs. exact (TermRel_step B1 x y Hx Hs).
        -- exact Hsnapp.
        -- exact Hw.
        -- intros v Hm Hval x Hx.
           destruct (app_multistep_value (tsubst sigma t1) (tsubst sigma t2) v Hm Hval)
             as [v1 [v2 [Hm1 [Hval1 [Hm2 [Hval2 Hmapp]]]]]].
           pose proof (TermRel_value_red (Ty_Arrow T1 (Ty_Arrow B1 B2))
                         (tsubst sigma t1) v1 HT1 Hm1 Hval1) as HV1.
           pose proof (TermRel_multistep T1 (tsubst sigma t2) v2 Hm2 HT2) as HT2v.
           pose proof (HV1 v2 HT2v) as HTapp.
           pose proof (TermRel_app_SN B1 B2 (tm_app v1 v2) x HTapp Hx) as Hsnx.
           pose proof (multi_app_l (tm_app v1 v2) v Hmapp x (TermRel_lc B1 x Hx)) as Hmx.
           exact (SN_multistep (tm_app (tm_app v1 v2) x) (tm_app v x) Hmx Hsnx).
      * intros v Hm Hval w Hw.
        destruct (app_multistep_value (tsubst sigma t1) (tsubst sigma t2) v Hm Hval)
          as [v1 [v2 [Hm1 [Hval1 [Hm2 [Hval2 Hmapp]]]]]].
        pose proof (TermRel_value_red (Ty_Arrow T1 (Ty_Arrow B1 B2))
                      (tsubst sigma t1) v1 HT1 Hm1 Hval1) as HV1.
        pose proof (TermRel_multistep T1 (tsubst sigma t2) v2 Hm2 HT2) as HT2v.
        pose proof (HV1 v2 HT2v) as HTapp.
        exact (TermRel_value_red (Ty_Arrow B1 B2) (tm_app v1 v2) v HTapp Hmapp Hval w Hw).
  - (* T_True *)
    intros sigma [Hlc_sigma Hsat]. simpl. split.
    + apply SN_intro. intros t' Hs. inversion Hs.
    + split.
      * apply lc_true.
      * exact I.
  - (* T_False *)
    intros sigma [Hlc_sigma Hsat]. simpl. split.
    + apply SN_intro. intros t' Hs. inversion Hs.
    + split.
      * apply lc_false.
      * exact I.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  pose proof (fundamental empty t T Hty) as Hsem.
  unfold sem_ty in Hsem.
  specialize (Hsem (fun x => tm_fvar x)).
  assert (Henv : env_sat (fun x => tm_fvar x) empty).
  { split.
    - intros x. apply lc_fvar.
    - intros x T0 Hx. unfold empty in Hx. discriminate. }
  specialize (Hsem Henv).
  rewrite tsubst_id in Hsem.
  exact (TermRel_SN T t Hsem).
Qed.

End STLCNormalizationNoneHardTask.
