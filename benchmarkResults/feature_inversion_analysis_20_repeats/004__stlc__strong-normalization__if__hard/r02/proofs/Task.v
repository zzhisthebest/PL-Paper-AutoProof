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

(** ** Auxiliary definitions and lemmas for the strong normalization proof. *)

Definition lc (t : tm) : Prop := lc_at 0 t.

(** *** Fresh atoms *)

Fixpoint list_max (l : list atom) : atom :=
  match l with
  | [] => 0
  | x :: l' => Nat.max x (list_max l')
  end.

Lemma list_max_spec : forall (l : list atom) (x : atom),
  In x l -> x <= list_max l.
Proof.
  induction l as [| y l IH]; intros x Hin; simpl in *.
  - destruct Hin.
  - destruct Hin as [Heq | Hin].
    + subst. apply Nat.le_max_l.
    + apply Nat.le_trans with (list_max l);
        [apply IH; exact Hin | apply Nat.le_max_r].
Qed.

Definition fresh (l : list atom) : atom := S (list_max l).

Lemma fresh_notin : forall l : list atom, ~ In (fresh l) l.
Proof.
  intros l Hin. unfold fresh in Hin.
  apply list_max_spec in Hin. lia.
Qed.

(** *** Inversion principles for local closure *)

Lemma lc_at_bvar_inv : forall (k : nat) (i : nat),
  lc_at k (tm_bvar i) -> i < k.
Proof.
  intros k i H. inversion H. assumption.
Qed.

Lemma lc_at_app_inv : forall (k : nat) (t1 t2 : tm),
  lc_at k (tm_app t1 t2) -> lc_at k t1 /\ lc_at k t2.
Proof.
  intros k t1 t2 H. inversion H; subst. split; assumption.
Qed.

Lemma lc_at_abs_inv : forall (k : nat) (T : ty) (b : tm),
  lc_at k (tm_abs T b) -> lc_at (S k) b.
Proof.
  intros k T b H. inversion H; subst. assumption.
Qed.

Lemma lc_at_if_inv : forall (k : nat) (t1 t2 t3 : tm),
  lc_at k (tm_if t1 t2 t3) ->
  lc_at k t1 /\ lc_at k t2 /\ lc_at k t3.
Proof.
  intros k t1 t2 t3 H. inversion H; subst. repeat split; assumption.
Qed.

Lemma lc_at_mono : forall (k : nat) (t : tm),
  lc_at k t -> forall k', k <= k' -> lc_at k' t.
Proof.
  intros k t H. induction H as
    [k i Hlt | k x | k t1 t2 H1 IH1 H2 IH2 | k T b H1 IH1 | k | k
    | k t1 t2 t3 H1 IH1 H2 IH2 H3 IH3]; intros k' Hle.
  - apply lc_bvar. lia.
  - apply lc_fvar.
  - apply lc_app; [apply IH1 | apply IH2]; lia.
  - apply lc_abs. apply IH1. lia.
  - apply lc_true.
  - apply lc_false.
  - apply lc_if; [apply IH1 | apply IH2 | apply IH3]; lia.
Qed.

(** *** Interaction of opening with local closure *)

Lemma open_rec_lc_gen : forall (t : tm) (j : nat),
  lc_at j t -> forall k u, j <= k -> open_rec k u t = t.
Proof.
  induction t as [i|x|t1 IH1 t2 IH2|T b IHb| | |t1 IH1 t2 IH2 t3 IH3];
    intros j Hj k u Hjk; simpl.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst.
      exfalso. apply lc_at_bvar_inv in Hj. lia.
    + reflexivity.
  - reflexivity.
  - apply lc_at_app_inv in Hj as [H1 H2].
    rewrite (IH1 j H1 k u Hjk), (IH2 j H2 k u Hjk). reflexivity.
  - apply lc_at_abs_inv in Hj.
    rewrite (IHb (S j) Hj (S k) u). reflexivity. lia.
  - reflexivity.
  - reflexivity.
  - apply lc_at_if_inv in Hj as [H1 [H2 H3]].
    rewrite (IH1 j H1 k u Hjk), (IH2 j H2 k u Hjk), (IH3 j H3 k u Hjk).
    reflexivity.
Qed.

Lemma lc_open_rec : forall (t : tm) (k : nat) (u : tm),
  lc_at (S k) t -> lc_at k u -> lc_at k (open_rec k u t).
Proof.
  induction t as [i|x|t1 IH1 t2 IH2|T b IHb| | |t1 IH1 t2 IH2 t3 IH3];
    intros k u Ht Hu; simpl.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst. exact Hu.
    + apply Nat.eqb_neq in E.
      apply lc_bvar. apply lc_at_bvar_inv in Ht. lia.
  - apply lc_fvar.
  - apply lc_at_app_inv in Ht as [H1 H2].
    apply lc_app; [exact (IH1 k u H1 Hu) | exact (IH2 k u H2 Hu)].
  - apply lc_at_abs_inv in Ht.
    apply lc_abs. apply (IHb (S k) u Ht).
    apply (lc_at_mono k u Hu (S k)); lia.
  - apply lc_true.
  - apply lc_false.
  - apply lc_at_if_inv in Ht as [H1 [H2 H3]].
    apply lc_if; [exact (IH1 k u H1 Hu) | exact (IH2 k u H2 Hu)
                  | exact (IH3 k u H3 Hu)].
Qed.

Lemma open_inv_lc : forall (t : tm) (k : nat) (x : atom),
  lc_at k (open_rec k (tm_fvar x) t) -> lc_at (S k) t.
Proof.
  induction t as [i|x|t1 IH1 t2 IH2|T b IHb| | |t1 IH1 t2 IH2 t3 IH3];
    intros k y H; simpl in H.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst. apply lc_bvar. lia.
    + apply lc_bvar. apply lc_at_bvar_inv in H. lia.
  - apply lc_fvar.
  - apply lc_at_app_inv in H as [H1 H2].
    apply lc_app; [exact (IH1 k y H1) | exact (IH2 k y H2)].
  - apply lc_at_abs_inv in H. apply lc_abs. apply (IHb (S k) y H).
  - apply lc_true.
  - apply lc_false.
  - apply lc_at_if_inv in H as [H1 [H2 H3]].
    apply lc_if; [exact (IH1 k y H1) | exact (IH2 k y H2)
                  | exact (IH3 k y H3)].
Qed.

(** *** Free variables and substitution *)

Fixpoint fvars (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_app t1 t2 => fvars t1 ++ fvars t2
  | tm_abs _ b => fvars b
  | tm_true => []
  | tm_false => []
  | tm_if t1 t2 t3 => fvars t1 ++ (fvars t2 ++ fvars t3)
  end.

Fixpoint subst (σ : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => σ x
  | tm_app t1 t2 => tm_app (subst σ t1) (subst σ t2)
  | tm_abs T b => tm_abs T (subst σ b)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (subst σ t1) (subst σ t2) (subst σ t3)
  end.

Lemma subst_agree : forall (σ σ' : atom -> tm) (t : tm),
  (forall x, In x (fvars t) -> σ x = σ' x) ->
  subst σ t = subst σ' t.
Proof.
  intros σ σ' t. induction t as
    [i|x|t1 IH1 t2 IH2|T b IHb| | |t1 IH1 t2 IH2 t3 IH3]; intros Hag.
  - reflexivity.
  - simpl. apply Hag. simpl. auto.
  - simpl.
    assert (E1 : subst σ t1 = subst σ' t1)
      by (apply IH1; intros y Hy; apply Hag; apply in_app_iff; left; exact Hy).
    assert (E2 : subst σ t2 = subst σ' t2)
      by (apply IH2; intros y Hy; apply Hag; apply in_app_iff; right; exact Hy).
    rewrite E1, E2. reflexivity.
  - simpl. f_equal. apply IHb. intros y Hy. apply Hag. exact Hy.
  - reflexivity.
  - reflexivity.
  - simpl.
    assert (E1 : subst σ t1 = subst σ' t1)
      by (apply IH1; intros y Hy; apply Hag; apply in_app_iff; left; exact Hy).
    assert (E2 : subst σ t2 = subst σ' t2)
      by (apply IH2; intros y Hy; apply Hag;
          apply in_app_iff; right; apply in_app_iff; left; exact Hy).
    assert (E3 : subst σ t3 = subst σ' t3)
      by (apply IH3; intros y Hy; apply Hag;
          apply in_app_iff; right; apply in_app_iff; right; exact Hy).
    rewrite E1, E2, E3. reflexivity.
Qed.

Lemma subst_open_rec : forall (σ : atom -> tm) (t u : tm) (k : nat),
  (forall x, lc (σ x)) ->
  subst σ (open_rec k u t) = open_rec k (subst σ u) (subst σ t).
Proof.
  intros σ t. induction t as
    [i|x|t1 IH1 t2 IH2|T b IHb| | |t1 IH1 t2 IH2 t3 IH3];
    intros u k Hσ; simpl.
  - destruct (Nat.eqb k i); reflexivity.
  - rewrite (open_rec_lc_gen (σ x) 0 (Hσ x) k (subst σ u) (Nat.le_0_l k)).
    reflexivity.
  - rewrite (IH1 u k Hσ), (IH2 u k Hσ). reflexivity.
  - rewrite (IHb u (S k) Hσ). reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite (IH1 u k Hσ), (IH2 u k Hσ), (IH3 u k Hσ). reflexivity.
Qed.

Lemma lc_at_subst : forall (σ : atom -> tm) (t : tm) (k : nat),
  (forall x, lc (σ x)) -> lc_at k t -> lc_at k (subst σ t).
Proof.
  intros σ t. induction t as
    [i|x|t1 IH1 t2 IH2|T b IHb| | |t1 IH1 t2 IH2 t3 IH3];
    intros k Hσ Hk; simpl.
  - exact Hk.
  - apply lc_at_mono with (k := 0); [apply Hσ | lia].
  - apply lc_at_app_inv in Hk as [H1 H2].
    apply lc_app; [exact (IH1 k Hσ H1) | exact (IH2 k Hσ H2)].
  - apply lc_at_abs_inv in Hk. apply lc_abs. apply (IHb (S k) Hσ Hk).
  - apply lc_true.
  - apply lc_false.
  - apply lc_at_if_inv in Hk as [H1 [H2 H3]].
    apply lc_if; [exact (IH1 k Hσ H1) | exact (IH2 k Hσ H2)
                  | exact (IH3 k Hσ H3)].
Qed.

Lemma subst_id : forall (t : tm), subst (fun x => tm_fvar x) t = t.
Proof.
  induction t as [i|x|t1 IH1 t2 IH2|T b IHb| | |t1 IH1 t2 IH2 t3 IH3];
    simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IHb. reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IH1, IH2, IH3. reflexivity.
Qed.

(** *** Basic properties of strong normalization *)

Lemma sn_step : forall (t : tm), strongly_normalizing t ->
  forall t', t --> t' -> strongly_normalizing t'.
Proof.
  intros t Hsn. destruct Hsn as [t0 Hall].
  intros t' Hstep. apply Hall. exact Hstep.
Qed.

Lemma step_abs_inv : forall (T : ty) (b t' : tm),
  ~ (tm_abs T b --> t').
Proof.
  intros T b t' H. inversion H.
Qed.

Lemma sn_abs : forall (T : ty) (b : tm), strongly_normalizing (tm_abs T b).
Proof.
  intros T b. apply SN_intro. intros t' H.
  exfalso. apply (step_abs_inv T b t'). exact H.
Qed.

Lemma step_true_inv : forall t', ~ (tm_true --> t').
Proof. intros t' H. inversion H. Qed.

Lemma step_false_inv : forall t', ~ (tm_false --> t').
Proof. intros t' H. inversion H. Qed.

Lemma sn_true : strongly_normalizing tm_true.
Proof. apply SN_intro. intros t' H. inversion H. Qed.

Lemma sn_false : strongly_normalizing tm_false.
Proof. apply SN_intro. intros t' H. inversion H. Qed.

Lemma value_lc : forall (v : tm), value v -> lc v.
Proof.
  intros v H. destruct H as [T b Hlc | |].
  - exact Hlc.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma lc_step : forall (t t' : tm), t --> t' -> lc t -> lc t'.
Proof.
  intros t t' Hstep. induction Hstep as
    [T b v Hlcabs Hvalv
    | t1 t1' t2 Hstep1 IH1 Hlct2
    | v1 t2 t2' Hval1 Hstep2 IH2
    | t1 t2 Hlct1 Hlct2
    | t1 t2 Hlct1 Hlct2
    | t1 t1' t2 t3 Hstep1 IH1 Hlct2 Hlct3];
    intros Hlc.
  - apply lc_at_app_inv in Hlc as [H1 H2].
    apply lc_at_abs_inv in H1.
    exact (lc_open_rec b 0 v H1 H2).
  - apply lc_at_app_inv in Hlc as [H1 H2].
    apply lc_app; [exact (IH1 H1) | exact H2].
  - apply lc_at_app_inv in Hlc as [H1 H2].
    apply lc_app; [exact H1 | exact (IH2 H2)].
  - apply lc_at_if_inv in Hlc as [H1 [H2 H3]]. exact H2.
  - apply lc_at_if_inv in Hlc as [H1 [H2 H3]]. exact H3.
  - apply lc_at_if_inv in Hlc as [H1 [H2 H3]].
    apply lc_if; [exact (IH1 H1) | exact H2 | exact H3].
Qed.

(** *** The logical relation *)

Fixpoint C (T : ty) (t : tm) {struct T} : Prop :=
  lc t /\
  strongly_normalizing t /\
  match T with
  | Ty_Bool => True
  | Ty_Arrow T1 T2 => forall u, C T1 u -> C T2 (tm_app t u)
  end.

Lemma C_lc : forall (T : ty) (t : tm), C T t -> lc t.
Proof.
  intros T t H. destruct T; simpl in H; apply (proj1 H).
Qed.

Lemma C_sn : forall (T : ty) (t : tm), C T t -> strongly_normalizing t.
Proof.
  intros T t H. destruct T; simpl in H; apply (proj1 (proj2 H)).
Qed.

Lemma C_app : forall (T1 T2 : ty) (t u : tm),
  C (Ty_Arrow T1 T2) t -> C T1 u -> C T2 (tm_app t u).
Proof.
  intros T1 T2 t u H Hu. simpl in H.
  apply (proj2 (proj2 H)). exact Hu.
Qed.

(** *** Environments and closure under one step *)

Definition env_ok (Gamma : context) (σ : atom -> tm) : Prop :=
  (forall x, lc (σ x)) /\
  (forall x T, Gamma x = Some T -> C T (σ x)).

Definition subst_env (σ : atom -> tm) (x : atom) (u : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then u else σ y.

Lemma subst_env_same : forall (σ : atom -> tm) (x : atom) (u : tm),
  subst_env σ x u x = u.
Proof.
  intros. unfold subst_env. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma env_ok_update : forall (Gamma : context) (σ : atom -> tm)
  (x : atom) (T : ty) (u : tm),
  env_ok Gamma σ -> C T u -> env_ok (update Gamma x T) (subst_env σ x u).
Proof.
  intros Gamma σ x T u [Hlcall Hdom] Cu. split.
  - intros y. unfold subst_env.
    destruct (Nat.eqb x y); [apply C_lc with (T := T); exact Cu | apply Hlcall].
  - intros y Ty Hty. unfold update in Hty. unfold subst_env.
    destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst. injection Hty as Heq. subst. exact Cu.
    + apply Hdom. exact Hty.
Qed.

Lemma C_step : forall (T : ty) (t t' : tm),
  C T t -> t --> t' -> C T t'.
Proof.
  induction T as [| T1 IH1 T2 IH2]; intros t t' HC Hstep.
  - simpl in HC. destruct HC as [Hlc [Hsn _]].
    simpl. split.
    + exact (lc_step t t' Hstep Hlc).
    + split.
      * exact (sn_step t Hsn t' Hstep).
      * exact I.
  - simpl in HC. destruct HC as [Hlc [Hsn Hclos]].
    simpl. split.
    + exact (lc_step t t' Hstep Hlc).
    + split.
      * exact (sn_step t Hsn t' Hstep).
      * intros u Cu.
        apply IH2 with (t := tm_app t u).
        -- apply Hclos. exact Cu.
        -- apply ST_App1 with (t1 := t) (t1' := t') (t2 := u);
             [exact Hstep | exact (C_lc T1 u Cu)].
Qed.

(** *** Terms whose head is not an abstraction *)

Lemma C_intro_notabs : forall (T : ty) (t : tm),
  (forall (T0 : ty) (b : tm), t <> tm_abs T0 b) ->
  lc t ->
  (forall t', t --> t' -> C T t') ->
  C T t.
Proof.
  induction T as [| T1 IH1 T2 IH2]; intros t Hnotabs Hlc Hreds.
  - simpl. split; [exact Hlc | split].
    + apply SN_intro. intros t' Hstep.
      apply C_sn with (T := Ty_Bool). apply Hreds. exact Hstep.
    + exact I.
  - simpl. split; [exact Hlc | split].
    + apply SN_intro. intros t' Hstep.
      apply C_sn with (T := Ty_Arrow T1 T2). apply Hreds. exact Hstep.
    + assert (Hclos : forall u, C T1 u -> C T2 (tm_app t u)).
      { intros u Cu.
        assert (Hsn : strongly_normalizing u)
          by (apply C_sn with (T := T1); exact Cu).
        revert Cu.
        induction Hsn as [u0 Hreds0 IH].
        intros Cu.
        apply IH2.
        * intros T0 b Heq. discriminate Heq.
        * apply lc_app; [exact Hlc | exact (C_lc T1 u0 Cu)].
        * intros z Hz. inversion Hz as
            [T0 b v Hlcabs Hvalv
            | ta ta' tb Hstepa Hlctb
            | va tb tb' Hvala Hstepb
            | u1 u2 Hlcu1 Hlcu2
            | u1 u2 Hlcu1 Hlcu2
            | ta ta' tb tc Hstepa Hlctb Hlctc]; subst.
          -- exfalso. apply (Hnotabs T0 b). reflexivity.
          -- exact (C_app T1 T2 ta' u0 (Hreds ta' Hstepa) Cu).
          -- exact (IH tb' Hstepb (C_step T1 u0 tb' Cu Hstepb)). }
      exact Hclos.
Qed.

(** *** Abstractions *)

Lemma C_abs : forall (T1 T2 : ty) (b : tm),
  lc (tm_abs T1 b) ->
  (forall u, value u -> C T1 u -> C T2 (open b u)) ->
  C (Ty_Arrow T1 T2) (tm_abs T1 b).
Proof.
  intros T1 T2 b Hlc Hsem.
  simpl. split; [exact Hlc | split].
  - apply sn_abs.
  - assert (Hclos : forall u,
        C T1 u -> C T2 (tm_app (tm_abs T1 b) u)).
    { intros u Cu.
      assert (Hsn : strongly_normalizing u)
        by (apply C_sn with (T := T1); exact Cu).
      revert Cu.
      induction Hsn as [u0 Hreds0 IH].
      intros Cu.
      apply C_intro_notabs.
      - intros T0 b0 Heq. discriminate Heq.
      - apply lc_app; [exact Hlc | exact (C_lc T1 u0 Cu)].
      - intros z Hz. inversion Hz as
          [T0 b0 v Hlcabs Hvalv
          | ta ta' tb Hstepa Hlctb
          | va tb tb' Hvala Hstepb
          | u1 u2 Hlcu1 Hlcu2
          | u1 u2 Hlcu1 Hlcu2
          | ta ta' tb tc Hstepa Hlctb Hlctc]; subst.
        + apply Hsem; [exact Hvalv | exact Cu].
        + exfalso. exact (step_abs_inv T1 b ta' Hstepa).
        + exact (IH tb' Hstepb (C_step T1 u0 tb' Cu Hstepb)). }
    exact Hclos.
Qed.

(** *** If-then-else *)

Lemma C_if : forall (T : ty) (b1 b2 b3 : tm),
  C Ty_Bool b1 -> C T b2 -> C T b3 -> C T (tm_if b1 b2 b3).
Proof.
  intros T b1 b2 b3 C1 C2 C3.
  assert (H : forall c1,
    strongly_normalizing c1 -> C Ty_Bool c1 -> C T (tm_if c1 b2 b3)).
  { intros c1 Hsn. induction Hsn as [c0 Hreds IH]. intros C1'.
    apply C_intro_notabs.
    - intros T0 b Heq. discriminate Heq.
    - apply lc_if; [exact (C_lc Ty_Bool c0 C1')
                  | exact (C_lc T b2 C2) | exact (C_lc T b3 C3)].
    - intros z Hz. inversion Hz as
        [T0 b v Hlcabs Hvalv
        | ta ta' tb Hstepa Hlctb
        | va tb tb' Hvala Hstepb
        | u1 u2 Hlcu1 Hlcu2
        | u1 u2 Hlcu1 Hlcu2
        | ta ta' tb tc Hstepa Hlctb Hlctc]; subst.
      + exact C2.
      + exact C3.
      + exact (IH ta' Hstepa (C_step Ty_Bool c0 ta' C1' Hstepa)). }
  apply H.
  - apply C_sn with (T := Ty_Bool). exact C1.
  - exact C1.
Qed.

(** *** Well-typed terms are locally closed *)

Lemma has_type_lc : forall (Gamma : context) (t : tm) (T : ty),
  has_type Gamma t T -> lc t.
Proof.
  intros Gamma t T H. induction H as
    [Gamma x T Hx
    | L Gamma T1 T2 t1 Hbody IHbody
    | Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
    | Gamma
    | Gamma
    | Gamma t1 t2 t3 T H1 IH1 H2 IH2 H3 IH3].
  - apply lc_fvar.
  - apply lc_abs.
    set (x := fresh (L ++ fvars t1)).
    assert (HxL : ~ In x L).
    { intro Hin. apply (fresh_notin (L ++ fvars t1)).
      apply in_app_iff. left. exact Hin. }
    assert (Hx : lc (open t1 (tm_fvar x))).
    { apply (IHbody x HxL). }
    apply (open_inv_lc t1 0 x).
    change (lc_at 0 (open_rec 0 (tm_fvar x) t1)).
    exact Hx.
  - apply lc_app; assumption.
  - apply lc_true.
  - apply lc_false.
  - apply lc_if; assumption.
Qed.

(** *** Fundamental theorem *)

Lemma fundamental : forall (Gamma : context) (t : tm) (T : ty),
  has_type Gamma t T ->
  forall σ, env_ok Gamma σ -> C T (subst σ t).
Proof.
  intros Gamma t T Hty.
  induction Hty as
    [Gamma x T Hx
    | L Gamma T1 T2 t1 Hbody IHbody
    | Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
    | Gamma
    | Gamma
    | Gamma t1 t2 t3 T H1 IH1 H2 IH2 H3 IH3];
    intros σ Hok.
  - simpl. apply (proj2 Hok). exact Hx.
  - simpl.
    set (x := fresh (L ++ fvars t1)).
    assert (HxL : ~ In x L).
    { intro Hin. apply (fresh_notin (L ++ fvars t1)).
      apply in_app_iff. left. exact Hin. }
    assert (Hxnf : ~ In x (fvars t1)).
    { intro Hin. apply (fresh_notin (L ++ fvars t1)).
      apply in_app_iff. right. exact Hin. }
    apply C_abs.
    + apply lc_abs.
      apply (lc_at_subst σ t1 1 (proj1 Hok)).
      apply (open_inv_lc t1 0 x).
      change (lc_at 0 (open_rec 0 (tm_fvar x) t1)).
      apply has_type_lc with (Gamma := update Gamma x T1) (T := T2).
      apply Hbody. exact HxL.
    + intros u Hval Cu.
      pose (σ' := subst_env σ x u).
      assert (Hok' : env_ok (update Gamma x T1) σ').
      { apply env_ok_update; [exact Hok | exact Cu]. }
      specialize (IHbody x HxL σ' Hok').
      assert (Hσ'lc : forall y, lc (σ' y)).
      { intros y. unfold σ', subst_env.
        destruct (Nat.eqb x y); [apply value_lc; exact Hval | apply (proj1 Hok)]. }
      assert (Hsub : subst σ' (open t1 (tm_fvar x)) = open (subst σ t1) u).
      { change (subst σ' (open_rec 0 (tm_fvar x) t1)
                = open_rec 0 u (subst σ t1)).
        rewrite (subst_open_rec σ' t1 (tm_fvar x) 0 Hσ'lc).
        assert (Hagree : forall y, In y (fvars t1) -> σ y = σ' y).
        { intros y Hy. unfold σ', subst_env.
          destruct (Nat.eqb x y) eqn:E.
          - apply Nat.eqb_eq in E. subst. exfalso. apply Hxnf. exact Hy.
          - reflexivity. }
        assert (Hsubst : subst σ' t1 = subst σ t1).
        { symmetry. apply subst_agree. exact Hagree. }
        change (open_rec 0 (subst_env σ x u x) (subst σ' t1)
                = open_rec 0 u (subst σ t1)).
        rewrite (subst_env_same σ x u).
        rewrite Hsubst. reflexivity. }
      rewrite Hsub in IHbody. exact IHbody.
  - simpl. eapply C_app.
    + apply IH1. exact Hok.
    + apply IH2. exact Hok.
  - simpl. split; [apply lc_true | split; [apply sn_true | exact I]].
  - simpl. split; [apply lc_false | split; [apply sn_false | exact I]].
  - simpl. eapply C_if.
    + apply IH1. exact Hok.
    + apply IH2. exact Hok.
    + apply IH3. exact Hok.
Qed.

(** *** Target theorem *)

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  assert (Hok : env_ok empty (fun x => tm_fvar x)).
  { split.
    - intros x. apply lc_fvar.
    - intros x Ty Hx. unfold empty in Hx. discriminate Hx. }
  pose proof (fundamental empty t T Hty (fun x => tm_fvar x) Hok) as HC.
  rewrite subst_id in HC.
  apply (C_sn T t HC).
Qed.

End STLCCBVNormalizationTask.
