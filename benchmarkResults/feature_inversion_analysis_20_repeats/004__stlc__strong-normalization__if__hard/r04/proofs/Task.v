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

(** ** Auxiliary development for the strong normalization proof. *)

(** Free variables of a term, used to pick fresh atoms. *)

Fixpoint fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ => nil
  | tm_fvar x => x :: nil
  | tm_app t1 t2 => fv t1 ++ fv t2
  | tm_abs _ t1 => fv t1
  | tm_true => nil
  | tm_false => nil
  | tm_if t1 t2 t3 => fv t1 ++ fv t2 ++ fv t3
  end.

Fixpoint max_list (l : list nat) : nat :=
  match l with
  | nil => 0
  | x :: l' => Nat.max x (max_list l')
  end.

Lemma in_max_list : forall (l : list nat) (x : nat), In x l -> x <= max_list l.
Proof.
  induction l as [| a l IH]; intros x Hx; simpl in *.
  - destruct Hx.
  - destruct Hx as [-> | Hx].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; eauto | apply Nat.le_max_r].
Qed.

Lemma fresh_two : forall l1 l2 : list atom, exists x, ~ In x l1 /\ ~ In x l2.
Proof.
  intros l1 l2. exists (S (max_list (l1 ++ l2))). split; intro H.
  - assert (Hin : In (S (max_list (l1 ++ l2))) (l1 ++ l2))
      by (apply in_or_app; left; exact H).
    apply in_max_list in Hin.
    assert (Hlt : S (max_list (l1 ++ l2)) < S (max_list (l1 ++ l2)))
      by (apply Nat.lt_succ_r; exact Hin).
    apply (Nat.lt_irrefl _ Hlt).
  - assert (Hin : In (S (max_list (l1 ++ l2))) (l1 ++ l2))
      by (apply in_or_app; right; exact H).
    apply in_max_list in Hin.
    assert (Hlt : S (max_list (l1 ++ l2)) < S (max_list (l1 ++ l2)))
      by (apply Nat.lt_succ_r; exact Hin).
    apply (Nat.lt_irrefl _ Hlt).
Qed.

Lemma not_in_app_l : forall (x : atom) (l1 l2 : list atom),
  ~ In x (l1 ++ l2) -> ~ In x l1.
Proof.
  intros x l1 l2 H Hin. apply H. apply in_or_app. left. exact Hin.
Qed.

Lemma not_in_app_r : forall (x : atom) (l1 l2 : list atom),
  ~ In x (l1 ++ l2) -> ~ In x l2.
Proof.
  intros x l1 l2 H Hin. apply H. apply in_or_app. right. exact Hin.
Qed.

(** ** Monotonicity, opening, and invariance of local closure *)

Lemma lc_at_mono : forall (t : tm) (k k' : nat),
  k <= k' -> lc_at k t -> lc_at k' t.
Proof.
  intros t. induction t as [i | x | t1 IH1 t2 IH2 | T0 t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
    intros k k' Hle Hlc; inversion Hlc; subst; simpl.
  - apply lc_bvar. lia.
  - apply lc_fvar.
  - apply lc_app; [apply (IH1 k k' Hle) | apply (IH2 k k' Hle)]; assumption.
  - apply lc_abs. apply (IH1 (S k) (S k')); [lia | assumption].
  - apply lc_true.
  - apply lc_false.
  - apply lc_if; [apply (IH1 k k' Hle) | apply (IH2 k k' Hle) | apply (IH3 k k' Hle)];
      assumption.
Qed.

Lemma lc_open_rec : forall (t : tm) (k : nat) (u : tm),
  lc_at (S k) t -> lc_at k u -> lc_at k (open_rec k u t).
Proof.
  intros t. induction t as [i | x | t1 IH1 t2 IH2 | T0 t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
    intros k u Ht Hu; simpl.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst i. exact Hu.
    + apply lc_bvar. inversion Ht; subst. apply Nat.eqb_neq in E. lia.
  - apply lc_fvar.
  - inversion Ht; subst. apply lc_app; [apply (IH1 k u) | apply (IH2 k u)]; assumption.
  - inversion Ht; subst. apply lc_abs. apply (IH1 (S k) u);
      [assumption | apply (lc_at_mono u k (S k)); [lia | exact Hu]].
  - apply lc_true.
  - apply lc_false.
  - inversion Ht; subst. apply lc_if;
      [apply (IH1 k u) | apply (IH2 k u) | apply (IH3 k u)]; assumption.
Qed.

Lemma lc_open_rec_inv : forall (t : tm) (k : nat) (u : tm),
  lc_at k (open_rec k u t) -> lc_at k u -> lc_at (S k) t.
Proof.
  intros t. induction t as [i | x | t1 IH1 t2 IH2 | T0 t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
    intros k u H1 Hu; simpl in *.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst i. apply lc_bvar. lia.
    + apply lc_bvar. inversion H1; subst. apply Nat.eqb_neq in E. lia.
  - apply lc_fvar.
  - inversion H1; subst. apply lc_app; [apply (IH1 k u) | apply (IH2 k u)]; assumption.
  - inversion H1; subst. apply lc_abs. apply (IH1 (S k) u);
      [assumption | apply (lc_at_mono u k (S k)); [lia | exact Hu]].
  - apply lc_true.
  - apply lc_false.
  - inversion H1; subst. apply lc_if;
      [apply (IH1 k u) | apply (IH2 k u) | apply (IH3 k u)]; assumption.
Qed.

(** Opening a locally closed term is the identity, since a locally closed
    term has no free bound-variable indices. *)

Lemma lc_open_rec_id : forall (t : tm) (j k : nat) (u : tm),
  lc_at k t -> k <= j -> open_rec j u t = t.
Proof.
  intros t. induction t as [i | x | t1 IH1 t2 IH2 | T0 t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
    intros j k u Hlc Hle; simpl.
  - destruct (Nat.eqb j i) eqn:E.
    + apply Nat.eqb_eq in E. inversion Hlc; subst. lia.
    + reflexivity.
  - reflexivity.
  - inversion Hlc; subst. f_equal; [apply (IH1 j k u) | apply (IH2 j k u)]; assumption.
  - inversion Hlc; subst. f_equal. apply (IH1 (S j) (S k) u); [assumption | lia].
  - reflexivity.
  - reflexivity.
  - inversion Hlc; subst.
    assert (E1 : open_rec j u t1 = t1) by (apply (IH1 j k u); assumption).
    assert (E2 : open_rec j u t2 = t2) by (apply (IH2 j k u); assumption).
    assert (E3 : open_rec j u t3 = t3) by (apply (IH3 j k u); assumption).
    rewrite E1, E2, E3. reflexivity.
Qed.

(** ** Basic facts about values and strong normalization *)

Lemma value_lc : forall (v : tm), value v -> locally_closed v.
Proof.
  intros v Hv. induction Hv.
  - assumption.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma value_no_step : forall (v : tm), value v -> forall t, ~ step v t.
Proof.
  intros v Hv t Hs. induction Hv; inversion Hs.
Qed.

Lemma SN_step : forall (t t' : tm),
  strongly_normalizing t -> step t t' -> strongly_normalizing t'.
Proof.
  intros t t' H. induction H as [t0 Hpre IH]. intros Hs. apply Hpre. exact Hs.
Qed.

Lemma SN_abs : forall (T : ty) (t : tm), strongly_normalizing (tm_abs T t).
Proof.
  intros T t. apply SN_intro. intros t' Hs. inversion Hs.
Qed.

Lemma SN_true : strongly_normalizing tm_true.
Proof. apply SN_intro. intros t' Hs. inversion Hs. Qed.

Lemma SN_false : strongly_normalizing tm_false.
Proof. apply SN_intro. intros t' Hs. inversion Hs. Qed.

(** ** Local closure is preserved by reduction *)

Lemma lc_at_app_inv : forall (k : nat) (t1 t2 : tm),
  lc_at k (tm_app t1 t2) -> lc_at k t1 /\ lc_at k t2.
Proof. intros k t1 t2 H; inversion H; auto. Qed.

Lemma lc_at_abs_inv : forall (k : nat) (T : ty) (t : tm),
  lc_at k (tm_abs T t) -> lc_at (S k) t.
Proof. intros k T t H; inversion H; auto. Qed.

Lemma lc_at_if_inv : forall (k : nat) (t1 t2 t3 : tm),
  lc_at k (tm_if t1 t2 t3) -> lc_at k t1 /\ lc_at k t2 /\ lc_at k t3.
Proof. intros k t1 t2 t3 H; inversion H; auto. Qed.

Lemma lc_step_fwd : forall (s s' : tm),
  step s s' -> locally_closed s -> locally_closed s'.
Proof.
  intros s s' Hs. induction Hs as [T t v Hlcabs Hv
                                 | t1 t1' t2 Hstep IH Hlc2
                                 | v1 t2 t2' Hv1 Hstep IH
                                 | t1 t2 Hlc1 Hlc2
                                 | t1 t2 Hlc1 Hlc2
                                 | t1 t1' t2 t3 Hstep IH Hlc2 Hlc3];
    intros Hlc; unfold locally_closed in *.
  - apply lc_open_rec with (k := 0).
    + apply (lc_at_abs_inv 0 T t). apply (proj1 (lc_at_app_inv 0 (tm_abs T t) v Hlc)).
    + apply (proj2 (lc_at_app_inv 0 (tm_abs T t) v Hlc)).
  - destruct (lc_at_app_inv 0 t1 t2 Hlc) as [H1 H2].
    apply lc_app; [apply IH; exact H1 | exact H2].
  - destruct (lc_at_app_inv 0 v1 t2 Hlc) as [H1 H2].
    apply lc_app; [apply value_lc; exact Hv1 | apply IH; exact H2].
  - destruct (lc_at_if_inv 0 tm_true t1 t2 Hlc) as [H1 [H2 H3]].
    exact H2.
  - destruct (lc_at_if_inv 0 tm_false t1 t2 Hlc) as [H1 [H2 H3]].
    exact H3.
  - destruct (lc_at_if_inv 0 t1 t2 t3 Hlc) as [H1 [H2 H3]].
    apply lc_if; [apply IH; exact H1 | exact H2 | exact H3].
Qed.

(** ** The type-indexed logical relation

    A term is reducible at [Bool] when it is strongly normalizing; at a
    function type it must moreover map every reducible argument to a
    reducible application.  Locally-closedness is carried along so that
    congruence rules of the operational semantics can be applied. *)

Fixpoint R (T : ty) (t : tm) {struct T} : Prop :=
  locally_closed t /\
  strongly_normalizing t /\
  match T with
  | Ty_Bool => True
  | Ty_Arrow T1 T2 => forall u, R T1 u -> R T2 (tm_app t u)
  end.

Lemma R_lc : forall (T : ty) (t : tm), R T t -> locally_closed t.
Proof.
  intros T; destruct T; simpl; intros t H; destruct H as [Hlc _]; exact Hlc.
Qed.

Lemma R_SN : forall (T : ty) (t : tm), R T t -> strongly_normalizing t.
Proof.
  intros T; destruct T; simpl; intros t H; destruct H as [Hlc [Hsn _]]; exact Hsn.
Qed.

Lemma R_step_fwd : forall (T : ty) (s s' : tm),
  R T s -> step s s' -> R T s'.
Proof.
  intros T. induction T as [| A IHA B IHB]; intros s s' HR Hs.
  - simpl in *. destruct HR as [Hlc [Hsn _]]. split.
    + eapply lc_step_fwd; eauto.
    + split.
      * apply SN_step with (t := s); assumption.
      * exact I.
  - simpl in *. destruct HR as [Hlc [Hsn Happ]]. split.
    + eapply lc_step_fwd; eauto.
    + split.
      * apply SN_step with (t := s); assumption.
      * intros u Hu. apply (IHB (tm_app s u) (tm_app s' u)).
        -- apply Happ. exact Hu.
        -- apply ST_App1; [exact Hs | apply R_lc in Hu; exact Hu].
Qed.

(** A term which is not a value and whose one-step reducts are all reducible
    is itself reducible.  This is the key inversion/expansion principle;
    applications are never values, so their reducts only arise from the
    congruence rule for the function position. *)

Lemma R_of_reducts : forall (T : ty) (s : tm),
  locally_closed s -> ~ value s ->
  (forall s', step s s' -> R T s') -> R T s.
Proof.
  intros T. induction T as [| A IHA B IHB]; intros s Hlc Hnv Hred.
  - simpl. split; [exact Hlc | split].
    + apply SN_intro. intros s' Hs. apply R_SN with (T := Ty_Bool). apply Hred. exact Hs.
    + exact I.
  - simpl. split; [exact Hlc | split].
    + apply SN_intro. intros s' Hs. apply R_SN with (T := Ty_Arrow A B). apply Hred. exact Hs.
    + intros w Hw.
      apply (IHB (tm_app s w)).
      * apply lc_app; [exact Hlc | apply R_lc in Hw; exact Hw].
      * intro Hv; inversion Hv.
      * intros u Hu. inversion Hu; subst.
        -- (* ST_AppAbs *) exfalso. apply Hnv. apply v_abs. assumption.
        -- (* ST_App1 *) apply (proj2 (proj2 (Hred t1' H1))). exact Hw.
        -- (* ST_App2 *) exfalso. apply Hnv. exact H1.
Qed.

(** Beta-expansion for abstractions: if opening the body with a reducible
    argument is reducible, then applying the abstraction is reducible. *)

Lemma R_beta : forall (T1 T2 : ty) (t u0 : tm),
  locally_closed (tm_abs T1 t) ->
  R T1 u0 ->
  (forall u', R T1 u' -> R T2 (open t u')) ->
  R T2 (tm_app (tm_abs T1 t) u0).
Proof.
  intros T1 T2 t u0 Hlcabs Hu0 H.
  assert (main : forall u, strongly_normalizing u ->
      R T1 u -> (forall u', R T1 u' -> R T2 (open t u')) ->
      R T2 (tm_app (tm_abs T1 t) u)).
  { intros u Hsn. induction Hsn as [u1 Hstep IH]. intros HR Hgen.
    apply R_of_reducts with (s := tm_app (tm_abs T1 t) u1).
    - apply lc_app; [exact Hlcabs | apply R_lc in HR; exact HR].
    - intro Hv; inversion Hv.
    - intros s' Hs. inversion Hs; subst.
      + (* ST_AppAbs *) apply Hgen. exact HR.
      + (* ST_App1 *) exfalso.
        exact (value_no_step (tm_abs T1 t) (v_abs T1 t Hlcabs) t1' H2).
      + (* ST_App2 *) apply IH; [exact H4 | apply R_step_fwd with (s := u1); assumption | exact Hgen].
  }
  apply main; [exact (R_SN T1 u0 Hu0) | exact Hu0 | exact H].
Qed.

(** If-expansion: an if-then-else whose condition is reducible at [Bool] and
    whose branches are reducible at the result type is reducible. *)

Lemma R_if : forall (T : ty) (u1 u2 u3 : tm),
  R Ty_Bool u1 -> R T u2 -> R T u3 -> R T (tm_if u1 u2 u3).
Proof.
  intros T u1 u2 u3 H1 H2 H3.
  assert (main : forall u1, strongly_normalizing u1 ->
      R Ty_Bool u1 -> R T u2 -> R T u3 -> R T (tm_if u1 u2 u3)).
  { intros ucond Hsn. induction Hsn as [u1a Hstep IH]. intros HR1 HR2 HR3.
    apply R_of_reducts with (s := tm_if u1a u2 u3).
    - apply lc_if; [apply R_lc in HR1; exact HR1 | apply R_lc in HR2; exact HR2 | apply R_lc in HR3; exact HR3].
    - intro Hv; inversion Hv.
    - intros s' Hs. inversion Hs; subst.
      + (* ST_IfTrue *) exact HR2.
      + (* ST_IfFalse *) exact HR3.
      + (* ST_If *) apply IH; [exact H5 | apply R_step_fwd with (s := u1a); assumption | exact HR2 | exact HR3].
  }
  apply main; [exact (R_SN Ty_Bool u1 H1) | exact H1 | exact H2 | exact H3].
Qed.

Lemma R_fvar : forall (T : ty) (z : atom), R T (tm_fvar z).
Proof.
  intros T z.
  apply R_of_reducts with (s := tm_fvar z).
  - apply lc_fvar.
  - intro Hv; inversion Hv.
  - intros s' Hs; inversion Hs.
Qed.

(** ** Free-variable substitution *)

Fixpoint subst_env (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_app t1 t2 => tm_app (subst_env sigma t1) (subst_env sigma t2)
  | tm_abs T t1 => tm_abs T (subst_env sigma t1)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 =>
      tm_if (subst_env sigma t1) (subst_env sigma t2) (subst_env sigma t3)
  end.

Lemma subst_env_id : forall (t : tm), subst_env (fun x => tm_fvar x) t = t.
Proof.
  induction t; simpl; congruence.
Qed.

Definition env_update (sigma : atom -> tm) (x : atom) (u : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then u else sigma y.

Definition env_ok (Gamma : context) (sigma : atom -> tm) : Prop :=
  (forall x, locally_closed (sigma x)) /\
  (forall x T, Gamma x = Some T -> R T (sigma x)).

Lemma env_ok_update : forall (Gamma : context) (sigma : atom -> tm)
                             (x : atom) (T : ty) (u : tm),
  env_ok Gamma sigma -> R T u ->
  env_ok (update Gamma x T) (env_update sigma x u).
Proof.
  intros Gamma sigma x T u [Hlcs Henv] Hu. split.
  - intros y. unfold env_update. destruct (Nat.eqb x y).
    + apply R_lc in Hu. exact Hu.
    + apply Hlcs.
  - intros y S Hy. unfold update, env_update in *.
    destruct (Nat.eqb x y) eqn:E.
    + injection Hy as HS. subst S. exact Hu.
    + apply Henv. exact Hy.
Qed.

(** Substituting into an opened term: opening with a fresh variable and then
    substituting that variable is the same as opening with the substituted
    term directly.  Local closedness of the substitution images is needed so
    that opening does not affect them. *)

Lemma subst_env_open_rec : forall (t : tm) (sigma : atom -> tm)
                                  (x : atom) (u : tm) (k : nat),
  (forall y, locally_closed (sigma y)) ->
  ~ In x (fv t) ->
  subst_env (env_update sigma x u) (open_rec k (tm_fvar x) t)
  = open_rec k u (subst_env sigma t).
Proof.
  intros t. induction t as [i | y | t1 IH1 t2 IH2 | T0 t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
    intros sigma x u k Hsig Hx; simpl.
  - change (subst_env (env_update sigma x u)
              (if Nat.eqb k i then tm_fvar x else tm_bvar i)
            = (if Nat.eqb k i then u else tm_bvar i)).
    destruct (Nat.eqb k i) eqn:E; simpl.
    + unfold env_update. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. exfalso. apply Hx. simpl. left. symmetry. exact E.
    + unfold env_update. rewrite E.
      symmetry. apply lc_open_rec_id with (k := 0); [apply Hsig | lia].
  - assert (Hx1 : ~ In x (fv t1)) by (apply (not_in_app_l x (fv t1) (fv t2)); exact Hx).
    assert (Hx2 : ~ In x (fv t2)) by (apply (not_in_app_r x (fv t1) (fv t2)); exact Hx).
    rewrite (IH1 sigma x u k Hsig Hx1). rewrite (IH2 sigma x u k Hsig Hx2).
    reflexivity.
  - rewrite (IH1 sigma x u (S k) Hsig Hx). reflexivity.
  - reflexivity.
  - reflexivity.
  - assert (Hx1 : ~ In x (fv t1))
      by (apply (not_in_app_l x (fv t1) (fv t2 ++ fv t3)); exact Hx).
    assert (Hx23 : ~ In x (fv t2 ++ fv t3))
      by (apply (not_in_app_r x (fv t1) (fv t2 ++ fv t3)); exact Hx).
    assert (Hx2 : ~ In x (fv t2)) by (apply (not_in_app_l x (fv t2) (fv t3)); exact Hx23).
    assert (Hx3 : ~ In x (fv t3)) by (apply (not_in_app_r x (fv t2) (fv t3)); exact Hx23).
    rewrite (IH1 sigma x u k Hsig Hx1). rewrite (IH2 sigma x u k Hsig Hx2).
    rewrite (IH3 sigma x u k Hsig Hx3). reflexivity.
Qed.

(** ** The fundamental theorem of logical relations *)

Theorem fundamental : forall (Gamma : context) (t : tm) (T : ty),
  <{ Gamma |-- t \in T }> ->
  forall sigma, env_ok Gamma sigma -> R T (subst_env sigma t).
Proof.
  intros Gamma t T Hty.
  induction Hty as [Gamma x T Heq
                 | L Gamma T1 T2 t1 Hpre IHpre
                 | Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
                 | Gamma
                 | Gamma
                 | Gamma t1 t2 t3 T H1 IH1 H2 IH2 H3 IH3];
    intros sigma Henv.
  - (* T_Var *) simpl. apply (proj2 Henv). exact Heq.
  - (* T_Abs *)
    simpl.
    destruct (fresh_two L (fv t1)) as [x [HxL Hxfv]].
    set (body := subst_env sigma t1).
    assert (Hmain : forall u, R T1 u -> R T2 (open body u)).
    { intros u Hu.
      assert (Henv' : env_ok (update Gamma x T1) (env_update sigma x u))
        by (apply env_ok_update; [exact Henv | exact Hu]).
      pose proof (IHpre x HxL (env_update sigma x u) Henv') as Hres.
      unfold open in Hres.
      rewrite (subst_env_open_rec t1 sigma x u 0 (proj1 Henv) Hxfv) in Hres.
      unfold open. unfold body. exact Hres. }
    assert (Hlcbody : locally_closed (tm_abs T1 body)).
    { apply lc_abs.
      pose proof (Hmain (tm_fvar 0) (R_fvar T1 0)) as H0.
      apply R_lc in H0.
      apply (lc_open_rec_inv body 0 (tm_fvar 0)); [exact H0 | apply lc_fvar]. }
    split.
    + exact Hlcbody.
    + split.
      * apply SN_abs.
      * intros u Hu.
        apply R_beta with (T2 := T2) (t := body) (u0 := u);
          [exact Hlcbody | exact Hu | exact Hmain].
  - (* T_App *)
    simpl. apply (proj2 (proj2 (IH1 sigma Henv))). apply IH2. exact Henv.
  - (* T_True *)
    simpl. split; [apply lc_true | split; [apply SN_true | exact I]].
  - (* T_False *)
    simpl. split; [apply lc_false | split; [apply SN_false | exact I]].
  - (* T_If *)
    simpl. apply R_if; [apply IH1 | apply IH2 | apply IH3]; exact Henv.
Qed.

(** ** Target theorem *)

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  assert (Henv : env_ok empty (fun x => tm_fvar x)).
  { split.
    - intros x. apply lc_fvar.
    - intros x S Hx. unfold empty in Hx. discriminate. }
  pose proof (fundamental empty t T Hty (fun x => tm_fvar x) Henv) as HR.
  rewrite subst_env_id in HR.
  apply R_SN in HR. exact HR.
Qed.

End STLCCBVNormalizationTask.
