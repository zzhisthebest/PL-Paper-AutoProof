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

(** * Toolkit for the strong normalization proof. *)

(** ** Free-variable substitution.

    Because the language is locally nameless, substituting terms for free
    variables never captures bound variables: [subst] simply recurses under
    binders without any shifting. *)

Fixpoint subst (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_app t1 t2 => tm_app (subst sigma t1) (subst sigma t2)
  | tm_abs T t1 => tm_abs T (subst sigma t1)
  | tm_true => tm_true
  | tm_false => tm_false
  end.

Definition ids : atom -> tm := fun x => tm_fvar x.

Lemma subst_ids : forall t, subst ids t = t.
Proof.
  induction t; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** ** Free variables, as a list. *)

Fixpoint fvars (t : tm) : list atom :=
  match t with
  | tm_bvar _ => nil
  | tm_fvar x => x :: nil
  | tm_app t1 t2 => fvars t1 ++ fvars t2
  | tm_abs _ t1 => fvars t1
  | tm_true => nil
  | tm_false => nil
  end.

Definition occurs_free (x : atom) (t : tm) : Prop := In x (fvars t).

(** ** Fresh atoms. *)

Fixpoint max_atoms (l : list atom) : atom :=
  match l with
  | nil => 0
  | x :: xs => Nat.max x (max_atoms xs)
  end.

Lemma max_atoms_spec : forall l x, In x l -> x <= max_atoms l.
Proof.
  induction l as [| a l IH]; intros x Hin; simpl in *.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + rewrite Heq. apply Nat.le_max_l.
    + apply Nat.le_trans with (max_atoms l); [apply IH; exact Hin | apply Nat.le_max_r].
Qed.

Definition fresh_atom (l : list atom) : atom := S (max_atoms l).

Lemma fresh_atom_spec : forall l, ~ In (fresh_atom l) l.
Proof.
  intros l Hin. unfold fresh_atom in Hin.
  pose proof (max_atoms_spec l (S (max_atoms l)) Hin). lia.
Qed.

(** ** Local closure: monotonicity, opening, and inversion. *)

Lemma lc_at_mono : forall k k' t, k <= k' -> lc_at k t -> lc_at k' t.
Proof.
  intros k k' t Hle H. revert k' Hle.
  induction H as [k0 i Hlt | k0 x | k0 t1 t2 H1 IH1 H2 IH2 | k0 T t1 H1 IH1 | k0 | k0];
    intros k' Hle.
  - apply lc_bvar. lia.
  - apply lc_fvar.
  - apply lc_app; [apply IH1; lia | apply IH2; lia].
  - apply lc_abs. apply IH1. lia.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma lc_at_S : forall k t, lc_at k t -> lc_at (S k) t.
Proof. intros k t H. apply (lc_at_mono k (S k) t); [lia | exact H]. Qed.

Lemma open_rec_lc_at : forall k t, lc_at k t -> forall j v, k <= j -> open_rec j v t = t.
Proof.
  intros k t H. induction H as [k0 i Hlt | k0 x | k0 t1 t2 H1 IH1 H2 IH2 | k0 T t1 H1 IH1 | k0 | k0];
    intros j v Hle; simpl.
  - destruct (Nat.eqb j i) eqn:E.
    + apply Nat.eqb_eq in E. exfalso. lia.
    + reflexivity.
  - reflexivity.
  - assert (H1' : open_rec j v t1 = t1) by (apply IH1; lia).
    assert (H2' : open_rec j v t2 = t2) by (apply IH2; lia).
    rewrite H1', H2'. reflexivity.
  - assert (H1' : open_rec (S j) v t1 = t1) by (apply IH1; lia).
    rewrite H1'. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma open_rec_lc : forall t v k, locally_closed t -> open_rec k v t = t.
Proof. intros t v k H. apply open_rec_lc_at with (k := 0); [exact H | lia]. Qed.

Lemma lc_open_rec : forall t, forall k u, lc_at (S k) t -> lc_at k u -> lc_at k (open_rec k u t).
Proof.
  induction t; intros k u Ht Hu; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. exact Hu.
    + apply Nat.eqb_neq in E. apply lc_bvar.
      assert (Hlt : n < S k) by (inversion Ht; assumption). lia.
  - apply lc_fvar.
  - inversion Ht; subst. apply lc_app.
    + apply IHt1; [assumption | exact Hu].
    + apply IHt2; [assumption | exact Hu].
  - inversion Ht; subst. apply lc_abs.
    apply IHt with (k := S k); [assumption | apply lc_at_S; exact Hu].
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma lc_open_rec_inv : forall t, forall k u, lc_at k u -> lc_at k (open_rec k u t) -> lc_at (S k) t.
Proof.
  induction t; intros k u Hu Hop; simpl in Hop.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. apply lc_bvar. lia.
    + apply Nat.eqb_neq in E. apply lc_bvar.
      assert (Hlt : n < k) by (inversion Hop; assumption). lia.
  - apply lc_fvar.
  - inversion Hop; subst. apply lc_app.
    + apply (IHt1 k u); [exact Hu | assumption].
    + apply (IHt2 k u); [exact Hu | assumption].
  - inversion Hop; subst. apply lc_abs.
    apply (IHt (S k) u); [apply lc_at_S; exact Hu | assumption].
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma lc_app_inv : forall k t1 t2, lc_at k (tm_app t1 t2) -> lc_at k t1 /\ lc_at k t2.
Proof. intros k t1 t2 H. inversion H. split; assumption. Qed.

Lemma lc_abs_inv : forall k T t, lc_at k (tm_abs T t) -> lc_at (S k) t.
Proof. intros k T t H. inversion H. assumption. Qed.

(** ** Interaction of substitution with opening. *)

Lemma subst_ext : forall (sigma sigma' : atom -> tm) t,
  (forall x, occurs_free x t -> sigma x = sigma' x) ->
  subst sigma t = subst sigma' t.
Proof.
  intros sigma sigma' t H. induction t; simpl.
  - reflexivity.
  - apply H. simpl. left. reflexivity.
  - f_equal.
    + apply IHt1. intros x Hx. apply H. simpl. apply in_or_app. left. exact Hx.
    + apply IHt2. intros x Hx. apply H. simpl. apply in_or_app. right. exact Hx.
  - f_equal. apply IHt. intros x Hx. apply H. simpl. exact Hx.
  - reflexivity.
  - reflexivity.
Qed.

Lemma subst_open_rec : forall (sigma : atom -> tm),
  (forall x, locally_closed (sigma x)) ->
  forall k u t,
    subst sigma (open_rec k u t) = open_rec k (subst sigma u) (subst sigma t).
Proof.
  intros sigma Hlc k u t. revert k u. induction t; intros k u; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. apply open_rec_lc. apply Hlc.
  - f_equal. apply IHt1. apply IHt2.
  - f_equal. apply IHt.
  - reflexivity.
  - reflexivity.
Qed.

Lemma subst_open : forall (sigma : atom -> tm),
  (forall x, locally_closed (sigma x)) ->
  forall t u, subst sigma (open t u) = open (subst sigma t) (subst sigma u).
Proof. intros sigma Hlc t u. unfold open. apply subst_open_rec. exact Hlc. Qed.

Lemma subst_open_fvar : forall (sigma sigma' : atom -> tm) t x,
  (forall y, locally_closed (sigma' y)) ->
  (forall y, y <> x -> sigma' y = sigma y) ->
  ~ occurs_free x t ->
  subst sigma' (open t (tm_fvar x)) = open (subst sigma t) (sigma' x).
Proof.
  intros sigma sigma' t x Hlc Hagree Hfresh.
  unfold open. rewrite subst_open_rec with (sigma := sigma') by exact Hlc.
  simpl.
  replace (subst sigma' t) with (subst sigma t).
  - reflexivity.
  - apply subst_ext. intros y Hy.
    symmetry. apply Hagree. intro Heq. subst y. apply Hfresh. exact Hy.
Qed.

(** ** Context update. *)

Lemma update_eq : forall Gamma x T, update Gamma x T x = Some T.
Proof. intros. unfold update. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma update_neq : forall Gamma x y T, x <> y -> update Gamma x T y = Gamma y.
Proof. intros. unfold update. apply Nat.eqb_neq in H. rewrite H. reflexivity. Qed.

(** ** Value and step facts. *)

Lemma value_app_inv : forall t1 t2, value (tm_app t1 t2) -> False.
Proof. intros t1 t2 H. inversion H. Qed.

Lemma value_no_step : forall t, value t -> forall t', step t t' -> False.
Proof.
  intros t Hv. induction Hv as [T t0 Hlc | |]; intros t' Hst; inversion Hst.
Qed.

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v H. destruct H as [T t Hlc | |].
  - exact Hlc.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma value_SN : forall t, value t -> strongly_normalizing t.
Proof.
  intros t Hv. apply SN_intro. intros t' Hst.
  exfalso. eapply value_no_step; eauto.
Qed.

Lemma abs_no_step : forall T t t', step (tm_abs T t) t' -> False.
Proof. intros T t t' H. inversion H. Qed.

Lemma fvar_no_step : forall x t', step (tm_fvar x) t' -> False.
Proof. intros x t' H. inversion H. Qed.

(** ** Strong normalization is preserved by reduction. *)

Lemma SN_step : forall t t', strongly_normalizing t -> step t t' -> strongly_normalizing t'.
Proof.
  intros t t' Hsn. revert t'. induction Hsn as [t0 Hred IH].
  intros t' Hst. apply Hred. exact Hst.
Qed.

(** ** Step preserves local closure. *)

Lemma step_lc : forall t t', step t t' -> locally_closed t -> locally_closed t'.
Proof.
  intros t t' H. induction H as [T t0 v Hlcabs Hval | t1 t1' t2 Hstep IH Hlct2 | v1 t2 t2' Hval Hstep IH];
    intros Hlc.
  - apply lc_app_inv in Hlc. destruct Hlc as [Habs Hv].
    apply lc_open_rec with (k := 0).
    + apply lc_abs_inv in Habs. exact Habs.
    + apply value_lc. exact Hval.
  - apply lc_app_inv in Hlc. destruct Hlc as [H1 H2].
    apply lc_app. apply IH. exact H1. exact H2.
  - apply lc_app_inv in Hlc. destruct Hlc as [H1 H2].
    apply lc_app. exact H1. apply IH. exact H2.
Qed.

(** * The logical relation.

    [LR T t] is a unary, type-indexed relation.  At base type it is strong
    normalization (plus local closure); at function type it additionally
    requires that the term be strongly normalizing and map related arguments
    to related results.  Local closure is carried along so that arguments of
    applications may be used as the side condition of [ST_App1]. *)

Fixpoint LR (T : ty) (t : tm) {struct T} : Prop :=
  match T with
  | Ty_Bool => locally_closed t /\ strongly_normalizing t
  | Ty_Arrow T1 T2 =>
      locally_closed t /\ strongly_normalizing t /\
      (forall u, LR T1 u -> LR T2 (tm_app t u))
  end.

Lemma LR_lc : forall T t, LR T t -> locally_closed t.
Proof.
  intros T. induction T as [| T1 IH1 T2 IH2]; intros t H; simpl in H.
  - destruct H as [H1 H2]. exact H1.
  - destruct H as [H1 [H2 H3]]. exact H1.
Qed.

Lemma LR_sn : forall T t, LR T t -> strongly_normalizing t.
Proof.
  intros T. induction T as [| T1 IH1 T2 IH2]; intros t H; simpl in H.
  - destruct H as [H1 H2]. exact H2.
  - destruct H as [H1 [H2 H3]]. exact H2.
Qed.

Lemma LR_arrow_app : forall T1 T2 t u,
  LR (Ty_Arrow T1 T2) t -> LR T1 u -> LR T2 (tm_app t u).
Proof.
  intros T1 T2 t u H Hu. simpl in H. destruct H as [H1 [H2 H3]]. apply H3. exact Hu.
Qed.

(** Any locally closed, non-value, stuck term is related at every type. *)

Lemma LR_stuck : forall T t,
  locally_closed t -> ~ value t -> (forall t', step t t' -> False) -> LR T t.
Proof.
  intros T. induction T as [| T1 IH1 T2 IH2]; intros t Hlc Hnv Hns; simpl.
  - split.
    + exact Hlc.
    + apply SN_intro. intros t' Hst. exfalso. exact (Hns t' Hst).
  - split.
    + exact Hlc.
    + split.
      * apply SN_intro. intros t' Hst. exfalso. exact (Hns t' Hst).
      * intros u Hu. apply IH2 with (t := tm_app t u).
        -- apply lc_app. exact Hlc. apply LR_lc with (T := T1). exact Hu.
        -- intro Hv. exact (value_app_inv _ _ Hv).
        -- intros t' Hst.
           inversion Hst as [TA ta v HlcA HvA | x1 x1' x2 Hstep1 Hlc2 | v1 x2 x2' Hv1 Hstep2];
             subst.
           ++ exfalso. apply Hnv. apply v_abs. exact HlcA.
           ++ exfalso. apply Hns with (t' := x1'). exact Hstep1.
           ++ exfalso. apply Hnv. exact Hv1.
Qed.

Lemma LR_fvar : forall T x, LR T (tm_fvar x).
Proof.
  intros T x. apply LR_stuck with (t := tm_fvar x).
  - apply lc_fvar.
  - intro Hv. inversion Hv.
  - intros t' Hst. inversion Hst.
Qed.

(** The relation is closed under one-step reduction. *)

Lemma LR_step : forall T t t', LR T t -> step t t' -> LR T t'.
Proof.
  intros T. induction T as [| T1 IH1 T2 IH2]; intros t t' HLR Hst; simpl in *.
  - destruct HLR as [Hlc Hsn]. split.
    + apply step_lc with (t := t); assumption.
    + apply SN_step with (t := t); assumption.
  - destruct HLR as [Hlc [Hsn Happ]]. split.
    + apply step_lc with (t := t); assumption.
    + split.
      * apply SN_step with (t := t); assumption.
      * intros u Hu. apply IH2 with (t := tm_app t u).
        -- apply Happ. exact Hu.
        -- apply ST_App1. exact Hst. apply LR_lc with (T := T1). exact Hu.
Qed.

(** A non-value whose one-step reducts are all related is itself related.
    (Applications only reduce through their function part when the function
    part is not a value.) *)

Lemma LR_neutral_expand : forall T t,
  locally_closed t -> strongly_normalizing t -> ~ value t ->
  (forall t', step t t' -> LR T t') -> LR T t.
Proof.
  intros T. induction T as [| T1 IH1 T2 IH2]; intros t Hlc Hsn Hnv Hred; simpl.
  - split; assumption.
  - split.
    + exact Hlc.
    + split.
      * exact Hsn.
      * intros u Hu.
        assert (Hred_app : forall t', step (tm_app t u) t' -> LR T2 t').
        { intros t' Hst.
          inversion Hst as [TA ta v HlcA HvA | x1 x1' x2 Hstep1 Hlc2 | v1 x2 x2' Hv1 Hstep2];
            subst.
          - exfalso. apply Hnv. apply v_abs. exact HlcA.
          - apply LR_arrow_app with (T1 := T1) (t := x1') (u := u).
            + apply Hred. exact Hstep1.
            + exact Hu.
          - exfalso. apply Hnv. exact Hv1. }
        apply IH2 with (t := tm_app t u).
        -- apply lc_app. exact Hlc. apply LR_lc with (T := T1). exact Hu.
        -- apply SN_intro. intros t' Hst. apply LR_sn with (T := T2). apply Hred_app. exact Hst.
        -- intro Hv. exact (value_app_inv _ _ Hv).
        -- exact Hred_app.
Qed.

(** Application of an abstraction whose beta-reducts are related. *)

Lemma LR_abs_app : forall A B (t1 : tm),
  lc_at 1 t1 ->
  (forall u, LR A u -> LR B (open t1 u)) ->
  forall u, LR A u -> LR B (tm_app (tm_abs A t1) u).
Proof.
  intros A B t1 Hlc1 Hbeta.
  assert (Hgen : forall u, strongly_normalizing u ->
      forall (A : ty) (B : ty) (t1 : tm), lc_at 1 t1 ->
      (forall w, LR A w -> LR B (open t1 w)) ->
      LR A u -> LR B (tm_app (tm_abs A t1) u)).
  { intros u0 Hsn. induction Hsn as [u1 Hred IH].
    intros A0 B0 t2 Hlc2 Hbeta2 Hu2.
    assert (Hred_app : forall t', step (tm_app (tm_abs A0 t2) u1) t' -> LR B0 t').
    { intros t' Hst.
      inversion Hst as [TA ta v HlcA HvA | x1 x1' x2 Hstep1 Hlc2' | v1 x2 x2' Hv1 Hstep2];
        subst.
      - apply Hbeta2. exact Hu2.
      - exfalso. eapply abs_no_step. exact Hstep1.
      - apply (IH x2' Hstep2 A0 B0 t2 Hlc2 Hbeta2).
        apply LR_step with (t := u1); assumption. }
    apply LR_neutral_expand with (T := B0) (t := tm_app (tm_abs A0 t2) u1).
    - apply lc_app. apply lc_abs. exact Hlc2.
      apply LR_lc with (T := A0). exact Hu2.
    - apply SN_intro. intros t' Hst. apply LR_sn with (T := B0). apply Hred_app. exact Hst.
    - intro Hv. exact (value_app_inv _ _ Hv).
    - exact Hred_app. }
  intros u Hu.
  apply Hgen with (A := A) (B := B) (t1 := t1).
  - apply LR_sn with (T := A). exact Hu.
  - exact Hlc1.
  - exact Hbeta.
  - exact Hu.
Qed.

(** * The semantic interpretation of typing contexts. *)

Definition env_ok (Gamma : context) (sigma : atom -> tm) : Prop :=
  (forall x, locally_closed (sigma x)) /\
  (forall x T, Gamma x = Some T -> LR T (sigma x)).

Lemma env_ok_update : forall Gamma x T1 (sigma sigma' : atom -> tm),
  env_ok Gamma sigma ->
  locally_closed (sigma' x) ->
  LR T1 (sigma' x) ->
  (forall y, y <> x -> sigma' y = sigma y) ->
  env_ok (update Gamma x T1) sigma'.
Proof.
  intros Gamma x T1 sigma sigma' Henv Hlcx HLRx Hagree.
  destruct Henv as [Hslc Hsmap]. split.
  - intros y. destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst y. exact Hlcx.
    + apply Nat.eqb_neq in E. rewrite Hagree.
      * apply Hslc.
      * intro H; apply E. symmetry. exact H.
  - intros y T Hy. unfold update in Hy. destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst y. simpl in Hy.
      inversion Hy. subst. exact HLRx.
    + assert (Hne : y <> x).
      { intro H. apply Nat.eqb_neq in E. apply E. symmetry. exact H. }
      rewrite (Hagree y Hne). apply Hsmap. exact Hy.
Qed.

(** * Fundamental theorem of logical relations. *)

Theorem fundamental : forall Gamma t T,
  has_type Gamma t T ->
  forall sigma, env_ok Gamma sigma -> LR T (subst sigma t).
Proof.
  intros Gamma t T H.
  induction H as [Gamma x T Hx
                 | L Gamma T1 T2 t1 Hbody IHbody
                 | Gamma t1 t2 T1 T2 Hty1 IH1 Hty2 IH2
                 | Gamma
                 | Gamma].
  - (* T_Var *)
    intros sigma Henv. simpl. destruct Henv as [Hslc Hsmap]. apply Hsmap. exact Hx.
  - (* T_Abs *)
    intros sigma Henv. simpl.
    set (x := fresh_atom (L ++ fvars t1)).
    assert (HxL : ~ In x L).
    { intro Hin. apply (fresh_atom_spec (L ++ fvars t1)). apply in_or_app. left. exact Hin. }
    assert (Hxfv : ~ occurs_free x t1).
    { intro Hin. apply (fresh_atom_spec (L ++ fvars t1)). apply in_or_app. right. exact Hin. }
    set (sigma_x := fun y => if Nat.eqb x y then tm_fvar x else sigma y).
    assert (Hsx_self : sigma_x x = tm_fvar x).
    { unfold sigma_x. rewrite Nat.eqb_refl. reflexivity. }
    assert (Hsx_lc : forall y, locally_closed (sigma_x y)).
    { intros y. unfold sigma_x. destruct (Nat.eqb x y) eqn:E.
      - apply lc_fvar.
      - apply (proj1 Henv). }
    assert (Hsx_agree : forall y, y <> x -> sigma_x y = sigma y).
    { intros y Hy. unfold sigma_x. destruct (Nat.eqb x y) eqn:E.
      - apply Nat.eqb_eq in E. exfalso. apply Hy. symmetry. exact E.
      - reflexivity. }
    assert (Henvx : env_ok (update Gamma x T1) sigma_x).
    { apply (env_ok_update Gamma x T1 sigma sigma_x).
      - exact Henv.
      - rewrite Hsx_self. apply lc_fvar.
      - rewrite Hsx_self. apply LR_fvar.
      - exact Hsx_agree. }
    assert (Heqx : subst sigma_x (open t1 (tm_fvar x)) = open (subst sigma t1) (tm_fvar x)).
    { rewrite (subst_open_fvar sigma sigma_x t1 x Hsx_lc Hsx_agree Hxfv).
      rewrite Hsx_self. reflexivity. }
    assert (Hbody_lr : LR T2 (open (subst sigma t1) (tm_fvar x))).
    { rewrite <- Heqx. apply (IHbody x HxL sigma_x Henvx). }
    assert (Hlc1 : lc_at 1 (subst sigma t1)).
    { apply lc_open_rec_inv with (u := tm_fvar x).
      - apply lc_fvar.
      - apply LR_lc with (T := T2). exact Hbody_lr. }
    split.
    + apply lc_abs. exact Hlc1.
    + split.
      * apply value_SN. apply v_abs. apply lc_abs. exact Hlc1.
      * intros u Hu.
        assert (Hbeta : forall u0, LR T1 u0 -> LR T2 (open (subst sigma t1) u0)).
        { intros u0 Hu0.
          set (sigma_u := fun y => if Nat.eqb x y then u0 else sigma y).
          assert (Hsu_self : sigma_u x = u0).
          { unfold sigma_u. rewrite Nat.eqb_refl. reflexivity. }
          assert (Hsu_lc : forall y, locally_closed (sigma_u y)).
          { intros y. unfold sigma_u. destruct (Nat.eqb x y) eqn:E.
            - apply LR_lc with (T := T1). exact Hu0.
            - apply (proj1 Henv). }
          assert (Hsu_agree : forall y, y <> x -> sigma_u y = sigma y).
          { intros y Hy. unfold sigma_u. destruct (Nat.eqb x y) eqn:E.
            - apply Nat.eqb_eq in E. exfalso. apply Hy. symmetry. exact E.
            - reflexivity. }
          assert (Henvu : env_ok (update Gamma x T1) sigma_u).
          { apply (env_ok_update Gamma x T1 sigma sigma_u).
            - exact Henv.
            - rewrite Hsu_self. apply LR_lc with (T := T1). exact Hu0.
            - rewrite Hsu_self. exact Hu0.
            - exact Hsu_agree. }
          assert (Hequ : subst sigma_u (open t1 (tm_fvar x)) = open (subst sigma t1) u0).
          { rewrite (subst_open_fvar sigma sigma_u t1 x Hsu_lc Hsu_agree Hxfv).
            rewrite Hsu_self. reflexivity. }
          rewrite <- Hequ. apply (IHbody x HxL sigma_u Henvu). }
        apply LR_abs_app with (A := T1) (B := T2) (t1 := subst sigma t1).
        -- exact Hlc1.
        -- exact Hbeta.
        -- exact Hu.
  - (* T_App *)
    intros sigma Henv. simpl.
    pose proof (IH1 sigma Henv) as Hh. simpl in Hh.
    destruct Hh as [Hlc [Hsn Happ]]. apply Happ. apply IH2. exact Henv.
  - (* T_True *)
    intros sigma Henv. simpl. split.
    + apply lc_true.
    + apply value_SN. apply v_true.
  - (* T_False *)
    intros sigma Henv. simpl. split.
    + apply lc_false.
    + apply value_SN. apply v_false.
Qed.

(** * The target theorem. *)

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  apply LR_sn with (T := T).
  pose proof (fundamental empty t T Hty ids) as H.
  assert (Henv : env_ok empty ids).
  { split.
    - intros x. apply lc_fvar.
    - intros x T0 Hx. unfold empty in Hx. discriminate. }
  specialize (H Henv).
  rewrite subst_ids in H.
  exact H.
Qed.

End STLCNormalizationNoneHardTask.
