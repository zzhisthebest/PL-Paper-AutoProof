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

(** ** Auxiliary definitions and lemmas for the normalization proof. *)

(** Free variables of a term, plus a fresh-atom generator. *)

Fixpoint fvars (t : tm) : list atom :=
  match t with
  | tm_bvar _ => nil
  | tm_fvar x => x :: nil
  | tm_app t1 t2 => fvars t1 ++ fvars t2
  | tm_abs _ t1 => fvars t1
  | tm_true => nil
  | tm_false => nil
  end.

Fixpoint max_atom (l : list atom) : atom :=
  match l with
  | nil => 0
  | a :: l' => Nat.max a (max_atom l')
  end.

Lemma max_atom_spec : forall l a, In a l -> a <= max_atom l.
Proof.
  induction l as [| b l IH]; intros a Ha.
  - destruct Ha.
  - simpl in Ha. simpl. destruct Ha as [Hba | Ha].
    + subst a. apply Nat.le_max_l.
    + apply Nat.le_trans with (max_atom l).
      * apply IH; exact Ha.
      * apply Nat.le_max_r.
Qed.

Definition fresh (l : list atom) : atom := S (max_atom l).

Lemma fresh_notin : forall l, ~ In (fresh l) l.
Proof.
  intros l Hin. unfold fresh in Hin.
  pose proof (max_atom_spec l (S (max_atom l)) Hin). lia.
Qed.

Lemma fresh_notin_app_l : forall l1 l2, ~ In (fresh (l1 ++ l2)) l1.
Proof.
  intros l1 l2 Hin.
  assert (Hin' : In (fresh (l1 ++ l2)) (l1 ++ l2)).
  { apply in_or_app. left. exact Hin. }
  exact (fresh_notin (l1 ++ l2) Hin').
Qed.

Lemma fresh_notin_app_r : forall l1 l2, ~ In (fresh (l1 ++ l2)) l2.
Proof.
  intros l1 l2 Hin.
  assert (Hin' : In (fresh (l1 ++ l2)) (l1 ++ l2)).
  { apply in_or_app. right. exact Hin. }
  exact (fresh_notin (l1 ++ l2) Hin').
Qed.

(** Substitution of free variables. *)

Definition subst_id : atom -> tm := fun x => tm_fvar x.

Definition subst_update (sigma : atom -> tm) (x : atom) (w : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then w else sigma y.

Fixpoint substf (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_app t1 t2 => tm_app (substf sigma t1) (substf sigma t2)
  | tm_abs T t1 => tm_abs T (substf sigma t1)
  | tm_true => tm_true
  | tm_false => tm_false
  end.

Lemma substf_id : forall t, substf subst_id t = t.
Proof.
  induction t as [i|x|t1 IH1 t2 IH2|T t1 IH| |]; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** Local-closure lemmas. *)

Lemma lc_at_mono : forall t k k', k <= k' -> lc_at k t -> lc_at k' t.
Proof.
  intros t k k' Hle Hlc. revert k' Hle.
  induction Hlc; intros k' Hle.
  - apply lc_bvar. lia.
  - apply lc_fvar.
  - apply lc_app; [apply IHHlc1 | apply IHHlc2]; exact Hle.
  - apply lc_abs. apply IHHlc. lia.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma open_rec_lc : forall t k u, lc_at k t -> open_rec k u t = t.
Proof.
  induction t as [i|x|t1 IH1 t2 IH2|T t1 IH| |]; intros k u Hlc; simpl.
  - assert (Hneq : (k =? i) = false).
    { apply Nat.eqb_neq. inversion Hlc. lia. }
    rewrite Hneq. reflexivity.
  - reflexivity.
  - assert (E1 : open_rec k u t1 = t1).
    { apply IH1. inversion Hlc; assumption. }
    assert (E2 : open_rec k u t2 = t2).
    { apply IH2. inversion Hlc; assumption. }
    rewrite E1, E2. reflexivity.
  - assert (E1 : open_rec (S k) u t1 = t1).
    { apply IH. inversion Hlc; assumption. }
    rewrite E1. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma lc_open_rec : forall t k v, lc_at (S k) t -> lc_at k v -> lc_at k (open_rec k v t).
Proof.
  induction t as [i|x|t1 IH1 t2 IH2|T t1 IH| |]; intros k v Ht Hv; simpl.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst i. exact Hv.
    + apply lc_bvar. apply Nat.eqb_neq in E. inversion Ht. lia.
  - apply lc_fvar.
  - apply lc_app.
    + apply IH1; [inversion Ht; assumption | exact Hv].
    + apply IH2; [inversion Ht; assumption | exact Hv].
  - apply lc_abs. apply IH.
    + inversion Ht; assumption.
    + apply lc_at_mono with (k := k); [lia | exact Hv].
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma lc_open_fvar_inv : forall t k x, lc_at k (open_rec k (tm_fvar x) t) -> lc_at (S k) t.
Proof.
  induction t as [i|x|t1 IH1 t2 IH2|T t1 IH| |]; intros k y H; simpl in H.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst i. apply lc_bvar. lia.
    + apply lc_bvar. apply Nat.eqb_neq in E. inversion H. lia.
  - apply lc_fvar.
  - inversion H as [k0 i Hlt | k0 z | k0 a b Ha Hb | k0 T0 body Hb | k0 | k0].
    apply lc_app.
    + apply (IH1 k y). exact Ha.
    + apply (IH2 k y). exact Hb.
  - inversion H as [k0 i Hlt | k0 z | k0 a b Ha Hb | k0 T0 body Hb | k0 | k0].
    apply lc_abs. apply (IH (S k) y). exact Hb.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma lc_subst : forall t k (sigma : atom -> tm),
  lc_at k t -> (forall x, lc_at k (sigma x)) -> lc_at k (substf sigma t).
Proof.
  induction t as [i|x|t1 IH1 t2 IH2|T t1 IH| |]; intros k sigma Hlc Hsig; simpl.
  - exact Hlc.
  - apply Hsig.
  - inversion Hlc as [k0 i Hlt | k0 z | k0 a b Ha Hb | k0 T0 body Hb | k0 | k0].
    apply lc_app.
    + apply IH1; [exact Ha | exact Hsig].
    + apply IH2; [exact Hb | exact Hsig].
  - inversion Hlc as [k0 i Hlt | k0 z | k0 a b Ha Hb | k0 T0 body Hb | k0 | k0].
    apply lc_abs. apply IH.
    + exact Hb.
    + intros y. apply lc_at_mono with (k := k); [lia | apply Hsig].
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma typing_lc : forall Gamma t T, has_type Gamma t T -> lc_at 0 t.
Proof.
  intros Gamma t T H. induction H as
    [Gamma x T Hx | L Gamma T1 T2 t1 Hprem IH | Gamma t1 t2 T1 T2 H1 IH1 H2 IH2 | Gamma | Gamma].
  - apply lc_fvar.
  - apply lc_abs.
    pose proof (IH (fresh L) (fresh_notin L)) as Hx.
    exact (lc_open_fvar_inv t1 0 (fresh L) Hx).
  - apply lc_app; assumption.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma step_lc : forall t t', step t t' -> lc_at 0 t -> lc_at 0 t'.
Proof.
  intros t t' Hst. induction Hst; intros Hlc.
  - simpl in Hlc. inversion Hlc as [k i Hlt | k z | k a b Ha Hb | k T0 body Hbody | k | k].
    subst.
    apply lc_open_rec with (k := 0).
    + inversion Ha as [k' i' Hlt' | k' z' | k' a' b' Ha' Hb' | k' T0' body' Hbody' | k' | k'].
      subst. exact Hbody'.
    + exact Hb.
  - simpl in Hlc. inversion Hlc as [k i Hlt | k z | k a b Ha Hb | k T0 body Hbody | k | k].
    subst.
    apply lc_app.
    + apply IHHst. exact Ha.
    + exact Hb.
  - simpl in Hlc. inversion Hlc as [k i Hlt | k z | k a b Ha Hb | k T0 body Hbody | k | k].
    subst.
    apply lc_app.
    + exact Ha.
    + apply IHHst. exact Hb.
Qed.

Lemma abs_no_step : forall T body t', ~ step (tm_abs T body) t'.
Proof. intros T body t' H. inversion H. Qed.

Lemma true_no_step : forall t', ~ step tm_true t'.
Proof. intros t' H. inversion H. Qed.

Lemma false_no_step : forall t', ~ step tm_false t'.
Proof. intros t' H. inversion H. Qed.

Lemma subst_open_rec_fvar : forall (sigma : atom -> tm) x w t k,
  (forall y, lc_at 0 (sigma y)) ->
  lc_at 0 w ->
  ~ In x (fvars t) ->
  substf (subst_update sigma x w) (open_rec k (tm_fvar x) t) =
    open_rec k w (substf sigma t).
Proof.
  intros sigma x w t. induction t as [i|y|t1 IH1 t2 IH2|T t1 IH| |]; intros k Hsig Hw Hfresh; simpl.
  - destruct (Nat.eqb k i) eqn:E.
    + unfold subst_update. simpl. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - assert (Hxy : x <> y).
    { intro Heq. apply Hfresh. subst y. simpl. left. reflexivity. }
    assert (Exy : (x =? y) = false) by (apply Nat.eqb_neq; exact Hxy).
    unfold subst_update. simpl. rewrite Exy.
    assert (Hlc : lc_at k (sigma y)).
    { apply lc_at_mono with (k := 0); [lia | apply Hsig]. }
    rewrite (open_rec_lc (sigma y) k w Hlc). reflexivity.
  - assert (Hf1 : ~ In x (fvars t1)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. left. exact Hin. }
    assert (Hf2 : ~ In x (fvars t2)).
    { intro Hin. apply Hfresh. simpl. apply in_or_app. right. exact Hin. }
    assert (E1 : substf (subst_update sigma x w) (open_rec k (tm_fvar x) t1) =
                 open_rec k w (substf sigma t1)).
    { apply IH1; assumption. }
    assert (E2 : substf (subst_update sigma x w) (open_rec k (tm_fvar x) t2) =
                 open_rec k w (substf sigma t2)).
    { apply IH2; assumption. }
    rewrite E1, E2. reflexivity.
  - assert (E1 : substf (subst_update sigma x w) (open_rec (S k) (tm_fvar x) t1) =
                 open_rec (S k) w (substf sigma t1)).
    { apply IH; assumption. }
    rewrite E1. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** ** The type-indexed logical relation. *)

Fixpoint Red (T : ty) (t : tm) : Prop :=
  match T with
  | Ty_Bool => lc_at 0 t /\ strongly_normalizing t
  | Ty_Arrow T1 T2 =>
      lc_at 0 t /\ strongly_normalizing t /\
      (forall u, Red T1 u -> Red T2 (tm_app t u))
  end.

Lemma Red_lc : forall T t, Red T t -> lc_at 0 t.
Proof.
  intros T t HR. destruct T as [| T1 T2]; simpl in HR.
  - exact (proj1 HR).
  - exact (proj1 HR).
Qed.

Lemma Red_sn : forall T t, Red T t -> strongly_normalizing t.
Proof.
  intros T t HR. destruct T as [| T1 T2]; simpl in HR.
  - exact (proj2 HR).
  - exact (proj1 (proj2 HR)).
Qed.

Lemma Red_step : forall T t t', Red T t -> step t t' -> Red T t'.
Proof.
  induction T as [| T1 IH1 T2 IH2]; intros t t' HR Hst; simpl in *.
  - destruct HR as [Hlc Hsn]. split.
    + apply step_lc with (t := t); assumption.
    + inversion Hsn as [t0 Hsucc]. apply Hsucc. exact Hst.
  - destruct HR as [Hlc [Hsn Hcl]]. split.
    + apply step_lc with (t := t); assumption.
    + split.
      * inversion Hsn as [t0 Hsucc]. apply Hsucc. exact Hst.
      * intros u HRu.
        assert (Hstep' : step (tm_app t u) (tm_app t' u)).
        { apply ST_App1.
          - exact Hst.
          - apply Red_lc with (T := T1). exact HRu. }
        specialize (IH2 (tm_app t u) (tm_app t' u)).
        apply IH2; [apply Hcl; exact HRu | exact Hstep'].
Qed.

(** Backwards closure for terms that are not abstractions. *)
Lemma Red_backward : forall T t,
  lc_at 0 t ->
  strongly_normalizing t ->
  (forall t', step t t' -> Red T t') ->
  (forall T0 body, t <> tm_abs T0 body) ->
  Red T t.
Proof.
  induction T as [| T1 IH1 T2 IH2]; intros t Hlc Hsn Hred Hnotabs.
  - simpl. split; assumption.
  - simpl. split; [assumption | split; [assumption |]].
    intros u HRu.
    assert (Hmain : forall v, strongly_normalizing v -> Red T1 v -> Red T2 (tm_app t v)).
    { intros v HSN. induction HSN as [v0 Hstep IH].
      intros HRv.
      assert (Happs : forall s, step (tm_app t v0) s -> Red T2 s).
      { intros s Hs.
        inversion Hs as [T0 body0 v1 Hlc0 Hval | t1 t1' t2 Hst Hlct2 | w1 t2 t2' Hval Hst].
        - subst. exfalso. apply (Hnotabs T0 body0). reflexivity.
        - subst.
          assert (HRt' : Red (Ty_Arrow T1 T2) t1') by (apply Hred; exact Hst).
          simpl in HRt'. apply (proj2 (proj2 HRt')). exact HRv.
        - subst.
          apply IH.
          + exact Hst.
          + apply Red_step with (t := v0); assumption.
      }
      apply IH2 with (t := tm_app t v0).
      + apply lc_app; [exact Hlc | apply Red_lc with (T := T1); exact HRv].
      + apply SN_intro. intros s Hs. apply Red_sn with (T := T2). apply Happs. exact Hs.
      + exact Happs.
      + intros T0 body0 Heq. discriminate Heq.
    }
    apply Hmain.
    + apply Red_sn with (T := T1); exact HRu.
    + exact HRu.
Qed.

(** Applications of an abstraction to any reducible argument. *)
Lemma abs_app_red : forall u, strongly_normalizing u ->
  forall T1 T2 body,
    lc_at 0 (tm_abs T1 body) ->
    (forall w, Red T1 w -> Red T2 (open body w)) ->
    Red T1 u ->
    Red T2 (tm_app (tm_abs T1 body) u).
Proof.
  intros u HSN. induction HSN as [u Hstep IH].
  intros T1 T2 body Hlc Hbody HRu.
  apply Red_backward with (T := T2).
  - apply lc_app; [exact Hlc | apply Red_lc with (T := T1); exact HRu].
  - apply SN_intro. intros s Hs.
    inversion Hs as [T0 body0 v Hlc0 Hval | t1 t1' t2 Hst Hlct2 | v1 t2 t2' Hval Hst].
    + subst. apply Red_sn with (T := T2). apply Hbody. exact HRu.
    + subst. exfalso. apply (abs_no_step T1 body t1'). exact Hst.
    + subst. apply Red_sn with (T := T2). apply IH.
      * exact Hst.
      * exact Hlc.
      * exact Hbody.
      * apply Red_step with (t := u); assumption.
  - intros s Hs.
    inversion Hs as [T0 body0 v Hlc0 Hval | t1 t1' t2 Hst Hlct2 | v1 t2 t2' Hval Hst].
    + subst. apply Hbody. exact HRu.
    + subst. exfalso. apply (abs_no_step T1 body t1'). exact Hst.
    + subst. apply IH.
      * exact Hst.
      * exact Hlc.
      * exact Hbody.
      * apply Red_step with (t := u); assumption.
  - intros T0 body0 Heq. discriminate Heq.
Qed.

(** Fundamental theorem: every well-typed term is in the logical relation
    under any well-formed context interpretation. *)
Theorem fundamental : forall Gamma t T,
  <{ Gamma |-- t \in T }> ->
  forall sigma,
    (forall y, lc_at 0 (sigma y)) ->
    (forall x S, Gamma x = Some S -> Red S (sigma x)) ->
    Red T (substf sigma t).
Proof.
  intros Gamma t T H. induction H as
    [Gamma x T Hx | L Gamma T1 T2 t1 Hprem IH | Gamma t1 t2 T1 T2 H1 IH1 H2 IH2 | Gamma | Gamma];
    intros sigma HsigLc Hsig.
  - simpl. apply Hsig. exact Hx.
  - simpl.
    assert (Hlcabs : lc_at 0 (tm_abs T1 t1)).
    { eapply typing_lc. eapply T_Abs. eassumption. }
    assert (Hlcbody : lc_at 1 (substf sigma t1)).
    { apply (lc_subst t1 1 sigma).
      - inversion Hlcabs. assumption.
      - intros y. apply lc_at_mono with (k := 0); [lia | apply HsigLc]. }
    split.
    + apply lc_abs. exact Hlcbody.
    + split.
      * apply SN_intro. intros t' Hst. exfalso. exact (abs_no_step T1 (substf sigma t1) t' Hst).
      * intros u HRu.
        apply (abs_app_red u).
        -- apply Red_sn with (T := T1). exact HRu.
        -- apply lc_abs. exact Hlcbody.
        -- intros w HRw.
           assert (Hlcw : lc_at 0 w) by (apply Red_lc with (T := T1); exact HRw).
           assert (HsigLc' : forall y, lc_at 0 (subst_update sigma (fresh (L ++ fvars t1)) w y)).
           { intros y. unfold subst_update.
             destruct (Nat.eqb (fresh (L ++ fvars t1)) y).
             - exact Hlcw.
             - apply HsigLc. }
           assert (Hctx' : forall y S,
             update Gamma (fresh (L ++ fvars t1)) T1 y = Some S ->
             Red S (subst_update sigma (fresh (L ++ fvars t1)) w y)).
           { intros y S Hy. unfold update in Hy.
             destruct (Nat.eqb (fresh (L ++ fvars t1)) y) eqn:E.
             - apply Nat.eqb_eq in E. subst y. inversion Hy. subst S.
               unfold subst_update. rewrite Nat.eqb_refl. exact HRw.
             - unfold subst_update. rewrite E.
               apply Hsig. exact Hy. }
           pose proof (IH (fresh (L ++ fvars t1)) (fresh_notin_app_l L (fvars t1))
                        (subst_update sigma (fresh (L ++ fvars t1)) w) HsigLc' Hctx') as Hsem.
           assert (Hcomm : substf (subst_update sigma (fresh (L ++ fvars t1)) w)
                             (open t1 (tm_fvar (fresh (L ++ fvars t1)))) =
                           open (substf sigma t1) w).
           { apply subst_open_rec_fvar; [exact HsigLc | exact Hlcw | exact (fresh_notin_app_r L (fvars t1))]. }
           rewrite Hcomm in Hsem. exact Hsem.
        -- exact HRu.
  - simpl. pose proof (IH1 sigma HsigLc Hsig) as Hf. simpl in Hf.
    destruct Hf as [Hlcf [Hsnf Hclf]].
    apply (Hclf (substf sigma t2)). apply IH2; assumption.
  - simpl. split.
    + apply lc_true.
    + apply SN_intro. intros t' Hst. exfalso. exact (true_no_step t' Hst).
  - simpl. split.
    + apply lc_false.
    + apply SN_intro. intros t' Hst. exfalso. exact (false_no_step t' Hst).
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T H.
  assert (HsigLc : forall y, lc_at 0 (subst_id y)).
  { intros y. apply lc_fvar. }
  assert (Hctx : forall x S, empty x = Some S -> Red S (subst_id x)).
  { intros x S Hx. unfold empty in Hx. discriminate Hx. }
  pose proof (fundamental empty t T H subst_id HsigLc Hctx) as HR.
  rewrite substf_id in HR.
  exact (Red_sn T t HR).
Qed.

End STLCNormalizationNoneHardTask.
