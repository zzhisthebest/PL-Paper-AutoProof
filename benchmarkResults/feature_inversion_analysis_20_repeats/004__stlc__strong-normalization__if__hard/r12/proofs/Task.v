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

(** * Auxiliary development: strong normalization via a logical relation *)

(** ** Free variables *)

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
  | x :: xs => Nat.max x (max_list xs)
  end.

Lemma in_max_list : forall l x, In x l -> x <= max_list l.
Proof.
  induction l as [| y ys IH]; intros x Hin; simpl in *.
  - inversion Hin.
  - destruct Hin as [-> | Hin].
    + apply Nat.le_max_l.
    + apply Nat.le_trans with (max_list ys);
        [apply IH; exact Hin | apply Nat.le_max_r].
Qed.

Lemma not_in_max_succ : forall l : list nat, ~ In (S (max_list l)) l.
Proof.
  intros l Hin. pose proof (in_max_list l (S (max_list l)) Hin). lia.
Qed.

Lemma fresh_atom : forall L : list atom, exists x, ~ In x L.
Proof. intros L. exists (S (max_list L)). apply not_in_max_succ. Qed.

Lemma fresh_atom_two : forall L1 L2 : list atom,
  exists x, ~ In x L1 /\ ~ In x L2.
Proof.
  intros L1 L2. exists (S (max_list (L1 ++ L2))). split; intro Hin;
    apply not_in_max_succ with (l := L1 ++ L2); rewrite in_app_iff;
    [left | right]; exact Hin.
Qed.

Lemma not_in_app_l : forall (x : atom) l1 l2, ~ In x (l1 ++ l2) -> ~ In x l1.
Proof. intros x l1 l2 H H1. apply H. rewrite in_app_iff. left. exact H1. Qed.

Lemma not_in_app_r : forall (x : atom) l1 l2, ~ In x (l1 ++ l2) -> ~ In x l2.
Proof. intros x l1 l2 H H1. apply H. rewrite in_app_iff. right. exact H1. Qed.

(** ** Substitution of free variables *)

Fixpoint subst_tm (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_app t1 t2 => tm_app (subst_tm sigma t1) (subst_tm sigma t2)
  | tm_abs T t1 => tm_abs T (subst_tm sigma t1)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 =>
      tm_if (subst_tm sigma t1) (subst_tm sigma t2) (subst_tm sigma t3)
  end.

Definition upd (sigma : atom -> tm) (x : atom) (v : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then v else sigma y.

Lemma subst_tm_open_rec : forall sigma k u t,
  (forall x j w, open_rec j w (sigma x) = sigma x) ->
  subst_tm sigma (open_rec k u t) =
  open_rec k (subst_tm sigma u) (subst_tm sigma t).
Proof.
  intros sigma k u t Himg. revert k u.
  induction t as [n | x | t1 IH1 t2 IH2 | T t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
    intros k u; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. apply Himg.
  - rewrite (IH1 k u), (IH2 k u). reflexivity.
  - rewrite (IH1 (S k) u). reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite (IH1 k u), (IH2 k u), (IH3 k u). reflexivity.
Qed.

Lemma subst_tm_fvar_id : forall t, subst_tm (fun x => tm_fvar x) t = t.
Proof.
  induction t as [n | x | t1 IH1 t2 IH2 | T t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
    simpl; try reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH1. reflexivity.
  - rewrite IH1, IH2, IH3. reflexivity.
Qed.

Lemma subst_tm_upd_agree : forall t x v sigma,
  ~ In x (fv t) -> subst_tm (upd sigma x v) t = subst_tm sigma t.
Proof.
  induction t as [n | y | t1 IH1 t2 IH2 | T t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
    intros x v sigma Hfresh; simpl in *.
  - reflexivity.
  - simpl in Hfresh. unfold upd. destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst y. exfalso. apply Hfresh.
      simpl. left. reflexivity.
    + reflexivity.
  - assert (H1 : ~ In x (fv t1))
      by (apply not_in_app_l with (l2 := fv t2); exact Hfresh).
    assert (H2 : ~ In x (fv t2))
      by (apply not_in_app_r with (l1 := fv t1); exact Hfresh).
    rewrite (IH1 x v sigma H1), (IH2 x v sigma H2). reflexivity.
  - rewrite (IH1 x v sigma Hfresh). reflexivity.
  - reflexivity.
  - reflexivity.
  - assert (H23 : ~ In x (fv t2 ++ fv t3))
      by (apply not_in_app_r with (l1 := fv t1); exact Hfresh).
    assert (H1 : ~ In x (fv t1))
      by (apply not_in_app_l with (l2 := fv t2 ++ fv t3); exact Hfresh).
    assert (H2 : ~ In x (fv t2))
      by (apply not_in_app_l with (l2 := fv t3); exact H23).
    assert (H3 : ~ In x (fv t3))
      by (apply not_in_app_r with (l1 := fv t2); exact H23).
    rewrite (IH1 x v sigma H1), (IH2 x v sigma H2), (IH3 x v sigma H3).
    reflexivity.
Qed.

(** ** Context update lemmas *)

Lemma update_same : forall Gamma x T, update Gamma x T x = Some T.
Proof.
  intros. unfold update. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma update_other : forall Gamma x y T,
  x <> y -> update Gamma x T y = Gamma y.
Proof.
  intros. unfold update. apply Nat.eqb_neq in H. rewrite H. reflexivity.
Qed.

(** ** Local closure lemmas *)

Lemma lc_bvar_inv : forall k i, lc_at k (tm_bvar i) -> i < k.
Proof. intros k i H. inversion H. assumption. Qed.

Lemma lc_app_inv : forall k t1 t2,
  lc_at k (tm_app t1 t2) -> lc_at k t1 /\ lc_at k t2.
Proof. intros k t1 t2 H. inversion H; subst; auto. Qed.

Lemma lc_abs_inv : forall k T t, lc_at k (tm_abs T t) -> lc_at (S k) t.
Proof. intros k T t H. inversion H; subst; auto. Qed.

Lemma lc_if_inv : forall k t1 t2 t3,
  lc_at k (tm_if t1 t2 t3) -> lc_at k t1 /\ lc_at k t2 /\ lc_at k t3.
Proof. intros k t1 t2 t3 H. inversion H; subst; auto. Qed.

Lemma lc_at_mono : forall t k k', k <= k' -> lc_at k t -> lc_at k' t.
Proof.
  intros t. induction t as
    [n | x | t1 IH1 t2 IH2 | T t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
    intros k k' Hle Hlc.
  - apply lc_bvar. pose proof (lc_bvar_inv _ _ Hlc). lia.
  - apply lc_fvar.
  - apply lc_app_inv in Hlc as [H1 H2].
    apply lc_app; [exact (IH1 k k' Hle H1) | exact (IH2 k k' Hle H2)].
  - apply lc_abs. apply lc_abs_inv in Hlc.
    exact (IH1 (S k) (S k') (le_n_S k k' Hle) Hlc).
  - apply lc_true.
  - apply lc_false.
  - apply lc_if_inv in Hlc as [H1 [H2 H3]].
    apply lc_if; [exact (IH1 k k' Hle H1) | exact (IH2 k k' Hle H2) |
                  exact (IH3 k k' Hle H3)].
Qed.

Lemma lc_at_open_rec : forall t k u,
  lc_at (S k) t -> lc_at k u -> lc_at k (open_rec k u t).
Proof.
  induction t as [n | x | t1 IH1 t2 IH2 | T t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
    intros k u Ht Hu; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. exact Hu.
    + apply lc_bvar. apply lc_bvar_inv in Ht. apply Nat.eqb_neq in E. lia.
  - apply lc_fvar.
  - apply lc_app_inv in Ht as [H1 H2].
    apply lc_app; [exact (IH1 k u H1 Hu) | exact (IH2 k u H2 Hu)].
  - apply lc_abs. apply lc_abs_inv in Ht.
    apply (IH1 (S k) u Ht).
    apply lc_at_mono with (k := k); [lia | exact Hu].
  - apply lc_true.
  - apply lc_false.
  - apply lc_if_inv in Ht as [H1 [H2 H3]].
    apply lc_if; [exact (IH1 k u H1 Hu) | exact (IH2 k u H2 Hu) |
                  exact (IH3 k u H3 Hu)].
Qed.

Lemma lc_at_open_down : forall t k u,
  lc_at k (open_rec k u t) -> lc_at (S k) t.
Proof.
  induction t as [n | x | t1 IH1 t2 IH2 | T t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
    intros k u H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. apply lc_bvar. lia.
    + apply lc_bvar. apply lc_bvar_inv in H. apply Nat.eqb_neq in E. lia.
  - apply lc_fvar.
  - apply lc_app_inv in H as [H1 H2].
    apply lc_app; [exact (IH1 k u H1) | exact (IH2 k u H2)].
  - apply lc_abs. apply lc_abs_inv in H. exact (IH1 (S k) u H).
  - apply lc_true.
  - apply lc_false.
  - apply lc_if_inv in H as [H1 [H2 H3]].
    apply lc_if; [exact (IH1 k u H1) | exact (IH2 k u H2) |
                  exact (IH3 k u H3)].
Qed.

(** Opening a locally closed term at a sufficiently large level does
    nothing. *)
Lemma lc_open_rec_id : forall t k, lc_at k t ->
  forall j u, k <= j -> open_rec j u t = t.
Proof.
  induction t as [n | x | t1 IH1 t2 IH2 | T t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
    intros k Hlc j u Hle; simpl.
  - destruct (Nat.eqb j n) eqn:E. apply Nat.eqb_eq in E. subst n.
    pose proof (lc_bvar_inv _ _ Hlc). lia.
    reflexivity.
  - reflexivity.
  - apply lc_app_inv in Hlc as [H1' H2'].
    rewrite (IH1 k H1' j u Hle), (IH2 k H2' j u Hle).
    reflexivity.
  - assert (H1 : lc_at (S k) t1) by (apply lc_abs_inv in Hlc; exact Hlc).
    rewrite (IH1 (S k) H1 (S j) u); [reflexivity | lia].
  - reflexivity.
  - reflexivity.
  - apply lc_if_inv in Hlc as [H1 [H2 H3]].
    rewrite (IH1 k H1 j u Hle), (IH2 k H2 j u Hle), (IH3 k H3 j u Hle).
    reflexivity.
Qed.

Lemma lc_open_rec_id' : forall t, locally_closed t ->
  forall j u, open_rec j u t = t.
Proof.
  intros t H j u. apply lc_open_rec_id with (k := 0); [exact H | lia].
Qed.

Lemma lc_step : forall t t', locally_closed t -> t --> t' -> locally_closed t'.
Proof.
  intros t t' Hlc Hst. revert Hlc. induction Hst; intros Hlc.
  - (* ST_AppAbs *)
    apply lc_app_inv in Hlc as [Habs Hv].
    apply lc_abs_inv in Habs.
    simpl. apply lc_at_open_rec with (k := 0); assumption.
  - (* ST_App1 *)
    apply lc_app_inv in Hlc as [H1 H2].
    apply lc_app; [apply IHHst; exact H1 | exact H2].
  - (* ST_App2 *)
    apply lc_app_inv in Hlc as [H1 H2].
    apply lc_app; [exact H1 | apply IHHst; exact H2].
  - (* ST_IfTrue *)
    apply lc_if_inv in Hlc as [H1 [H2 H3]]. exact H2.
  - (* ST_IfFalse *)
    apply lc_if_inv in Hlc as [H1 [H2 H3]]. exact H3.
  - (* ST_If *)
    apply lc_if_inv in Hlc as [H1 [H2 H3]].
    apply lc_if; [apply IHHst; exact H1 | exact H2 | exact H3].
Qed.

Lemma has_type_lc : forall Gamma t T, has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T Hty. induction Hty as
    [Gamma0 x T0 Hvar
    | L Gamma0 T1 T2 t1 Hbody IHbody
    | Gamma0 t1 t2 T1 T2 H1 IH1 H2 IH2
    | Gamma0 | Gamma0
    | Gamma0 t1 t2 t3 T0 H1 IH1 H2 IH2 H3 IH3].
  - simpl. apply lc_fvar.
  - simpl. apply lc_abs.
    destruct (fresh_atom L) as [x Hx].
    specialize (IHbody x Hx).
    exact (lc_at_open_down t1 0 (tm_fvar x) IHbody).
  - simpl. apply lc_app; assumption.
  - simpl. apply lc_true.
  - simpl. apply lc_false.
  - simpl. apply lc_if; assumption.
Qed.

(** ** Basic facts about strong normalization and values *)

Lemma SN_step : forall t t',
  strongly_normalizing t -> t --> t' -> strongly_normalizing t'.
Proof.
  intros t t' Hsn Hst. destruct Hsn as [t0 Hprem]. apply Hprem. exact Hst.
Qed.

Lemma value_no_step : forall t t', value t -> ~ (t --> t').
Proof. intros t t' Hv Hst. destruct Hv; inversion Hst. Qed.

Lemma SN_value : forall t, value t -> strongly_normalizing t.
Proof.
  intros t Hv. apply SN_intro. intros t' Hst.
  exfalso. eapply value_no_step; eauto.
Qed.

Lemma neutral_app : forall t1 t2, ~ value (tm_app t1 t2).
Proof. intros t1 t2 Hv. inversion Hv. Qed.

Lemma neutral_if : forall t1 t2 t3, ~ value (tm_if t1 t2 t3).
Proof. intros t1 t2 t3 Hv. inversion Hv. Qed.

(** ** Analysis of the small-step relation *)

Lemma step_app_inv : forall t u t'',
  tm_app t u --> t'' ->
  (exists T b v, t = tm_abs T b /\ u = v /\ value v /\ t'' = open b v) \/
  (exists t1', t --> t1' /\ t'' = tm_app t1' u) \/
  (exists u', u --> u' /\ t'' = tm_app t u').
Proof.
  intros t u t'' H. inversion H; subst; eauto 10.
Qed.

Lemma step_if_inv : forall b u w t'',
  tm_if b u w --> t'' ->
  (b = tm_true /\ t'' = u) \/ (b = tm_false /\ t'' = w) \/
  (exists b', b --> b' /\ t'' = tm_if b' u w).
Proof.
  intros b u w t'' H. inversion H; subst; eauto 10.
Qed.

(** ** The logical relation *)

Fixpoint R (T : ty) (t : tm) : Prop :=
  match T with
  | Ty_Bool => locally_closed t /\ strongly_normalizing t
  | Ty_Arrow T1 T2 =>
      locally_closed t /\
      strongly_normalizing t /\
      (forall u, R T1 u -> R T2 (tm_app t u))
  end.

Definition neutral (t : tm) : Prop := ~ value t.

Definition R_env (sigma : atom -> tm) (Gamma : context) : Prop :=
  (forall x, locally_closed (sigma x)) /\
  (forall x T, Gamma x = Some T -> R T (sigma x)).

Lemma R_lc : forall T t, R T t -> locally_closed t.
Proof. intros T; destruct T; intros t H; simpl in H; tauto. Qed.

Lemma R_sn : forall T t, R T t -> strongly_normalizing t.
Proof. intros T; destruct T; intros t H; simpl in H; tauto. Qed.

Lemma R_app : forall T1 T2 t u,
  R (Ty_Arrow T1 T2) t -> R T1 u -> R T2 (tm_app t u).
Proof.
  intros T1 T2 t u H Hu. simpl in H.
  destruct H as [Hlc [Hsn Happ]]. apply Happ. exact Hu.
Qed.

(** Closure of the relation under one reduction step. *)
Lemma R_step : forall T t t', R T t -> t --> t' -> R T t'.
Proof.
  induction T as [| T1 IH1 T2 IH2]; intros t t' HR Hst; simpl in *.
  - destruct HR as [Hlc Hsn]. split.
    + exact (lc_step t t' Hlc Hst).
    + exact (SN_step t t' Hsn Hst).
  - destruct HR as [Hlc [Hsn Happ]]. split; [ | split].
    + exact (lc_step t t' Hlc Hst).
    + exact (SN_step t t' Hsn Hst).
    + intros u Hu.
      apply (IH2 (tm_app t u) (tm_app t' u)).
      * exact (Happ u Hu).
      * apply ST_App1; [exact Hst | exact (R_lc T1 u Hu)].
Qed.

(** Expansion (CR3 restricted to neutral terms). *)
Lemma R_neutral : forall T t,
  locally_closed t ->
  neutral t ->
  strongly_normalizing t ->
  (forall t', t --> t' -> R T t') ->
  R T t.
Proof.
  induction T as [| T1 IH1 T2 IH2]; intros t Hlc Hn Hsn Hred; simpl.
  - split; assumption.
  - split; [exact Hlc | split; [exact Hsn |]].
    intros u Hu.
    pose proof (R_sn T1 u Hu) as Hsn_u.
    revert Hu.
    induction Hsn_u as [u0 Hprem IH_u].
    intros Hu.
    assert (Hreds_app : forall w, tm_app t u0 --> w -> R T2 w).
    { intros w Hst.
      destruct (step_app_inv t u0 w Hst) as
        [[T0 [b0 [v [Ht [Hu' [Hval Hw]]]]]] |
         [[t1' [Hst1 Hw]] | [u' [Hst2 Hw]]]].
      - subst t. exfalso. apply Hn. apply v_abs. exact Hlc.
      - subst w. apply (R_app T1 T2); [exact (Hred t1' Hst1) | exact Hu].
      - subst w. apply IH_u;
          [exact Hst2 | exact (R_step T1 u0 u' Hu Hst2)].
    }
    apply (IH2 (tm_app t u0)).
    + apply lc_app; [exact Hlc | exact (R_lc T1 u0 Hu)].
    + apply neutral_app.
    + apply SN_intro. intros w Hst. apply R_sn with (T := T2).
      apply Hreds_app. exact Hst.
    + exact Hreds_app.
Qed.

(** Abstraction introduction. *)
Lemma R_abs : forall T1 T2 b,
  locally_closed (tm_abs T1 b) ->
  (forall v, value v -> R T1 v -> R T2 (open b v)) ->
  R (Ty_Arrow T1 T2) (tm_abs T1 b).
Proof.
  intros T1 T2 b Hlc Hbody. simpl. split; [exact Hlc | split].
  - apply SN_value. apply v_abs. exact Hlc.
  - intros u Hu.
    pose proof (R_sn T1 u Hu) as Hsn_u.
    revert Hu.
    induction Hsn_u as [u0 Hprem IH_u].
    intros Hu.
    assert (Hreds_app : forall w, tm_app (tm_abs T1 b) u0 --> w -> R T2 w).
    { intros w Hst.
      destruct (step_app_inv (tm_abs T1 b) u0 w Hst) as
        [[T0 [b0 [v [Ht [Hu' [Hval Hw]]]]]] |
         [[t1' [Hst1 Hw]] | [u' [Hst2 Hw]]]].
      - inversion Ht; subst; subst.
        apply Hbody; assumption.
      - subst w. exfalso. exact (value_no_step _ _ (v_abs T1 b Hlc) Hst1).
      - subst w. apply IH_u;
          [exact Hst2 | exact (R_step T1 u0 u' Hu Hst2)].
    }
    apply (R_neutral T2).
    + apply lc_app; [exact Hlc | exact (R_lc T1 u0 Hu)].
    + apply neutral_app.
    + apply SN_intro. intros w Hst. apply R_sn with (T := T2).
      apply Hreds_app. exact Hst.
    + exact Hreds_app.
Qed.

(** Conditional introduction. *)
Lemma R_if : forall T b u w,
  R Ty_Bool b -> R T u -> R T w -> R T (tm_if b u w).
Proof.
  intros T b u w Hb Hu Hw.
  pose proof (R_sn Ty_Bool b Hb) as Hsn_b.
  revert Hb Hu Hw.
  induction Hsn_b as [b0 Hprem IH_b].
  intros Hb Hu Hw.
  assert (Hreds : forall t'', tm_if b0 u w --> t'' -> R T t'').
  { intros t'' Hst.
    destruct (step_if_inv b0 u w t'' Hst) as
      [[Hb' Ht''] | [[Hb' Ht''] | [b' [Hst' Ht'']]]].
    - subst. exact Hu.
    - subst. exact Hw.
    - subst. apply IH_b;
        [exact Hst' | exact (R_step Ty_Bool b0 b' Hb Hst') | exact Hu | exact Hw].
  }
  apply (R_neutral T).
  - apply lc_if; [exact (R_lc Ty_Bool b0 Hb) | exact (R_lc T u Hu) |
                  exact (R_lc T w Hw)].
  - apply neutral_if.
  - apply SN_intro. intros t'' Hst. apply R_sn with (T := T).
    apply Hreds. exact Hst.
  - exact Hreds.
Qed.

(** ** Environment lemmas *)

Lemma R_env_update : forall sigma Gamma x T1 v,
  R T1 v -> R_env sigma Gamma -> R_env (upd sigma x v) (update Gamma x T1).
Proof.
  intros sigma Gamma x T1 v HRv [Hlc Hsem]. split.
  - intros y. unfold upd. destruct (Nat.eqb x y).
    + apply R_lc with (T := T1). exact HRv.
    + apply Hlc.
  - intros y S HS. unfold update in HS.
    destruct (Nat.eqb x y) eqn:E.
    + inversion HS; subst. unfold upd. rewrite E. exact HRv.
    + unfold upd. rewrite E. apply Hsem. exact HS.
Qed.

(** ** Substitution preserves local closure *)

Lemma subst_tm_lc_at : forall sigma t k,
  (forall x, lc_at k (sigma x)) -> lc_at k t -> lc_at k (subst_tm sigma t).
Proof.
  intros sigma t. induction t as
    [n | x | t1 IH1 t2 IH2 | T t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
    intros k Hsig Hlc; simpl.
  - exact Hlc.
  - apply Hsig.
  - apply lc_app_inv in Hlc as [H1 H2].
    apply lc_app; [exact (IH1 k Hsig H1) | exact (IH2 k Hsig H2)].
  - apply lc_abs. apply lc_abs_inv in Hlc.
    apply (IH1 (S k)).
    + intros x. apply lc_at_mono with (k := k); [lia | apply Hsig].
    + exact Hlc.
  - apply lc_true.
  - apply lc_false.
  - apply lc_if_inv in Hlc as [H1 [H2 H3]].
    apply lc_if; [exact (IH1 k Hsig H1) | exact (IH2 k Hsig H2) |
                  exact (IH3 k Hsig H3)].
Qed.

(** ** The fundamental theorem of the logical relation *)

Theorem fundamental : forall Gamma t T,
  has_type Gamma t T ->
  forall sigma, R_env sigma Gamma -> R T (subst_tm sigma t).
Proof.
  intros Gamma t T Hty. induction Hty as
    [Gamma0 x T0 Hvar
    | L Gamma0 T1 T2 t1 Hbody IHbody
    | Gamma0 t1 t2 T1 T2 H1 IH1 H2 IH2
    | Gamma0 | Gamma0
    | Gamma0 t1 t2 t3 T0 H1 IH1 H2 IH2 H3 IH3];
    intros sigma Hsig; simpl.
  - apply (proj2 Hsig). exact Hvar.
  - apply R_abs.
    + apply lc_abs.
      apply subst_tm_lc_at with (k := 1).
      * intros x. apply lc_at_mono with (k := 0); [lia | apply (proj1 Hsig)].
      * pose proof (has_type_lc _ _ _ (T_Abs L Gamma0 T1 T2 t1 Hbody)) as Hlca.
        apply lc_abs_inv in Hlca. exact Hlca.
    + intros v Hval HRv.
      destruct (fresh_atom_two L (fv t1)) as [x [HxL Hxfv]].
      specialize (IHbody x HxL).
      specialize (IHbody (upd sigma x v)).
      assert (Himg : forall y j w, open_rec j w (upd sigma x v y) = upd sigma x v y).
      { intros y j w. apply lc_open_rec_id with (k := 0); [| lia].
        unfold upd. destruct (Nat.eqb x y).
        - apply R_lc with (T := T1). exact HRv.
        - apply (proj1 Hsig). }
      assert (Heq : subst_tm (upd sigma x v) (open t1 (tm_fvar x)) =
                    open (subst_tm sigma t1) v).
      { unfold open. rewrite (subst_tm_open_rec (upd sigma x v) 0 (tm_fvar x) t1 Himg).
        assert (Hx : subst_tm (upd sigma x v) (tm_fvar x) = v).
        { simpl. unfold upd. rewrite Nat.eqb_refl. reflexivity. }
        rewrite Hx.
        rewrite (subst_tm_upd_agree t1 x v sigma Hxfv).
        reflexivity. }
      rewrite <- Heq.
      apply IHbody.
      apply R_env_update; assumption.
  - apply (R_app T1 T2); [exact (IH1 sigma Hsig) | exact (IH2 sigma Hsig)].
  - split; [apply lc_true | apply SN_value; apply v_true].
  - split; [apply lc_false | apply SN_value; apply v_false].
  - apply R_if; [exact (IH1 sigma Hsig) | exact (IH2 sigma Hsig) |
                 exact (IH3 sigma Hsig)].
Qed.

(** ** Target theorem: strong normalization for the supplied CBV relation *)

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  assert (HR0 : R T (subst_tm (fun x => tm_fvar x) t)).
  { apply (fundamental empty t T Hty). split.
    - intros x. apply lc_fvar.
    - intros x S HS. unfold empty in HS. discriminate. }
  rewrite subst_tm_fvar_id in HR0.
  exact (R_sn T t HR0).
Qed.

End STLCCBVNormalizationTask.
