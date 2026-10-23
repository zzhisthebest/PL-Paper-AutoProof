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

(** **************************************************************** *)
(** * Auxiliary definitions and lemmas for the normalization proof    *)
(** **************************************************************** *)

(** ** Free variables and freshness *)

Fixpoint fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ => nil
  | tm_fvar x => x :: nil
  | tm_app t1 t2 => fv t1 ++ fv t2
  | tm_abs _ t1 => fv t1
  | tm_true => nil
  | tm_false => nil
  end.

Fixpoint max_atom (l : list atom) : atom :=
  match l with
  | nil => 0
  | x :: xs => Nat.max x (max_atom xs)
  end.

Lemma in_max_atom : forall (l : list atom) x, In x l -> x <= max_atom l.
Proof.
  induction l as [| a l IH]; intros x Hx; simpl in *.
  - destruct Hx.
  - destruct Hx as [-> | Hx].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; eauto | apply Nat.le_max_r].
Qed.

Lemma fresh_atom : forall l : list atom, exists x, ~ In x l.
Proof.
  intros l. exists (S (max_atom l)).
  intros Hx. pose proof (in_max_atom l _ Hx). lia.
Qed.

(** ** Free-variable substitution *)

Fixpoint subst_tm (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_app t1 t2 => tm_app (subst_tm sigma t1) (subst_tm sigma t2)
  | tm_abs T t1 => tm_abs T (subst_tm sigma t1)
  | tm_true => tm_true
  | tm_false => tm_false
  end.

Definition update_env (rho : atom -> tm) (x : atom) (w : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then w else rho y.

Lemma update_env_same : forall rho x w, update_env rho x w x = w.
Proof. intros. unfold update_env. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma update_env_other : forall rho x w y, x <> y -> update_env rho x w y = rho y.
Proof.
  intros rho x w y Hne. unfold update_env.
  destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. congruence.
  - reflexivity.
Qed.

(** Opening a locally closed term at a level above all its bound variables
    has no effect. *)
Lemma open_rec_lc : forall t k u m, m <= k -> lc_at m t -> open_rec k u t = t.
Proof.
  intros t. induction t; intros k u m Hle Hlc; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst k. inversion Hlc; subst. exfalso. lia.
    + reflexivity.
  - reflexivity.
  - inversion Hlc; subst. f_equal.
    + apply IHt1 with (m := m); assumption.
    + apply IHt2 with (m := m); assumption.
  - inversion Hlc; subst. f_equal. apply IHt with (m := S m); [lia | assumption].
  - reflexivity.
  - reflexivity.
Qed.

Lemma subst_tm_open_rec : forall sigma k u t,
  (forall x, lc_at 0 (sigma x)) ->
  subst_tm sigma (open_rec k u t) = open_rec k (subst_tm sigma u) (subst_tm sigma t).
Proof.
  intros sigma k u t Hsig. revert k u.
  induction t; intros k u; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. apply open_rec_lc with (m := 0); [lia | apply Hsig].
  - rewrite IHt1, IHt2; reflexivity.
  - rewrite IHt. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma subst_tm_update_notin : forall rho x w t,
  ~ In x (fv t) -> subst_tm (update_env rho x w) t = subst_tm rho t.
Proof.
  intros rho x w t Hx. induction t; simpl.
  - reflexivity.
  - destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E. subst a. exfalso. apply Hx. simpl. left. reflexivity.
    + apply update_env_other. apply Nat.eqb_neq in E. auto.
  - f_equal.
    + apply IHt1. intros Hin. apply Hx. apply in_or_app. left. exact Hin.
    + apply IHt2. intros Hin. apply Hx. apply in_or_app. right. exact Hin.
  - f_equal. apply IHt. exact Hx.
  - reflexivity.
  - reflexivity.
Qed.

Lemma subst_tm_id : forall t, subst_tm (fun x => tm_fvar x) t = t.
Proof.
  induction t; simpl; try reflexivity.
  - f_equal; assumption.
  - f_equal; assumption.
Qed.

(** ** Closure properties of [lc_at] *)

Lemma lc_at_mono : forall t k k', k <= k' -> lc_at k t -> lc_at k' t.
Proof.
  intros t k k' Hle H. revert k' Hle.
  induction H as [k0 i Hi | k0 x | k0 t1 t2 H1 IH1 H2 IH2 | k0 T0 t1 H1 IH1 | k0 | k0];
    intros k' Hle.
  - constructor. lia.
  - constructor.
  - constructor; [apply IH1 | apply IH2]; lia.
  - constructor. apply IH1. lia.
  - constructor.
  - constructor.
Qed.

Lemma lc_open_rec_gen : forall n t, lc_at n t ->
  forall k u, n = S k -> lc_at k u -> lc_at k (open_rec k u t).
Proof.
  intros n t H.
  induction H as [k0 i Hi | k0 x | k0 t1 t2 H1 IH1 H2 IH2 | k0 T0 t1 H1 IH1 | k0 | k0];
    intros k u Hn Hu; simpl.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst. exact Hu.
    + constructor. apply Nat.eqb_neq in E. lia.
  - constructor.
  - constructor; [apply IH1 with (k := k) | apply IH2 with (k := k)]; auto.
  - constructor. apply IH1 with (k := S k).
    + lia.
    + apply lc_at_mono with (k := k); [lia | exact Hu].
  - constructor.
  - constructor.
Qed.

Lemma lc_open_rec : forall k u t, lc_at (S k) t -> lc_at k u -> lc_at k (open_rec k u t).
Proof. intros. eapply lc_open_rec_gen; eauto. Qed.

Lemma lc_open_rec_inv : forall k u t, lc_at k (open_rec k u t) -> lc_at (S k) t.
Proof.
  intros k u t. revert k u.
  induction t; intros k u H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. constructor. lia.
    + apply Nat.eqb_neq in E. constructor. inversion H; subst; lia.
  - constructor.
  - inversion H; subst. constructor.
    + eapply IHt1; eauto.
    + eapply IHt2; eauto.
  - inversion H; subst. constructor. apply IHt with (u := u). assumption.
  - constructor.
  - constructor.
Qed.

Lemma lc_abs_inv : forall k T t, lc_at k (tm_abs T t) -> lc_at (S k) t.
Proof. intros. inversion H. assumption. Qed.

Lemma lc_subst_tm : forall t k, lc_at k t ->
  forall sigma, (forall x, lc_at k (sigma x)) -> lc_at k (subst_tm sigma t).
Proof.
  intros t. induction t; intros k Hk sigma Hs; simpl.
  - inversion Hk; subst. constructor. assumption.
  - apply Hs.
  - inversion Hk; subst. constructor; auto.
  - inversion Hk; subst. constructor. apply IHt with (k := S k).
    + assumption.
    + intros x. apply lc_at_mono with (k := k); [lia | apply Hs].
  - constructor.
  - constructor.
Qed.

(** ** Typing implies local closure *)

Lemma has_type_lc : forall Gamma t T, has_type Gamma t T -> lc_at 0 t.
Proof.
  intros Gamma t T H.
  induction H as [Gamma0 x T0 Hvar
                 | L Gamma0 T1 T2 t1 Hbody IHbody
                 | Gamma0 t1 t2 T1 T2 H1 IH1 H2 IH2
                 | Gamma0
                 | Gamma0].
  - constructor.
  - constructor.
    destruct (fresh_atom L) as [x Hx].
    apply lc_open_rec_inv with (u := tm_fvar x) (k := 0).
    apply IHbody. exact Hx.
  - constructor; assumption.
  - constructor.
  - constructor.
Qed.

(** ** The step relation: values are irreducible, and step is deterministic *)

Lemma value_no_step : forall v t, value v -> ~ step v t.
Proof.
  intros v t Hv Hst. destruct Hv; inversion Hst.
Qed.

Lemma step_det : forall t u1 u2, step t u1 -> step t u2 -> u1 = u2.
Proof.
  intros t. induction t; intros u1 u2 H1 H2.
  - inversion H1.
  - inversion H1.
  - inversion H1 as [Ta ba va Hlca Hva | a a' b Hsa Hlcb | b1 b2 b2' Hvb Hsb]; subst.
    + inversion H2 as [Ta' ba' va' Hlca' Hva' | a'' a''' b'' Hsa' Hlcb' | b1' b2'' b2''' Hvb' Hsb']; subst.
      * reflexivity.
      * exfalso. eapply value_no_step; [constructor; exact Hlca | exact Hsa'].
      * exfalso. eapply value_no_step; [exact Hva | exact Hsb'].
    + inversion H2 as [Ta' ba' va' Hlca' Hva' | a'' a''' b'' Hsa' Hlcb' | b1' b2'' b2''' Hvb' Hsb']; subst.
      * exfalso. eapply value_no_step; [constructor; exact Hlca' | exact Hsa].
      * f_equal. eapply IHt1; eauto.
      * exfalso. eapply value_no_step; [exact Hvb' | exact Hsa].
    + inversion H2 as [Ta' ba' va' Hlca' Hva' | a'' a''' b'' Hsa' Hlcb' | b1' b2'' b2''' Hvb' Hsb']; subst.
      * exfalso. eapply value_no_step; [exact Hva' | exact Hsb].
      * exfalso. eapply value_no_step; [exact Hvb | exact Hsa'].
      * f_equal. eapply IHt2; eauto.
  - inversion H1.
  - inversion H1.
  - inversion H1.
Qed.

(** ** Multi-step lemmas *)

Lemma multi_trans : forall t1 t2 t3,
  multi step t1 t2 -> multi step t2 t3 -> multi step t1 t3.
Proof.
  intros t1 t2 t3 H. induction H as [x | x y z Hstep Hmulti IH].
  - intros H23. exact H23.
  - intros H23. eapply multi_step; [exact Hstep | apply IH; exact H23].
Qed.

Lemma multi_app_l : forall t1 t1', multi step t1 t1' ->
  forall t2, lc_at 0 t2 -> multi step (tm_app t1 t2) (tm_app t1' t2).
Proof.
  intros t1 t1' H. induction H as [x | x y z Hstep Hmulti IH].
  - intros t2 Hlc. apply multi_refl.
  - intros t2 Hlc. eapply multi_step.
    + apply ST_App1; [exact Hstep | exact Hlc].
    + apply IH. exact Hlc.
Qed.

Lemma multi_app_r : forall v1 t2 t2', value v1 ->
  multi step t2 t2' -> multi step (tm_app v1 t2) (tm_app v1 t2').
Proof.
  intros v1 t2 t2' Hv H. induction H as [x | x y z Hstep Hmulti IH].
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_App2; [exact Hv | exact Hstep].
    + apply IH.
Qed.

Lemma multi_sn : forall t v,
  multi step t v -> (forall w, ~ step v w) -> strongly_normalizing t.
Proof.
  intros t v H. induction H as [x | x y z Hstep Hmulti IH].
  - intros Hnf. apply SN_intro. intros t' Hst. exfalso. apply (Hnf t' Hst).
  - intros Hnf. apply SN_intro. intros t' Hst.
    assert (Heq : t' = y) by (eapply step_det; eauto).
    subst t'. apply IH. exact Hnf.
Qed.

(** ** The type-indexed logical relation

    [VR T v] says that the value [v] is semantically of type [T];
    [LR T t] says that [t] reduces to such a value and is locally closed. *)

Fixpoint LR (T : ty) (t : tm) {struct T} : Prop :=
  match T with
  | Ty_Bool =>
      lc_at 0 t /\
      exists v, multi step t v /\ (v = tm_true \/ v = tm_false)
  | Ty_Arrow T1 T2 =>
      lc_at 0 t /\
      exists body,
        multi step t (tm_abs T1 body) /\
        lc_at 1 body /\
        (forall w, VR T1 w -> LR T2 (open body w))
  end
with VR (T : ty) (v : tm) {struct T} : Prop :=
  match T with
  | Ty_Bool => v = tm_true \/ v = tm_false
  | Ty_Arrow T1 T2 =>
      exists body,
        v = tm_abs T1 body /\
        lc_at 1 body /\
        (forall w, VR T1 w -> LR T2 (open body w))
  end.

Lemma VR_value : forall T v, VR T v -> value v.
Proof.
  intros T v H. destruct T; simpl in H.
  - destruct H as [-> | ->]; constructor.
  - destruct H as [body [-> [Hlc _]]]. constructor. constructor. exact Hlc.
Qed.

Lemma VR_lc : forall T v, VR T v -> lc_at 0 v.
Proof.
  intros T v H. destruct T; simpl in H.
  - destruct H as [-> | ->]; constructor.
  - destruct H as [body [-> [Hlc _]]]. constructor. exact Hlc.
Qed.

Lemma LR_lc : forall T t, LR T t -> lc_at 0 t.
Proof.
  intros T t H. destruct T; simpl in H; apply (proj1 H).
Qed.

Lemma LR_pack : forall T t v,
  lc_at 0 t -> multi step t v -> VR T v -> LR T t.
Proof.
  intros T t v Hlc Hm HV. destruct T; simpl.
  - simpl in HV. split; [exact Hlc | exists v; split; assumption].
  - simpl in HV. destruct HV as [body [Heq [Hlcbody Hsem]]]. subst v.
    split; [exact Hlc | exists body; split; [exact Hm | split; assumption]].
Qed.

Lemma VR_LR : forall T v, VR T v -> LR T v.
Proof.
  intros T v H. apply LR_pack with (v := v).
  - apply VR_lc with (T := T). exact H.
  - apply multi_refl.
  - exact H.
Qed.

Lemma LR_to_VR : forall T t, LR T t -> exists v, multi step t v /\ VR T v.
Proof.
  intros T t H. destruct T; simpl in H.
  - destruct H as [Hlc [v [Hm Hv]]]. exists v. split; assumption.
  - destruct H as [Hlc [body [Hm [Hlcbody Hsem]]]].
    exists (tm_abs T1 body). split; [exact Hm |].
    simpl. exists body. split; [reflexivity | split; assumption].
Qed.

(** The application obligation of the logical relation. *)

Lemma LR_app : forall T1 T2 t1 t2,
  LR (Ty_Arrow T1 T2) t1 -> LR T1 t2 -> LR T2 (tm_app t1 t2).
Proof.
  intros T1 T2 t1 t2 H1 H2.
  simpl in H1. destruct H1 as [Hlc1 [body [Hm1 [Hlcbody Hsem]]]].
  destruct (LR_to_VR T1 t2 H2) as [v2 [Hm2 HV2]].
  assert (Hval_body : value (tm_abs T1 body)) by (constructor; constructor; exact Hlcbody).
  assert (Hval2 : value v2) by (apply VR_value with (T := T1); exact HV2).
  assert (Hlr : LR T2 (open body v2)) by (apply Hsem; exact HV2).
  destruct (LR_to_VR T2 (open body v2) Hlr) as [v3 [Hm3 HV3]].
  apply LR_pack with (v := v3).
  - constructor.
    + exact Hlc1.
    + apply LR_lc with (T := T1). exact H2.
  - eapply multi_trans.
    + eapply multi_trans.
      * eapply multi_trans.
        -- eapply multi_app_l; [exact Hm1 | apply LR_lc with (T := T1); exact H2].
        -- eapply multi_app_r; [exact Hval_body | exact Hm2].
      * eapply multi_step.
        -- apply ST_AppAbs; [constructor; exact Hlcbody | exact Hval2].
        -- apply multi_refl.
    + exact Hm3.
  - exact HV3.
Qed.

(** Strong normalization follows from the logical relation. *)

Lemma LR_sn : forall T t, LR T t -> strongly_normalizing t.
Proof.
  intros T t H.
  destruct (LR_to_VR T t H) as [v [Hm HV]].
  eapply multi_sn; [exact Hm |].
  intros w Hst. exact (value_no_step v w (VR_value T v HV) Hst).
Qed.

(** ** Interpretation of typing contexts by term substitutions *)

Definition env_sem (Gamma : context) (rho : atom -> tm) : Prop :=
  (forall x, lc_at 0 (rho x)) /\
  (forall x T, Gamma x = Some T -> LR T (rho x)).

(** ** Fundamental theorem of the logical relation *)

Lemma fundamental : forall Gamma t T,
  has_type Gamma t T -> forall rho, env_sem Gamma rho -> LR T (subst_tm rho t).
Proof.
  intros Gamma t T H.
  induction H as [Gamma0 x T0 Hvar
                 | L Gamma0 T1 T2 t1 Hbody IHbody
                 | Gamma0 t1 t2 T1 T2 H1 IH1 H2 IH2
                 | Gamma0
                 | Gamma0].
  - (* T_Var *)
    intros rho [Henv_lc Henv_ty]. simpl. apply Henv_ty. exact Hvar.
  - (* T_Abs *)
    intros rho [Henv_lc Henv_ty]. simpl.
    assert (Hbody_lc : lc_at 1 (subst_tm rho t1)).
    { apply lc_subst_tm with (k := 1).
      - apply lc_abs_inv with (T := T1).
        apply has_type_lc with (Gamma := Gamma0) (T := Ty_Arrow T1 T2).
        apply T_Abs with (L := L). exact Hbody.
      - intros x. apply lc_at_mono with (k := 0); [lia | apply Henv_lc]. }
    split.
    + constructor. exact Hbody_lc.
    + exists (subst_tm rho t1). split.
      * apply multi_refl.
      * split.
        -- exact Hbody_lc.
        -- intros w Hw.
           destruct (fresh_atom (L ++ fv t1)) as [x Hx].
           assert (HxL : ~ In x L).
           { intros Hin. apply Hx. apply in_or_app. left. exact Hin. }
           assert (Hxfv : ~ In x (fv t1)).
           { intros Hin. apply Hx. apply in_or_app. right. exact Hin. }
           assert (Henv' : env_sem (update Gamma0 x T1) (update_env rho x w)).
           { split.
             - intros y. unfold update_env. destruct (Nat.eqb x y) eqn:E.
               + apply VR_lc with (T := T1). exact Hw.
               + apply Henv_lc.
             - intros y T' Hty'. unfold update_env. destruct (Nat.eqb x y) eqn:E.
               + apply Nat.eqb_eq in E. subst y.
                 unfold update in Hty'. rewrite Nat.eqb_refl in Hty'.
                 injection Hty' as <-. apply VR_LR. exact Hw.
               + apply Henv_ty with (T := T'). unfold update in Hty'. rewrite E in Hty'. exact Hty'. }
           pose proof (IHbody x HxL (update_env rho x w) Henv') as Hlr.
           assert (Heq : subst_tm (update_env rho x w) (open t1 (tm_fvar x))
                       = open (subst_tm rho t1) w).
           { assert (Hsig : forall y, lc_at 0 (update_env rho x w y)).
             { intros y. unfold update_env. destruct (Nat.eqb x y) eqn:E.
               - apply VR_lc with (T := T1). exact Hw.
               - apply Henv_lc. }
             unfold open.
             rewrite (subst_tm_open_rec (update_env rho x w) 0 (tm_fvar x) t1 Hsig).
             simpl. rewrite update_env_same.
             rewrite (subst_tm_update_notin rho x w t1 Hxfv). reflexivity. }
           rewrite Heq in Hlr. exact Hlr.
  - (* T_App *)
    intros rho [Henv_lc Henv_ty]. simpl.
    apply LR_app with (T1 := T1) (T2 := T2).
    + apply IH1. split; assumption.
    + apply IH2. split; assumption.
  - (* T_True *)
    intros rho [Henv_lc Henv_ty]. simpl. split.
    + constructor.
    + exists tm_true. split; [apply multi_refl | left; reflexivity].
  - (* T_False *)
    intros rho [Henv_lc Henv_ty]. simpl. split.
    + constructor.
    + exists tm_false. split; [apply multi_refl | right; reflexivity].
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  assert (Henv : env_sem empty (fun x => tm_fvar x)).
  { split.
    - intros x. constructor.
    - intros x T' Hc. unfold empty in Hc. discriminate. }
  pose proof (fundamental empty t T Hty (fun x => tm_fvar x) Henv) as Hlr.
  rewrite subst_tm_id in Hlr.
  apply LR_sn in Hlr. exact Hlr.
Qed.

End STLCNormalizationNoneHardTask.
