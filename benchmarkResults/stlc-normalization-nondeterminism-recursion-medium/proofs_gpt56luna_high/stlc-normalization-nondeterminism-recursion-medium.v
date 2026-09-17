(** STLC CBV strong-normalization benchmark, Medium variant.
    Features: nondeterminism-recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Relations.Relation_Definitions Lia.
Import ListNotations.

Module STLCNormalizationNondeterminismRecursionMediumTask.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
      R x y ->
      multi R y z ->
      multi R x z.

Definition atom := nat.

Inductive ty : Type :=
  | Ty_Bool : ty
  | Ty_Nat : ty
  | Ty_Arrow : ty -> ty -> ty.

Inductive tm : Type :=
  | tm_bvar : nat -> tm
  | tm_fvar : atom -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : ty -> tm -> tm
  | tm_true : tm
  | tm_false : tm
  | tm_zero : tm
  | tm_succ : tm -> tm

  | tm_natrec : tm -> tm -> tm -> tm
  | tm_choice : tm -> tm -> tm.

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
Notation "'zero'" := tm_zero
  (in custom stlc_tm at level 0) : stlc_scope.
Notation "'succ' t" := (tm_succ t)
  (in custom stlc_tm at level 9, t custom stlc_tm at level 0) : stlc_scope.
Notation "'rec' n b s" := (tm_natrec n b s)
  (in custom stlc_tm at level 9,
   n custom stlc_tm at level 0, b custom stlc_tm at level 0,
   s custom stlc_tm at level 0) : stlc_scope.
Notation "'Nat'" := Ty_Nat
  (in custom stlc_ty at level 0) : stlc_scope.

Notation "'choice' t1 'or' t2" := (tm_choice t1 t2)
  (in custom stlc_tm at level 200,
   t1 custom stlc_tm, t2 custom stlc_tm at level 200) : stlc_scope.

Fixpoint open_rec (k : nat) (u : tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => if Nat.eqb k i then u else tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_app t1 t2 => tm_app (open_rec k u t1) (open_rec k u t2)
  | tm_abs T t1 => tm_abs T (open_rec (S k) u t1)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (open_rec k u t1)
  | tm_natrec n b s =>
      tm_natrec (open_rec k u n) (open_rec k u b) (open_rec k u s)
  | tm_choice t1 t2 => tm_choice (open_rec k u t1) (open_rec k u t2)
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
  | lc_zero : forall k, lc_at k tm_zero
  | lc_succ : forall k t, lc_at k t -> lc_at k (tm_succ t)
  | lc_rec : forall k n b s,
      lc_at k n -> lc_at k b -> lc_at k s ->
      lc_at k (tm_natrec n b s)
    | lc_choice : forall k t1 t2,
      lc_at k t1 -> lc_at k t2 -> lc_at k (tm_choice t1 t2).

Definition locally_closed (t : tm) : Prop := lc_at 0 t.

Hint Constructors lc_at : core.

Inductive numeric_value : tm -> Prop :=
  | nv_zero : numeric_value tm_zero
  | nv_succ : forall (t : tm), numeric_value t -> numeric_value (tm_succ t).

Inductive value : tm -> Prop :=
  | v_abs : forall T t,
      locally_closed (tm_abs T t) ->
      value (tm_abs T t)
  | v_true :
      value tm_true
  | v_false :
      value tm_false
  | v_nat : forall n, numeric_value n -> value n.

Hint Constructors value : core.

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
  | ST_Succ : forall t t',
      t --> t' -> tm_succ t --> tm_succ t'
  | ST_RecArg : forall n n' b s,

      n --> n' -> locally_closed b -> locally_closed s ->
      tm_natrec n b s --> tm_natrec n' b s
  | ST_RecBase : forall n b b' s,

      numeric_value n -> b --> b' -> locally_closed s ->
      tm_natrec n b s --> tm_natrec n b' s
  | ST_RecStep : forall n b s s',

      numeric_value n -> value b -> s --> s' ->
      tm_natrec n b s --> tm_natrec n b s'
  | ST_RecZero : forall b s,

      value b -> value s -> tm_natrec tm_zero b s --> b
  | ST_RecSucc : forall n b s,

      numeric_value n -> value b -> value s ->
      tm_natrec (tm_succ n) b s -->
        tm_app (tm_app s n) (tm_natrec n b s)
  | ST_ChoiceLeft : forall t1 t2,
      locally_closed t1 ->
      locally_closed t2 ->
      tm_choice t1 t2 --> t1
  | ST_ChoiceRight : forall t1 t2,
      locally_closed t1 ->
      locally_closed t2 ->
      tm_choice t1 t2 --> t2
where "t '-->' t'" := (step t t').

Hint Constructors step : core.

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

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
  | T_Zero : forall Gamma,
      <{ Gamma |-- zero \in Nat }>
  | T_Succ : forall Gamma n,
      <{ Gamma |-- $(n) \in Nat }> ->
      <{ Gamma |-- succ $(n) \in Nat }>
  | T_Rec : forall Gamma n b s T,
      <{ Gamma |-- $(n) \in Nat }> ->
      <{ Gamma |-- $(b) \in T }> ->
      <{ Gamma |-- $(s) \in Nat -> T -> T }> ->
      <{ Gamma |-- rec $(n) $(b) $(s) \in T }>
  | T_Choice : forall Gamma t1 t2 T,
      <{ Gamma |-- $(t1) \in T }> ->
      <{ Gamma |-- $(t2) \in T }> ->
      <{ Gamma |-- choice $(t1) or $(t2) \in T }>
where "<{ Gamma '|--' t '\in' T }>" := (has_type Gamma t T)
  : stlc_scope.

Hint Constructors has_type : core.

Inductive strongly_normalizing : tm -> Prop :=

  | SN_intro : forall t,
      (forall t', t --> t' -> strongly_normalizing t') ->
      strongly_normalizing t.

Definition term_substitution := atom -> tm.

Definition id_substitution : term_substitution :=
  fun x => tm_fvar x.

Definition subst_update
    (rho : term_substitution) (x : atom) (v : tm) : term_substitution :=
  fun y => if Nat.eqb x y then v else rho y.

Fixpoint msubst (rho : term_substitution) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => rho x
  | tm_app t1 t2 => tm_app (msubst rho t1) (msubst rho t2)
  | tm_abs T t1 => tm_abs T (msubst rho t1)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_zero => tm_zero
  | tm_succ t => tm_succ (msubst rho t)
  | tm_natrec n b s => tm_natrec (msubst rho n) (msubst rho b) (msubst rho s)
  | tm_choice t1 t2 => tm_choice (msubst rho t1) (msubst rho t2)
  end.

Definition proper_substitution (rho : term_substitution) : Prop :=
  forall x, locally_closed (rho x).

Fixpoint strong_value_relation (T : ty) (v : tm) : Prop :=
  value v /\
  match T with
  | Ty_Nat => numeric_value v
  | Ty_Bool =>
      v = tm_true \/ v = tm_false
  | Ty_Arrow T1 T2 =>
      exists body,
        v = tm_abs T1 body /\
        forall arg,
          strong_value_relation T1 arg ->
          locally_closed (open body arg) /\
          strongly_normalizing (open body arg) /\
          forall result,
            open body arg -->* result ->
            value result ->
            strong_value_relation T2 result
  end.

Definition strong_expression_relation (T : ty) (t : tm) : Prop :=
  locally_closed t /\
  strongly_normalizing t /\
  forall v,
    t -->* v ->
    value v ->
    strong_value_relation T v.

Definition strong_related_substitution
    (Gamma : context) (rho : term_substitution) : Prop :=
    forall x T,
    Gamma x = Some T ->
    strong_value_relation T (rho x).

Lemma multi_trans : forall t u v, t -->* u -> u -->* v -> t -->* v.
Proof.
  intros t u v Htu Huv. induction Htu as [t|t u w Htu Hwv IH].
  - exact Huv.
  - eapply multi_step; eauto.
Qed.

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v Hv. induction Hv.
  - exact H.
  - constructor.
  - constructor.
  - induction H.
    + constructor.
    + constructor; auto.
Qed.

Lemma numeric_lc : forall n, numeric_value n -> locally_closed n.
Proof.
  intros n H. induction H; constructor; auto.
Qed.

Lemma lc_weaken : forall k t, lc_at k t -> lc_at (S k) t.
Proof.
  intros k t H. induction H; constructor; eauto; lia.
Qed.

Lemma lc_rec_parts : forall n b s,
    locally_closed (tm_natrec n b s) ->
    locally_closed n /\ locally_closed b /\ locally_closed s.
Proof.
  intros n b s H. inversion H; auto.
Qed.

Lemma lc_succ_part : forall n, locally_closed (tm_succ n) -> locally_closed n.
Proof. intros n H. inversion H; assumption. Qed.

Lemma lc_open_rec : forall k t u,
    lc_at (S k) t -> lc_at k u -> lc_at k (open_rec k u t).
Proof.
  intros k t. revert k.
  induction t; intros k u Ht Hu; simpl in *.
  - inversion Ht; subst. destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. exact Hu.
    + constructor. apply Nat.eqb_neq in E. lia.
  - inversion Ht. constructor.
  - inversion Ht; subst. constructor.
    + eapply IHt1; eauto.
    + eapply IHt2; eauto.
  - inversion Ht; subst. constructor.
    apply IHt; [assumption | apply lc_weaken; assumption].
  - inversion Ht. constructor.
  - inversion Ht. constructor.
  - inversion Ht. constructor.
  - inversion Ht; subst. constructor; eauto.
  - inversion Ht; subst. constructor; eauto.
  - inversion Ht; subst. constructor; eauto.
Qed.

Lemma lc_open : forall t u,
    lc_at 1 t -> locally_closed u -> locally_closed (open t u).
Proof.
  intros. unfold locally_closed, open. eapply lc_open_rec; eauto.
Qed.

Lemma lc_step : forall t t', locally_closed t -> t --> t' -> locally_closed t'.
Proof.
  intros t t' Hlc Hs. revert Hlc.
  induction Hs as
    [T t v Habs Hv
    | t1 t1' t2 Hstep IH Hlc2
    | v1 t2 t2' Hv1 Hstep IH
    | t t' Hstep IH
    | n n' b s Hstep IH Hlc_b Hlc_s
    | n b b' s Hnv Hstep IH Hlc_s
    | n b s s' Hnv Hv Hstep IH
    | b s Hv Hb
    | n b s Hnv Hv Hs
    | t1 t2 Hlc1 Hlc2
    | t1 t2 Hlc1 Hlc2];
    intros Hlc; unfold locally_closed in *.
  - apply lc_open.
    + inversion Hlc; subst. inversion Habs; assumption.
    + exact (value_lc _ Hv).
  - apply lc_app.
    + apply IH. inversion Hlc; assumption.
    + inversion Hlc; assumption.
  - apply lc_app.
    + inversion Hlc; assumption.
    + apply IH. inversion Hlc; assumption.
  - apply lc_succ. apply IH. inversion Hlc; assumption.
  - apply lc_rec.
    + apply IH. inversion Hlc; assumption.
    + inversion Hlc; assumption.
    + inversion Hlc; assumption.
  - apply lc_rec.
    + exact (numeric_lc _ Hnv).
    + apply IH. inversion Hlc; assumption.
    + inversion Hlc; assumption.
  - apply lc_rec.
    + exact (numeric_lc _ Hnv).
    + exact (value_lc _ Hv).
    + apply IH. inversion Hlc; assumption.
  - exact (value_lc _ Hv).
  - apply lc_app.
    + apply lc_app.
      * exact (proj2 (proj2 (lc_rec_parts _ _ _ Hlc))).
      * exact (lc_succ_part _ (proj1 (lc_rec_parts _ _ _ Hlc))).
    + apply lc_rec.
      exact (lc_succ_part _ (proj1 (lc_rec_parts _ _ _ Hlc))).
      exact (value_lc _ Hv).
      exact (value_lc _ Hs).
  - exact Hlc1.
  - exact Hlc2.
Qed.

Lemma sn_of_step : forall t,
    (forall t', t --> t' -> strongly_normalizing t') ->
    strongly_normalizing t.
Proof. exact SN_intro. Qed.

Lemma sn_multi : forall t u, strongly_normalizing t -> t -->* u ->
    strongly_normalizing u.
Proof.
  intros t u HSN Hmulti. revert HSN.
  induction Hmulti as [x | x y z Hxy Hyz IH]; intros HSN.
  - exact HSN.
  - apply IH. inversion HSN; eauto.
Qed.

Lemma sn_lc_step : forall t t', strongly_normalizing t -> t --> t' ->
    strongly_normalizing t'.
Proof. intros; eauto using sn_multi, multi_step, multi_refl. Qed.

Lemma expression_step : forall T t t',
    strong_expression_relation T t -> t --> t' ->
    strong_expression_relation T t'.
Proof.
  intros T t t' [Hlc [Hsn Hfin]] Hstep.
  split.
  - eapply lc_step; eauto.
  - split.
    + eapply sn_lc_step; eauto.
    + intros v Hmulti Hv.
      eapply Hfin; eauto using multi_step.
Qed.

Lemma expression_multi : forall T t u,
    strong_expression_relation T t -> t -->* u ->
    strong_expression_relation T u.
Proof.
  intros T t u H. induction 1 as [t|t u v Hstep Hmulti IH].
  - exact H.
  - exact (IH (expression_step _ _ _ H Hstep)).
Qed.

Lemma app_sn_aux : forall T1 T2 f a,
    locally_closed f -> strongly_normalizing f ->
    (forall v, f -->* v -> value v ->
       strong_value_relation (Ty_Arrow T1 T2) v) ->
    locally_closed a -> strongly_normalizing a ->
    (forall v, a -->* v -> value v -> strong_value_relation T1 v) ->
    strongly_normalizing (tm_app f a).
Proof.
  intros T1 T2 f a Hlf Hsf Hff Hla Hsa Hfa.
  revert a Hla Hsa Hfa.
  induction Hsf as [f Hf IHf]; intros a Hla Hsa Hfa.
  induction Hsa as [a Ha IHa].
  apply SN_intro. intros r Hr. inversion Hr; subst.
  - destruct (Hff (tm_abs T t)
                (@multi_refl tm step (tm_abs T t)) (v_abs _ _ H1))
      as [Hv [body [Heq Hbody]]].
    inversion Heq; subst.
    destruct (Hbody a
      (Hfa a (@multi_refl tm step a) H3)) as [Hlc [Hsn Hfin]].
    exact Hsn.
  - apply IHf.
    + exact H1.
    + eapply lc_step; [exact Hlf | exact H1].
    + intros v Hmulti Hv. eapply Hff; eauto using multi_step.
    + exact Hla.
    + apply SN_intro; exact Ha.
    + exact Hfa.
  - apply IHa.
    + exact H3.
    + eapply lc_step; [exact Hla | exact H3].
    + intros v Hmulti Hv. eapply Hfa; eauto using multi_step.
Qed.

Lemma app_final_aux : forall T1 T2 f a v,
    strong_expression_relation (Ty_Arrow T1 T2) f ->
    strong_expression_relation T1 a ->
    tm_app f a -->* v -> value v ->
    strong_value_relation T2 v.
Proof.
  intros T1 T2 f a v Ef Ea Hmulti Hv.
  remember (tm_app f a) as q eqn:Eq in Hmulti.
  revert f a Ef Ea Eq.
  induction Hmulti as [q|q r s Hqr Hrs IH];
    intros f a Ef Ea Eq.
  - inversion Eq; subst. now inversion Hv.
  - inversion Eq; subst. inversion Hqr; subst.
    + destruct Ef as [Hlf [Hsf Hff]].
      destruct (Hff _ (@multi_refl tm step _) (v_abs _ _ H2))
        as [Hval [body [Heq Hbody]]].
      inversion Heq; subst.
      destruct (Hbody a
        (proj2 (proj2 Ea) a (@multi_refl tm step a) H4))
        as [Hlc [Hsn Hfin]].
      eapply Hfin; eauto.
    + eapply IH.
      * exact Hv.
      * eapply expression_step; eauto.
      * exact Ea.
      * reflexivity.
    + eapply IH.
      * exact Hv.
      * exact Ef.
      * eapply expression_step; eauto.
      * reflexivity.
Qed.

Lemma app_expression : forall T1 T2 f a,
    strong_expression_relation (Ty_Arrow T1 T2) f ->
    strong_expression_relation T1 a ->
    strong_expression_relation T2 (tm_app f a).
Proof.
  intros T1 T2 f a Ef Ea.
  destruct Ef as [Hlf [Hsf Hff]].
  destruct Ea as [Hla [Hsa Hfa]].
  split.
  - constructor; assumption.
  - split.
    + eapply app_sn_aux.
      * exact Hlf.
      * exact Hsf.
      * exact Hff.
      * exact Hla.
      * exact Hsa.
      * exact Hfa.
    + intros v Hmulti Hv.
      eapply app_final_aux.
      * split; [exact Hlf | split; [exact Hsf | exact Hff]].
      * split; [exact Hla | split; [exact Hsa | exact Hfa]].
      * exact Hmulti.
      * exact Hv.
Qed.

Lemma succ_sn : forall t, strongly_normalizing t ->
    strongly_normalizing (tm_succ t).
Proof.
  intros t H. induction H as [t Hstep IH].
  apply SN_intro. intros t' Ht'. inversion Ht'; subst; eauto.
Qed.

Lemma succ_multi_inv : forall t v,
    tm_succ t -->* v ->
    exists u, t -->* u /\ v = tm_succ u.
Proof.
  intros t v H. remember (tm_succ t) as q eqn:Eq in H.
  revert t Eq.
  induction H as [q|q r s Hqr Hrs IH]; intros t Eq.
  - inversion Eq; subst. exists t. split.
    + exact (@multi_refl tm step t).
    + reflexivity.
  - inversion Eq; subst. inversion Hqr; subst.
    destruct (IH _ eq_refl) as [u [Hu Heq]].
    exists u. split; eauto using multi_step.
Qed.

Lemma succ_expression : forall t,
    strong_expression_relation Ty_Nat t ->
    strong_expression_relation Ty_Nat (tm_succ t).
Proof.
  intros t [Hlc [Hsn Hfin]].
  split.
  - constructor; exact Hlc.
  - split.
    + apply succ_sn; exact Hsn.
    + intros v Hmulti Hv.
      destruct (succ_multi_inv _ _ Hmulti) as [u [Hu Heq]].
      subst v.
      assert (Hvu : value u).
      { inversion Hv as [T0 t0 Hlc0 | | | n0 Hnum].
        inversion Hnum as [|u0 Hnum0].
        constructor; exact Hnum0. }
      destruct (Hfin u Hu Hvu) as [Hval Hnum].
      split.
      * constructor. constructor. exact Hnum.
      * constructor. exact Hnum.
Qed.

Lemma choice_expression : forall T t1 t2,
    strong_expression_relation T t1 ->
    strong_expression_relation T t2 ->
    strong_expression_relation T (tm_choice t1 t2).
Proof.
  intros T t1 t2 E1 E2.
  destruct E1 as [Hlc1 [Hsn1 Hfin1]].
  destruct E2 as [Hlc2 [Hsn2 Hfin2]].
  split.
  - constructor; assumption.
  - split.
    + apply SN_intro. intros r Hr. inversion Hr; subst.
      * exact Hsn1.
      * exact Hsn2.
    + intros v Hmulti Hv.
      remember (tm_choice t1 t2) as q eqn:Eq in Hmulti.
      revert t1 t2 Hlc1 Hsn1 Hfin1 Hlc2 Hsn2 Hfin2 Eq.
      induction Hmulti as [q|q r s Hqr Hrs IH];
        intros t1 t2 Hlc1 Hsn1 Hfin1 Hlc2 Hsn2 Hfin2 Eq.
      * inversion Eq; subst. now inversion Hv.
      * inversion Eq; subst. inversion Hqr; subst.
        -- eapply Hfin1; eauto.
        -- eapply Hfin2; eauto.
Qed.

Lemma numeric_no_step : forall n, numeric_value n ->
    forall n', ~ n --> n'.
Proof.
  intros n H. induction H as [|n Hn IH]; intros n' Hs.
  - inversion Hs.
  - inversion Hs; eapply IH; eauto.
Qed.

Lemma numeric_expression : forall n,
    numeric_value n -> strong_expression_relation Ty_Nat n.
Proof.
  intros n Hn.
  split.
  - apply numeric_lc; exact Hn.
  - split.
    + induction Hn as [|n Hn IH].
      * apply SN_intro. intros; inversion H.
      * apply succ_sn; exact IH.
    + intros v Hmulti Hv.
      remember n as q eqn:Eq in Hmulti.
      revert n Hn Eq.
      induction Hmulti as [q|q r s Hqr Hrs IH];
        intros n Hn Eq.
      * inversion Eq; subst. split; [exact Hv | exact Hn].
      * exfalso. inversion Eq; subst.
        eapply numeric_no_step; eauto.
Qed.

Lemma rec_zero_sn : forall b s,
    locally_closed b -> strongly_normalizing b ->
    locally_closed s -> strongly_normalizing s ->
    strongly_normalizing (tm_natrec tm_zero b s).
Proof.
  intros T b s Lb Sb Ls Ss.
  revert Lb.
  induction Sb as [b Hb IHb]; intros Lb.
  revert Ls.
  induction Ss as [s Hs IHs]; intros Ls.
  apply SN_intro. intros r Hr. inversion Hr; subst.
  - exact (IHb (lc_step _ _ Lb H1)).
  - exact (IHs Ls).
  - exact (SN_intro _ Hb).
Qed.

Lemma rec_numeric_expression : forall T n b s,
    numeric_value n ->
    strong_expression_relation T b ->
    strong_expression_relation
      (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
    strong_expression_relation T (tm_natrec n b s).
Proof.
  intros T n b s Hn.
  induction Hn as [|n Hn IHn]; intros Eb Es.
  - destruct Eb as [Lb [Sb Fb]].
    destruct Es as [Ls [Ss Fs]].
    destruct (numeric_expression tm_zero nv_zero)
      as [Ln [Sn Fn]].
    split.
    + constructor; assumption.
    + split.
      * eapply rec_zero_sn; eauto.
      * intros v Hmulti Hv.
        remember (tm_natrec tm_zero b s) as q eqn:Eq in Hmulti.
        revert b s Lb Sb Fb Ls Ss Fs Eq.
        induction Hmulti as [q|q r z Hqr Hrz IH];
          intros b s Lb Sb Fb Ls Ss Fs Eq.
        -- inversion Eq; subst. inversion Hv.
        -- inversion Eq; subst. inversion Hqr; subst.
           ++ eapply IH; eauto.
           ++ eapply IH; eauto.
           ++ eapply Fb; eauto.
  - intros Eb Es.
    destruct (IHn Eb Es) as [Hrec_lc [Hrec_sn Hrec_fin]].
    destruct (numeric_expression (tm_succ n) (nv_succ n Hn))
      as [Ln [Sn Fn]].
    destruct Eb as [Lb [Sb Fb]].
    destruct Es as [Ls [Ss Fs]].
    split.
    + constructor; assumption.
    + split.
      * eapply rec_sn_components; eauto.
      * intros v Hmulti Hv.
        remember (tm_natrec (tm_succ n) b s) as q eqn:Eq in Hmulti.
        revert b s Lb Sb Fb Ls Ss Fs Eq.
        induction Hmulti as [q|q r z Hqr Hrz IH];
          intros b s Lb Sb Fb Ls Ss Fs Eq.
        -- inversion Eq; subst. inversion Hv.
        -- inversion Eq; subst. inversion Hqr; subst.
           ++ eapply IH; eauto.
           ++ eapply IH; eauto.
           ++ destruct (numeric_expression n Hn)
                as [Hnlc [Hns Hnf]].
              destruct (app_expression
                (T1 := Ty_Nat) (T2 := Ty_Arrow T T) s n
                (conj Ls (conj (SN_intro _ Hs) Fs))
                (conj Hnlc (conj Hns Hnf))) as [Hsnlc [Hsn [Hsnf]]].
              eapply app_final_aux.
              * exact (conj Hsnlc (conj Hsn Hsnf)).
              * exact (conj Hrec_lc (conj Hrec_sn Hrec_fin)).
              * exact Hrz.
              * exact Hv.
Qed.

Lemma rec_final_aux : forall T n b s v,
    strong_expression_relation Ty_Nat n ->
    strong_expression_relation T b ->
    strong_expression_relation
      (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
    tm_natrec n b s -->* v -> value v ->
    strong_value_relation T v.
Proof.
  intros T n b s v En Eb Es Hmulti Hv.
  remember (tm_natrec n b s) as q eqn:Eq in Hmulti.
  revert n b s En Eb Es Eq.
  induction Hmulti as [q|q r z Hqr Hrz IH];
    intros n b s En Eb Es Eq.
  - inversion Eq; subst. inversion Hv.
  - inversion Eq; subst. inversion Hqr; subst.
    + eapply IH.
      * exact Hv.
      * eapply expression_step; eauto.
      * exact Eb.
      * exact Es.
      * reflexivity.
    + eapply IH.
      * exact Hv.
      * exact En.
      * eapply expression_step; eauto.
      * exact Es.
      * reflexivity.
    + eapply IH.
      * exact Hv.
      * exact En.
      * exact Eb.
      * eapply expression_step; eauto.
      * reflexivity.
    + eapply (proj2 (proj2 Eb)).
      eauto.
    + destruct (rec_numeric_expression T _ b s H0 Eb Es)
        as [Hrlc [Hrsn Hrf]].
      destruct (numeric_expression _ H0)
        as [Hnlc [Hnsn Hnfin]].
      destruct (app_expression
        (T1 := Ty_Nat) (T2 := Ty_Arrow T T) s _ Es
        (conj Hnlc (conj Hnsn Hnfin))) as [Hsnlc [Hsnsn Hsnfin]].
      eapply app_final_aux.
      * exact (conj Hsnlc (conj Hsnsn Hsnfin)).
      * exact (conj Hrlc (conj Hrsn Hrf)).
      * exact Hrz.
      * exact Hv.
Qed.

Lemma rec_expression : forall T n b s,
    strong_expression_relation Ty_Nat n ->
    strong_expression_relation T b ->
    strong_expression_relation
      (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
    strong_expression_relation T (tm_natrec n b s).
Proof.
  intros T n b s En Eb Es.
  destruct En as [Ln [Sn Fn]].
  destruct Eb as [Lb [Sb Fb]].
  destruct Es as [Ls [Ss Fs]].
  split.
  - apply lc_rec; assumption.
  - split.
    + eapply rec_sn_components; eauto.
    + intros v Hmulti Hv.
      eapply rec_final_aux; eauto.
Qed.

Fixpoint fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_app t1 t2 => fv t1 ++ fv t2
  | tm_abs _ t1 => fv t1
  | tm_true | tm_false | tm_zero => []
  | tm_succ t1 => fv t1
  | tm_natrec n b s => fv n ++ fv b ++ fv s
  | tm_choice t1 t2 => fv t1 ++ fv t2
  end.

Fixpoint fresh (l : list atom) : atom :=
  match l with
  | [] => 0
  | x :: xs => S (Nat.max x (fresh xs))
  end.

Lemma fresh_not_in : forall l, ~ In (fresh l) l.
Proof.
  induction l as [|x xs IH]; simpl.
  - tauto.
  - intro H. destruct H as [H|H].
    + subst. lia.
    + apply IH. eapply Nat.lt_irrefl.
      eapply Nat.lt_le_trans; [exact (Nat.lt_succ_self (fresh xs))|].
      apply Nat.le_max_r.
Qed.

Lemma lc_weaken_n : forall k n t, lc_at k t -> lc_at (k+n) t.
Proof.
  intros k n t H. induction n; simpl; auto using lc_weaken.
Qed.

Lemma lc_open_rec_inv : forall k t u,
    lc_at k (open_rec k u t) -> lc_at (S k) t.
Proof.
  intros k t u. revert k u.
  induction t; intros k u H; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + constructor; apply Nat.eqb_eq in E; lia.
    + inversion H; constructor; apply Nat.eqb_neq in E; lia.
  - constructor.
  - inversion H; constructor; eauto.
  - inversion H; constructor. eauto.
  - constructor.
  - constructor.
  - constructor.
  - inversion H; constructor; eauto.
  - inversion H; constructor; eauto.
  - inversion H; constructor; eauto.
Qed.

Lemma msubst_lc : forall k t rho,
    (forall x, locally_closed (rho x)) ->
    lc_at k t -> lc_at k (msubst rho t).
Proof.
  intros k t rho Hr H. induction H; simpl; eauto.
  - apply lc_weaken_n with (n := k). apply Hr.
  - constructor. apply IHlc_at.
    exact Hr.
Qed.

Lemma msubst_open_rec : forall rho k u t,
    msubst rho (open_rec k u t) =
    open_rec k (msubst rho u) (msubst rho t).
Proof.
  intros rho k u t. revert k u.
  induction t; intros k u; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2, IHt3. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma msubst_open_update : forall rho x v t,
    ~ In x (fv t) ->
    msubst (subst_update rho x v) (open t (tm_fvar x)) =
    open (msubst rho t) v.
Proof.
  intros rho x v t. unfold open. revert x v.
  induction t; intros x v Hfresh; simpl in *.
  - destruct (Nat.eqb 0 n) eqn:E.
    + reflexivity.
    + reflexivity.
  - simpl in Hfresh. destruct Hfresh as [H|H]; [contradiction|].
    unfold subst_update. rewrite Nat.eqb_neq by lia. reflexivity.
  - rewrite IHt1, IHt2; simpl in *; intuition.
  - rewrite IHt; simpl in *; intuition.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHt; simpl in *; intuition.
  - rewrite IHt1, IHt2, IHt3; simpl in *; intuition.
  - rewrite IHt1, IHt2; simpl in *; intuition.
Qed.

Lemma typing_lc : forall Gamma t T,
    <{ Gamma |-- t \in T }> -> locally_closed t.
Proof.
  intros Gamma t T H. induction H.
  - constructor.
  - apply lc_abs. apply lc_open_rec_inv with (u := tm_fvar x).
    apply IHhas_type.
  - constructor; assumption.
  - constructor; assumption.
  - constructor.
  - constructor.
  - constructor.
  - constructor. assumption.
  - constructor; assumption.
  - constructor; assumption.
Qed.

Lemma msubst_lc_fv : forall k t rho,
    lc_at k t ->
    (forall x, In x (fv t) -> locally_closed (rho x)) ->
    lc_at k (msubst rho t).
Proof.
  intros k t rho H. induction H; intros Hfv; simpl in *.
  - constructor.
  - constructor.
    apply Hfv x. simpl. auto.
  - constructor.
    + apply IHlc_at1. intros x Hx. apply Hfv x. apply in_or_app. left; exact Hx.
    + apply IHlc_at2. intros x Hx. apply Hfv x. apply in_or_app. right; exact Hx.
  - constructor. apply IHlc_at. exact Hfv.
  - constructor.
  - constructor.
  - constructor.
  - constructor. apply IHlc_at. exact Hfv.
  - constructor.
    + apply IHlc_at1. intros x Hx. apply Hfv x. apply in_or_app. left; apply in_or_app; left; exact Hx.
    + apply IHlc_at2. intros x Hx. apply Hfv x. apply in_or_app. left; apply in_or_app; right; exact Hx.
    + apply IHlc_at3. intros x Hx. apply Hfv x. apply in_or_app. right; exact Hx.
  - constructor.
    + apply IHlc_at1. intros x Hx. apply Hfv x. apply in_or_app; left; exact Hx.
    + apply IHlc_at2. intros x Hx. apply Hfv x. apply in_or_app; right; exact Hx.
Qed.

Lemma fv_open_preserve : forall t u x,
    In x (fv t) -> In x (fv (open t u)).
Proof.
  intros t u x H. unfold open. revert u x.
  induction t; intros u x Hx; simpl in *; try contradiction.
  - exact Hx.
  - apply in_or_app in Hx. apply in_or_app.
    destruct Hx as [H|H]; [left; eauto|right; eauto].
  - apply IHt; exact Hx.
  - apply in_or_app in Hx. apply in_or_app.
    destruct Hx as [H|H]; [left; apply in_or_app; left; eauto|
      left; apply in_or_app; right; eauto].
  - apply in_or_app in Hx. apply in_or_app.
    destruct Hx as [H|H]; [left; eauto|right; eauto].
Qed.

Lemma typing_fv : forall Gamma t T,
    <{ Gamma |-- t \in T }> ->
    forall x, In x (fv t) -> exists U, Gamma x = Some U.
Proof.
  intros Gamma t T H. induction H; intros y Hy.
  - simpl in Hy. destruct Hy as [Hy|Hy]; [subst; eexists; exact H|contradiction].
  - destruct (fresh_not_in (x :: L)) as Hfresh.
    specialize (H0 (fresh (x :: L)) Hfresh).
    destruct (IHhas_type (fresh (x :: L)) H0 y
      (fv_open_preserve _ _ _ Hy)) as [U HU].
    unfold update in HU. destruct (Nat.eqb (fresh (x :: L)) y) eqn:E.
    + apply Nat.eqb_eq in E. subst y. exfalso. apply Hfresh. simpl; auto.
    + exists U. exact HU.
  - simpl in Hy. apply in_app_or in Hy. destruct Hy as [Hy|Hy].
    + eauto.
    + eauto.
  - simpl in Hy. eauto.
  - simpl in Hy. contradiction.
  - simpl in Hy. contradiction.
  - simpl in Hy. contradiction.
  - simpl in Hy. eauto.
  - simpl in Hy. apply in_app_or in Hy. destruct Hy as [Hy|Hy].
    + apply in_app_or in Hy. destruct Hy as [Hy|Hy]; eauto.
    + eauto.
  - simpl in Hy. apply in_app_or in Hy. destruct Hy as [Hy|Hy]; eauto.
Qed.

Lemma related_update : forall Gamma rho x T v,
    strong_related_substitution Gamma rho ->
    strong_value_relation T v ->
    strong_related_substitution (update Gamma x T)
      (subst_update rho x v).
Proof.
  intros Gamma rho x T v Hr Hv y U Hlookup.
  unfold update in Hlookup. unfold subst_update.
  destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. subst y. exact Hv.
  - apply Hr. exact Hlookup.

Lemma value_no_step : forall v, value v -> forall v', ~ v --> v'.
Proof.
  intros v Hv. inversion Hv; subst.
  - intros v' H. inversion H.
  - intros v' H. inversion H.
  - intros v' H. inversion H.
  - induction H0; intros v' Hs.
    + inversion Hs.
    + inversion Hs; eauto.
Qed.

Lemma value_expression : forall T v,
    strong_value_relation T v -> strong_expression_relation T v.
Proof.
  intros T v [Hv HT].
  split.
  - apply value_lc; exact Hv.
  - split.
    + apply SN_intro. intros v' Hs. exfalso.
      eapply value_no_step; eauto.
    + intros w Hmulti Hw.
      remember v as q eqn:Eq in Hmulti.
      revert v Hv HT Eq.
      induction Hmulti as [q|q r s Hqr Hrs IH];
        intros v Hv HT Eq.
      * inversion Eq; subst. split; assumption.
      * exfalso. inversion Eq; subst.
        eapply value_no_step; eauto.
Qed.

Lemma true_expression : strong_expression_relation Ty_Bool tm_true.
Proof. apply value_expression. split; [constructor|left; reflexivity]. Qed.

Lemma false_expression : strong_expression_relation Ty_Bool tm_false.
Proof. apply value_expression. split; [constructor|right; reflexivity]. Qed.

Lemma zero_expression : strong_expression_relation Ty_Nat tm_zero.
Proof. apply value_expression. split; [constructor; constructor|constructor]. Qed.

Lemma fundamental : forall Gamma t T rho,
    <{ Gamma |-- t \in T }> ->
    strong_related_substitution Gamma rho ->
    strong_expression_relation T (msubst rho t).
Proof.
  intros Gamma t T rho H. induction H; intros Hr.
  - eapply value_expression. eapply Hr; eauto.
  - destruct (fresh_not_in (L ++ fv t1)) as Hfresh.
    assert (HfreshL : ~ In (fresh (L ++ fv t1)) L).
    { intro Hx. apply Hfresh. apply in_or_app; left; exact Hx. }
    assert (Hfreshfv : ~ In (fresh (L ++ fv t1)) (fv t1)).
    { intro Hx. apply Hfresh. apply in_or_app; right; exact Hx. }
    specialize (H0 (fresh (L ++ fv t1)) HfreshL).
    assert (Hbodylc : lc_at 1 t1).
    { apply lc_open_rec_inv with (u := tm_fvar (fresh (L ++ fv t1))).
      apply typing_lc; exact H0. }
    assert (Hrho_fv : forall y, In y (fv t1) ->
      locally_closed (rho y)).
    { intros y Hy. destruct (typing_fv _ _ _ H0 y (fv_open_preserve _ _ _ Hy))
        as [U HU].
      unfold update in HU.
      destruct (Nat.eqb (fresh (L ++ fv t1)) y) eqn:E.
      - apply Nat.eqb_eq in E. subst y. contradiction.
      - apply value_lc.
        eapply Hr; eauto. }
    assert (Hbodylc' : lc_at 1 (msubst rho t1)).
    { eapply msubst_lc_fv; eauto. }
    apply value_expression.
    split.
    + constructor. exact Hbodylc'.
    + exists (msubst rho t1). split; [reflexivity|].
      intros arg Harg.
      destruct (IHhas_type (fresh (L ++ fv t1)) HfreshL
        (related_update Gamma rho (fresh (L ++ fv t1)) T1 arg Hr Harg))
        as [Hlc [Hsn Hfin]].
      rewrite (msubst_open_update rho (fresh (L ++ fv t1)) arg t1 Hfreshfv)
        in Hlc, Hsn, Hfin.
      repeat split; assumption.
  - apply app_expression; [eapply IHhas_type1; exact Hr|eapply IHhas_type2; exact Hr].
  - apply true_expression.
  - apply false_expression.
  - apply zero_expression.
  - apply succ_expression. eapply IHhas_type; exact Hr.
  - apply rec_expression.
    + eapply IHhas_type1; exact Hr.
    + eapply IHhas_type2; exact Hr.
    + eapply IHhas_type3; exact Hr.
  - apply choice_expression.
    + eapply IHhas_type1; exact Hr.
    + eapply IHhas_type2; exact Hr.
Qed.

Lemma msubst_id : forall t, msubst id_substitution t = t.
Proof.
  induction t; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2, IHt3. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Ht.
  pose proof (fundamental empty t T id_substitution Ht) as Hexp.
  exact (proj1 (proj2 Hexp)).
Qed.

End STLCNormalizationNondeterminismRecursionMediumTask.
