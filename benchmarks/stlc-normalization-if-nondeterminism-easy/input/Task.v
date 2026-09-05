(** STLC CBV strong-normalization benchmark, Easy variant.
    Features: if-nondeterminism. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Relations.Relation_Definitions Lia.
Import ListNotations.

Module STLCNormalizationIfNondeterminismEasyTask.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
      R x y ->
      multi R y z ->
      multi R x z.

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

  | tm_if : tm -> tm -> tm -> tm
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

Notation "'if' t1 'then' t2 'else' t3" := (tm_if t1 t2 t3)
  (in custom stlc_tm at level 200,
   t1 custom stlc_tm, t2 custom stlc_tm, t3 custom stlc_tm at level 200) : stlc_scope.
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
  | tm_if t1 t2 t3 => tm_if (open_rec k u t1) (open_rec k u t2) (open_rec k u t3)
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
    | lc_if : forall k t1 t2 t3,
      lc_at k t1 -> lc_at k t2 -> lc_at k t3 -> lc_at k (tm_if t1 t2 t3)
  | lc_choice : forall k t1 t2,
      lc_at k t1 -> lc_at k t2 -> lc_at k (tm_choice t1 t2).

Definition locally_closed (t : tm) : Prop := lc_at 0 t.

Hint Constructors lc_at : core.

Inductive value : tm -> Prop :=
  | v_abs : forall T t,
      locally_closed (tm_abs T t) ->
      value (tm_abs T t)
  | v_true :
      value tm_true
  | v_false :
      value tm_false.

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
  | T_If : forall Gamma t1 t2 t3 T,
      <{ Gamma |-- $(t1) \in Bool }> ->
      <{ Gamma |-- $(t2) \in T }> ->
      <{ Gamma |-- $(t3) \in T }> ->
      <{ Gamma |-- $(tm_if t1 t2 t3) \in T }>
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
  | tm_if t1 t2 t3 => tm_if (msubst rho t1) (msubst rho t2) (msubst rho t3)
  | tm_choice t1 t2 => tm_choice (msubst rho t1) (msubst rho t2)
  end.

Definition proper_substitution (rho : term_substitution) : Prop :=
  forall x, locally_closed (rho x).

Fixpoint strong_value_relation (T : ty) (v : tm) : Prop :=
  value v /\
  match T with
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

Fixpoint free_vars (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_app t1 t2 => free_vars t1 ++ free_vars t2
  | tm_abs _ t1 => free_vars t1
  | tm_true => []
  | tm_false => []
  | tm_if t1 t2 t3 => free_vars t1 ++ free_vars t2 ++ free_vars t3
  | tm_choice t1 t2 => free_vars t1 ++ free_vars t2
  end.

Lemma update_eq : forall Gamma x T,
  update Gamma x T x = Some T.
Proof.
  intros. unfold update. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma update_neq : forall Gamma x y T,
  x <> y ->
  update Gamma x T y = Gamma y.
Proof.
  intros. unfold update.
  destruct (Nat.eqb x y) eqn:Heq.
  - apply Nat.eqb_eq in Heq. contradiction.
  - reflexivity.
Qed.

Fixpoint max_atom (L : list atom) : atom :=
  match L with
  | [] => 0
  | x :: L' => Nat.max x (max_atom L')
  end.

Definition fresh (L : list atom) : atom := S (max_atom L).

Lemma in_le_max_atom : forall x L,
  In x L -> x <= max_atom L.
Proof.
  induction L; simpl; intros.
  - contradiction.
  - destruct H as [H | H].
    + subst. lia.
    + specialize (IHL H). lia.
Qed.

Lemma fresh_notin : forall L,
  ~ In (fresh L) L.
Proof.
  unfold fresh. intros L H.
  pose proof (in_le_max_atom _ _ H). lia.
Qed.

Lemma lc_at_weaken : forall k j t,
  lc_at k t ->
  k <= j ->
  lc_at j t.
Proof.
  intros k j t H.
  generalize dependent j.
  induction H; intros j Hle; eauto using lc_at.
  - apply lc_bvar. lia.
  - apply lc_abs. apply IHlc_at. lia.
Qed.

Lemma term_lc_at : forall k t,
  locally_closed t ->
  lc_at k t.
Proof.
  unfold locally_closed. intros. eapply lc_at_weaken; eauto. lia.
Qed.

Lemma value_regular : forall v,
  value v -> locally_closed v.
Proof.
  intros v H. destruct H.
  - assumption.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma open_rec_preserves_lc_at : forall t k u,
  lc_at (S k) t ->
  locally_closed u ->
  lc_at k (open_rec k u t).
Proof.
  induction t; intros k u Hlc Hu; simpl in *; inversion Hlc; subst; eauto using lc_at.
  - destruct (Nat.eqb k n) eqn:Heq.
    + apply term_lc_at. exact Hu.
    + apply Nat.eqb_neq in Heq. apply lc_bvar. lia.
Qed.

Lemma open_preserves_term : forall t u,
  lc_at 1 t ->
  locally_closed u ->
  locally_closed (open t u).
Proof.
  unfold open, locally_closed. intros.
  apply open_rec_preserves_lc_at; assumption.
Qed.

Lemma lc_at_open_inv : forall t k u,
  lc_at k (open_rec k u t) ->
  lc_at (S k) t.
Proof.
  induction t; intros k u Hlc; simpl in *.
  - destruct (Nat.eqb k n) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst. apply lc_bvar. lia.
    + inversion Hlc; subst. apply lc_bvar. lia.
  - apply lc_fvar.
  - inversion Hlc; subst. eauto using lc_at.
  - inversion Hlc; subst. apply lc_abs. apply (IHt (S k) u). assumption.
  - apply lc_true.
  - apply lc_false.
  - inversion Hlc; subst. eauto using lc_at.
  - inversion Hlc; subst. eauto using lc_at.
Qed.

Lemma typing_regular : forall Gamma t T,
  <{ Gamma |-- t \in T }> ->
  locally_closed t.
Proof.
  intros Gamma t T Ht.
  induction Ht.
  - unfold locally_closed. apply lc_fvar.
  - unfold locally_closed. apply lc_abs.
    pose (x := fresh L).
    assert (Hfresh : ~ In x L) by (unfold x; apply fresh_notin).
    specialize (H0 x Hfresh).
    apply lc_at_open_inv with (u := tm_fvar x).
    exact H0.
  - unfold locally_closed. apply lc_app; assumption.
  - unfold locally_closed. apply lc_true.
  - unfold locally_closed. apply lc_false.
  - apply lc_if; assumption.
  - apply lc_choice; assumption.
Qed.

Lemma value_no_step : forall v,
  value v -> forall t, ~ (v --> t).
Proof.
  intros v Hv t Hs. destruct Hv; inversion Hs.
Qed.

Lemma open_rec_lc_at : forall k t j u,
  lc_at k t ->
  k <= j ->
  open_rec j u t = t.
Proof.
  intros k t j u Hlc.
  generalize dependent j.
  induction Hlc; intros j Hle; simpl.
  - destruct (Nat.eqb j i) eqn:Heq.
    + apply Nat.eqb_eq in Heq. lia.
    + reflexivity.
  - reflexivity.
  - rewrite IHHlc1 by assumption.
    rewrite IHHlc2 by assumption.
    reflexivity.
  - rewrite IHHlc by lia. reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHHlc1, IHHlc2, IHHlc3 by assumption. reflexivity.
  - rewrite IHHlc1, IHHlc2 by assumption. reflexivity.
Qed.

Lemma open_rec_term : forall t j u,
  locally_closed t ->
  open_rec j u t = t.
Proof.
  unfold locally_closed. intros.
  eapply open_rec_lc_at; eauto. lia.
Qed.

Lemma msubst_preserves_lc_at : forall rho k t,
  proper_substitution rho ->
  lc_at k t ->
  lc_at k (msubst rho t).
Proof.
  intros rho k t Hproper Hlc.
  induction Hlc; simpl; eauto using lc_at.
  - apply term_lc_at. apply Hproper.
Qed.

Lemma msubst_preserves_term : forall rho t,
  proper_substitution rho ->
  locally_closed t ->
  locally_closed (msubst rho t).
Proof.
  unfold locally_closed. intros.
  eapply msubst_preserves_lc_at; eauto.
Qed.

Lemma proper_update : forall rho x v,
  proper_substitution rho ->
  locally_closed v ->
  proper_substitution (subst_update rho x v).
Proof.
  unfold proper_substitution, subst_update.
  intros rho x v Hproper Hv y.
  destruct (Nat.eqb x y); auto.
Qed.

Lemma notin_app_split : forall (x : atom) L1 L2,
  ~ In x (L1 ++ L2) ->
  ~ In x L1 /\ ~ In x L2.
Proof.
  intros x L1 L2 H.
  split; intro Hin; apply H; apply in_app_iff; auto.
Qed.

Lemma msubst_open_update_rec : forall t rho x v k,
  ~ In x (free_vars t) ->
  proper_substitution rho ->
  locally_closed v ->
  msubst (subst_update rho x v) (open_rec k (tm_fvar x) t) =
  open_rec k v (msubst rho t).
Proof.
  induction t; intros rho x v k Hfresh Hproper Hv; simpl in *.
  - destruct (Nat.eqb k n) eqn:Heq.
    + unfold subst_update. simpl.
      destruct (Nat.eqb x x) eqn:Hxx.
      * reflexivity.
      * apply Nat.eqb_neq in Hxx. contradiction.
    + reflexivity.
  - destruct (Nat.eqb x a) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst a. contradiction Hfresh. simpl. auto.
    + unfold subst_update. rewrite Heq.
      symmetry. apply open_rec_term. apply Hproper.
  - apply notin_app_split in Hfresh as [Hfresh1 Hfresh2].
    rewrite IHt1 by assumption.
    rewrite IHt2 by assumption.
    reflexivity.
  - rewrite IHt by assumption. reflexivity.
  - reflexivity.
  - reflexivity.
  - apply notin_app_split in Hfresh as [Hfresh1 Hfresh23].
    apply notin_app_split in Hfresh23 as [Hfresh2 Hfresh3].
    rewrite IHt1, IHt2, IHt3 by assumption. reflexivity.
  - apply notin_app_split in Hfresh as [Hfresh1 Hfresh2].
    rewrite IHt1, IHt2 by assumption. reflexivity.
Qed.

Lemma msubst_open_update : forall t rho x v,
  ~ In x (free_vars t) ->
  proper_substitution rho ->
  locally_closed v ->
  msubst (subst_update rho x v) (open t (tm_fvar x)) =
  open (msubst rho t) v.
Proof.
  unfold open. intros.
  apply msubst_open_update_rec; assumption.
Qed.

Lemma msubst_id : forall t,
  msubst id_substitution t = t.
Proof.
  induction t; simpl; try rewrite IHt; try rewrite IHt1; try rewrite IHt2; try rewrite IHt3;
    reflexivity.
Qed.

Lemma id_substitution_proper :
  proper_substitution id_substitution.
Proof.
  unfold proper_substitution, id_substitution, locally_closed.
  intros. apply lc_fvar.
Qed.

Lemma step_preserves_lc : forall t t',
  t --> t' -> locally_closed t -> locally_closed t'.
Proof.
  intros t t' Hstep Hlc.
  unfold locally_closed in *.
  induction Hstep; inversion Hlc; subst; eauto 8 using lc_at, value_regular.
  apply open_preserves_term.
  - unfold locally_closed in H. inversion H. assumption.
  - apply value_regular. exact H0.
Qed.

Lemma sn_step : forall t t',
  strongly_normalizing t ->
  t --> t' ->
  strongly_normalizing t'.
Proof.
  intros t t' Hsn Hstep.
  inversion Hsn as [t0 Hnext].
  apply Hnext. exact Hstep.
Qed.

Lemma value_multi_eq : forall v t,
  value v ->
  v -->* t ->
  t = v.
Proof.
  intros v t Hv Hmulti.
  inversion Hmulti; subst.
  - reflexivity.
  - exfalso. eapply value_no_step; eauto.
Qed.

Lemma value_sn : forall v,
  value v ->
  strongly_normalizing v.
Proof.
  intros v Hv.
  apply SN_intro. intros t Hstep.
  exfalso. eapply value_no_step; eauto.
Qed.

Lemma strong_value_relation_value : forall T v,
  strong_value_relation T v -> value v.
Proof.
  intros T v H. destruct T; simpl in H; tauto.
Qed.

Lemma strong_value_relation_lc : forall T v,
  strong_value_relation T v -> locally_closed v.
Proof.
  intros T v H.
  apply value_regular.
  eapply strong_value_relation_value. exact H.
Qed.

Lemma strong_value_is_expression : forall T v,
  strong_value_relation T v ->
  strong_expression_relation T v.
Proof.
  intros T v Hv.
  split.
  - eapply strong_value_relation_lc. exact Hv.
  - split.
    + apply value_sn. eapply strong_value_relation_value. exact Hv.
    + intros v' Hmulti Hvalue.
      assert (v' = v).
      {
        eapply value_multi_eq.
        - eapply strong_value_relation_value. exact Hv.
        - exact Hmulti.
      }
      subst v'. exact Hv.
Qed.

Lemma strong_expression_step : forall T t t',
  strong_expression_relation T t ->
  t --> t' ->
  strong_expression_relation T t'.
Proof.
  intros T t t' [Hlc [Hsn Hall]] Hstep.
  split.
  - eapply step_preserves_lc; eauto.
  - split.
    + eapply sn_step; eauto.
    + intros v Hmulti Hv.
      apply Hall with (v := v); auto.
      eapply multi_step; eauto.
Qed.

Lemma strong_expression_of_reducts : forall T t,
  locally_closed t ->
  ~ value t ->
  (forall t', t --> t' -> strong_expression_relation T t') ->
  strong_expression_relation T t.
Proof.
  intros T t Hlc Hnotvalue Hnext.
  split. exact Hlc.
  split.
  - apply SN_intro. intros t' Hstep.
    destruct (Hnext t' Hstep) as [_ [Hsn _]]. exact Hsn.
  - intros v Hmulti Hv.
    inversion Hmulti; subst.
    + contradiction.
    + destruct (Hnext y H) as [_ [_ Hall]].
      eapply Hall; eauto.
Qed.

Lemma strong_expression_app : forall T1 T2 t1 t2,
  strong_expression_relation (Ty_Arrow T1 T2) t1 ->
  strong_expression_relation T1 t2 ->
  strong_expression_relation T2 (tm_app t1 t2).
Proof.
  intros T1 T2 t1 t2 HE1 HE2.
  destruct HE1 as [Hlc1 [Hsn1 Hall1]].
  revert T1 T2 Hlc1 Hall1 t2 HE2.
  induction Hsn1 as [t1 Hnext1 IH1].
  intros T1 T2 Hlc1 Hall1 t2 HE2.
  destruct HE2 as [Hlc2 [Hsn2 Hall2]].
  revert Hlc2 Hall2.
  induction Hsn2 as [t2 Hnext2 IH2].
  intros Hlc2 Hall2.
  apply strong_expression_of_reducts.
  - apply lc_app; assumption.
  - intro Hvalue. inversion Hvalue.
  - intros u Hstep.
    inversion Hstep; subst.
    + assert (Hrefl1 : tm_abs T t -->* tm_abs T t) by apply multi_refl.
      assert (Hrefl2 : t2 -->* t2) by apply multi_refl.
      pose proof
        (Hall1 (tm_abs T t) Hrefl1 (v_abs T t H1)) as HVfun.
      pose proof (Hall2 t2 Hrefl2 H3) as HVarg.
      simpl in HVfun.
      destruct HVfun as [_ [body [Heq Hbody]]].
      injection Heq as HeqT Heqbody.
      subst T. subst body.
      exact (Hbody t2 HVarg).
    + apply (IH1 t1' H1 T1 T2).
      * eapply step_preserves_lc; eauto.
      * intros v Hmulti Hv.
        apply Hall1 with (v := v); auto.
        eapply multi_step; eauto.
      * split. exact Hlc2.
        split.
        -- apply SN_intro. exact Hnext2.
        -- exact Hall2.
    + apply (IH2 t2' H3).
      * eapply step_preserves_lc; eauto.
      * intros v Hmulti Hv.
        apply Hall2 with (v := v); auto.
        eapply multi_step; eauto.
Qed.

Lemma strong_expression_choice : forall T t1 t2,
  strong_expression_relation T t1 ->
  strong_expression_relation T t2 ->
  strong_expression_relation T (tm_choice t1 t2).
Proof.
  intros T t1 t2 HE1 HE2.
  destruct HE1 as [Hlc1 [Hsn1 Hall1]].
  destruct HE2 as [Hlc2 [Hsn2 Hall2]].
  apply strong_expression_of_reducts.
  - apply lc_choice; assumption.
  - intro Hvalue. inversion Hvalue.
  - intros u Hstep. inversion Hstep; subst.
    + exact (conj Hlc1 (conj Hsn1 Hall1)).
    + exact (conj Hlc2 (conj Hsn2 Hall2)).
Qed.

Lemma strong_related_update : forall Gamma rho x T v,
  strong_related_substitution Gamma rho ->
  strong_value_relation T v ->
  strong_related_substitution
    (update Gamma x T) (subst_update rho x v).
Proof.
  unfold strong_related_substitution, subst_update, update.
  intros Gamma rho x T v Hrel HV y U Hy.
  destruct (Nat.eqb x y) eqn:Heq.
  - apply Nat.eqb_eq in Heq. subst y.
    injection Hy as ->. exact HV.
  - apply Hrel. exact Hy.
Qed.

Lemma strong_empty_related :
  strong_related_substitution empty id_substitution.
Proof.
  unfold strong_related_substitution, empty.
  intros. discriminate H.
Qed.

Lemma strong_expression_intro : forall T t,
  locally_closed t ->
  (value t -> strong_value_relation T t) ->
  (forall u, t --> u -> strong_expression_relation T u) ->
  strong_expression_relation T t.
Proof.
  intros T t Hlc HV Hnext. split. exact Hlc.
  split.
  - apply SN_intro. intros u Hstep.
    destruct (Hnext u Hstep) as [_ [Hsn _]]. exact Hsn.
  - intros v Hsteps Hv. inversion Hsteps; subst.
    + apply HV. exact Hv.
    + destruct (Hnext y H) as [_ [_ Hall]]. eapply Hall; eauto.
Qed.

Lemma strong_expression_if : forall T t1 t2 t3,
  strong_expression_relation Ty_Bool t1 ->
  strong_expression_relation T t2 ->
  strong_expression_relation T t3 ->
  strong_expression_relation T (tm_if t1 t2 t3).
Proof.
  intros T t1 t2 t3 [Hlc [Hsn Hall]] H2 H3.
  revert Hlc Hall. induction Hsn as [t1 Hnext IH]. intros Hlc Hall.
  apply strong_expression_of_reducts.
  - apply lc_if.
    + exact Hlc.
    + exact (proj1 H2).
    + exact (proj1 H3).
  - intro Hv. inversion Hv.
  - intros u Hstep. inversion Hstep; subst.
    + exact H2.
    + exact H3.
    + apply (IH t1' H4).
      * eapply step_preserves_lc; eauto.
      * intros v Hsteps Hv. apply Hall with (v := v); auto.
        eapply multi_step; eauto.
Qed.

Theorem strong_fundamental : forall Gamma t T,
  <{ Gamma |-- t \in T }> ->
  forall rho,
    proper_substitution rho ->
    strong_related_substitution Gamma rho ->
    strong_expression_relation T (msubst rho t).
Proof.
  intros Gamma t T Htyping.
  induction Htyping; intros rho Hproper Hrel.
  - simpl. apply strong_value_is_expression.
    apply Hrel with (x := x). exact H.
  - assert (Habs_lc : locally_closed (msubst rho (tm_abs T1 t1))).
    {
      apply msubst_preserves_term.
      - exact Hproper.
      - apply typing_regular with
          (Gamma := Gamma) (T := Ty_Arrow T1 T2).
        apply T_Abs with (L := L). exact H.
    }
    apply strong_value_is_expression.
    simpl. split.
    + apply v_abs. exact Habs_lc.
    + exists (msubst rho t1). split.
      * reflexivity.
      * intros arg HVarg.
        pose (x := fresh (L ++ free_vars t1)).
        assert (HxL : ~ In x L).
        {
          intro Hin. unfold x in Hin.
          apply (fresh_notin (L ++ free_vars t1)).
          apply in_or_app. left. exact Hin.
        }
        assert (Hxfv : ~ In x (free_vars t1)).
        {
          intro Hin. unfold x in Hin.
          apply (fresh_notin (L ++ free_vars t1)).
          apply in_or_app. right. exact Hin.
        }
        specialize (H0 x HxL (subst_update rho x arg)).
        assert (Harg_lc : locally_closed arg).
        {
          eapply strong_value_relation_lc. exact HVarg.
        }
        specialize (H0 (proper_update rho x arg Hproper Harg_lc)).
        specialize
          (H0 (strong_related_update Gamma rho x T1 arg Hrel HVarg)).
        rewrite
          (msubst_open_update t1 rho x arg Hxfv Hproper Harg_lc) in H0.
        exact H0.
  - apply strong_expression_app with (T1 := T1).
    + apply IHHtyping1; assumption.
    + apply IHHtyping2; assumption.
  - apply strong_value_is_expression.
    simpl. split.
    + apply v_true.
    + left. reflexivity.
  - apply strong_value_is_expression.
    simpl. split.
    + apply v_false.
    + right. reflexivity.
  - apply strong_expression_if.
    + apply IHHtyping1; assumption.
    + apply IHHtyping2; assumption.
    + apply IHHtyping3; assumption.
  - apply strong_expression_choice.
    + apply IHHtyping1; assumption.
    + apply IHHtyping2; assumption.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  (* Complete the proof of normalization. *)
Qed.

End STLCNormalizationIfNondeterminismEasyTask.
