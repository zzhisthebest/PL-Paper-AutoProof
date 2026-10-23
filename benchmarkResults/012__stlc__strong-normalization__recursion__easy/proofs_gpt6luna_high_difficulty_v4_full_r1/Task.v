(** STLC call-by-value strong-normalization benchmark, Easy variant.
    System T-style natural-number recursion; no if-then-else or choice. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Relations.Relation_Definitions Lia.
Import ListNotations.

Module STLCNormalizationRecursionEasyTask.

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

  | tm_natrec : tm -> tm -> tm -> tm.

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
      lc_at k (tm_natrec n b s).

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
  end.

Definition proper_substitution (rho : term_substitution) : Prop :=
  forall x, locally_closed (rho x).

Fixpoint value_relation (T : ty) (v : tm) : Prop :=
  value v /\
  match T with
  | Ty_Nat => numeric_value v
  | Ty_Bool =>
      v = tm_true \/ v = tm_false
  | Ty_Arrow T1 T2 =>
      exists body,
        v = tm_abs T1 body /\
        forall arg,
          value_relation T1 arg ->
          locally_closed (open body arg) /\
          exists v',
            open body arg -->* v' /\
            value_relation T2 v'
  end.

Definition expression_relation (T : ty) (t : tm) : Prop :=
  locally_closed t /\
  exists v,
    t -->* v /\
    value_relation T v.

Definition related_substitution
    (Gamma : context) (rho : term_substitution) : Prop :=
  forall x T, Gamma x = Some T -> value_relation T (rho x).

Fixpoint free_vars (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_app t1 t2 => free_vars t1 ++ free_vars t2
  | tm_abs _ t1 => free_vars t1
  | tm_true => []
  | tm_false => []
  | tm_zero => []
  | tm_succ t1 => free_vars t1
  | tm_natrec n b s => free_vars n ++ free_vars b ++ free_vars s
  end.

Fixpoint numeral (n : nat) : tm :=
  match n with
  | O => tm_zero
  | S m => tm_succ (numeral m)
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

Lemma numeric_value_lc : forall n,
  numeric_value n -> locally_closed n.
Proof.
  intros n H. induction H; constructor; assumption.
Qed.

Lemma value_regular : forall v,
  value v -> locally_closed v.
Proof.
  intros v H. destruct H.
  - assumption.
  - apply lc_true.
  - apply lc_false.
  - apply numeric_value_lc. assumption.
Qed.

Lemma numeral_numeric : forall n, numeric_value (numeral n).
Proof.
  induction n; simpl; constructor; assumption.
Qed.

Lemma numeric_numeral : forall t,
  numeric_value t -> exists n : nat, t = numeral n.
Proof.
  intros t H. induction H.
  - exists 0. reflexivity.
  - destruct IHnumeric_value as [m ->]. exists (S m). reflexivity.
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
  - apply lc_zero.
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
  - apply lc_zero.
  - apply lc_succ. assumption.
  - apply lc_rec; assumption.
Qed.

Lemma canonical_forms_fun : forall t T1 T2,
  <{ empty |-- t \in T1 -> T2 }> ->
  value t ->
  exists body, t = tm_abs T1 body.
Proof.
  intros t T1 T2 HT HV.
  inversion HV; subst.
  - inversion HT; subst. eauto.
  - inversion HT.
  - inversion HT.
  - inversion H; subst; inversion HT.
Qed.

Lemma canonical_forms_nat : forall t,
  <{ empty |-- t \in Nat }> ->
  value t -> numeric_value t.
Proof.
  intros t HT HV. inversion HV; subst; try assumption; inversion HT.
Qed.

Lemma numeric_no_step : forall n,
  numeric_value n -> forall t, ~ (n --> t).
Proof.
  intros n Hn. induction Hn; intros u Hs; inversion Hs; subst.
  eapply IHHn. eassumption.
Qed.

Lemma value_no_step : forall v,
  value v -> forall t, ~ (v --> t).
Proof.
  intros v Hv t Hs. destruct Hv; try solve [inversion Hs].
  eapply numeric_no_step; eauto.
Qed.

Lemma step_deterministic : forall t t1 t2,
  t --> t1 -> t --> t2 -> t1 = t2.
Proof.
  intros t t1 t2 Hs1. revert t2.
  induction Hs1; intros u Hs2; inversion Hs2; subst;
    try reflexivity;
    try solve [exfalso; eapply value_no_step; eauto];
    try solve [exfalso; eapply numeric_no_step; eauto];
    try solve [f_equal; eauto].
  all: try match goal with H : tm_abs _ _ --> _ |- _ => inversion H end.
  all: try match goal with H : tm_zero --> _ |- _ => inversion H end.
  all: try solve [match goal with
    | HV : value ?v, HS : ?v --> ?u |- _ =>
        exfalso; exact (value_no_step v HV u HS)
    end].
  all: try solve [match goal with
    | HN : numeric_value ?n, HS : tm_succ ?n --> ?u |- _ =>
        exfalso; exact (numeric_no_step (tm_succ n) (nv_succ n HN) u HS)
    end].
Qed.

Theorem progress : forall t T,
  <{ empty |-- t \in T }> ->
  value t \/ exists t', t --> t'.
Proof.
  intros t T Ht. remember empty as Gamma.
  induction Ht; subst Gamma.
  - discriminate H.
  - left. apply v_abs. apply typing_regular with
      (Gamma := empty) (T := Ty_Arrow T1 T2).
    apply T_Abs with (L := L). exact H.
  - right.
    destruct (IHHt1 eq_refl) as [Hv1 | [u Hs1]].
    + destruct (IHHt2 eq_refl) as [Hv2 | [u Hs2]].
      * destruct (canonical_forms_fun _ _ _ Ht1 Hv1) as [body ->].
        exists (open body t2). apply ST_AppAbs.
        -- apply value_regular. exact Hv1.
        -- exact Hv2.
      * exists (tm_app t1 u). apply ST_App2; assumption.
    + exists (tm_app u t2). apply ST_App1.
      * exact Hs1.
      * eapply typing_regular. exact Ht2.
  - left. apply v_true.
  - left. apply v_false.
  - left. apply v_nat. apply nv_zero.
  - destruct (IHHt eq_refl) as [Hv | [u Hs]].
    + left. apply v_nat. apply nv_succ.
      eapply canonical_forms_nat; eauto.
    + right. exists (tm_succ u). apply ST_Succ. exact Hs.
  - right.
    destruct (IHHt1 eq_refl) as [Hvn | [n' Hsn]].
    + pose proof (canonical_forms_nat _ Ht1 Hvn) as Hnum.
      destruct (IHHt2 eq_refl) as [Hvb | [b' Hsb]].
      * destruct (IHHt3 eq_refl) as [Hvs | [s' Hss]].
        -- inversion Hnum; subst.
           ++ exists b. apply ST_RecZero; assumption.
           ++ eexists. apply ST_RecSucc; eassumption.
        -- exists (tm_natrec n b s'). apply ST_RecStep; assumption.
      * exists (tm_natrec n b' s). apply ST_RecBase; try assumption.
        eapply typing_regular. exact Ht3.
    + exists (tm_natrec n' b s). apply ST_RecArg; try assumption;
        eapply typing_regular; eassumption.
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
  - reflexivity.
  - rewrite IHHlc by assumption. reflexivity.
  - rewrite IHHlc1 by assumption.
    rewrite IHHlc2 by assumption.
    rewrite IHHlc3 by assumption. reflexivity.
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
  - reflexivity.
  - rewrite IHt by assumption. reflexivity.
  - apply notin_app_split in Hfresh as [Hfresh1 Hfresh23].
    apply notin_app_split in Hfresh23 as [Hfresh2 Hfresh3].
    rewrite IHt1 by assumption.
    rewrite IHt2 by assumption.
    rewrite IHt3 by assumption. reflexivity.
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

Definition halts (t : tm) : Prop :=
  exists v, t -->* v /\ value v.

Lemma multi_trans : forall t u v,
  t -->* u ->
  u -->* v ->
  t -->* v.
Proof.
  intros t u v Htu Huv.
  induction Htu.
  - exact Huv.
  - eapply multi_step; eauto.
Qed.

Lemma multi_app1 : forall t1 t1' t2,
  t1 -->* t1' ->
  locally_closed t2 ->
  tm_app t1 t2 -->* tm_app t1' t2.
Proof.
  intros t1 t1' t2 Hs Ht2.
  induction Hs.
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_App1; eauto.
    + exact IHHs.
Qed.

Lemma multi_app2 : forall v1 t2 t2',
  value v1 ->
  t2 -->* t2' ->
  tm_app v1 t2 -->* tm_app v1 t2'.
Proof.
  intros v1 t2 t2' Hv Hs.
  induction Hs.
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_App2; eauto.
    + exact IHHs.
Qed.

Lemma value_relation_value : forall T v,
  value_relation T v -> value v.
Proof.
  intros T v H. destruct T; simpl in H; tauto.
Qed.

Lemma value_relation_term : forall T v,
  value_relation T v -> locally_closed v.
Proof.
  intros T v H.
  apply value_regular.
  apply value_relation_value with (T := T).
  exact H.
Qed.

Lemma expression_relation_halts : forall T t,
  expression_relation T t ->
  halts t.
Proof.
  intros T t [_ [v [Hs HV]]].
  exists v. split.
  - exact Hs.
  - apply value_relation_value with (T := T). exact HV.
Qed.

Lemma related_update : forall Gamma rho x T v,
  related_substitution Gamma rho ->
  value_relation T v ->
  related_substitution (update Gamma x T) (subst_update rho x v).
Proof.
  unfold related_substitution, subst_update, update.
  intros Gamma rho x T v Hrel HV y U Hy.
  destruct (Nat.eqb x y) eqn:Heq.
  - apply Nat.eqb_eq in Heq. subst y.
    injection Hy as ->. exact HV.
  - apply Hrel. exact Hy.
Qed.

Lemma empty_related :
  related_substitution empty id_substitution.
Proof.
  unfold related_substitution, empty.
  intros. discriminate H.
Qed.

Lemma value_is_expression : forall T v,
  value_relation T v -> expression_relation T v.
Proof.
  intros T v HV. split.
  - eapply value_relation_term. exact HV.
  - exists v. split.
    + apply multi_refl.
    + exact HV.
Qed.

Lemma expression_expansion : forall T t u,
  locally_closed t ->
  t -->* u ->
  expression_relation T u ->
  expression_relation T t.
Proof.
  intros T t u Hlc Hsteps [_ [v [Hs HV]]].
  split. exact Hlc.
  exists v. split.
  - eapply multi_trans; eauto.
  - exact HV.
Qed.

Lemma multi_succ : forall t u,
  t -->* u -> tm_succ t -->* tm_succ u.
Proof.
  intros t u H. induction H.
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_Succ. exact H.
    + exact IHmulti.
Qed.

Lemma multi_rec_arg : forall n n' b s,
  n -->* n' -> locally_closed b -> locally_closed s ->
  tm_natrec n b s -->* tm_natrec n' b s.
Proof.
  intros n n' b s H Hb Hs. induction H.
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_RecArg; eassumption.
    + exact IHmulti.
Qed.

Lemma multi_rec_base : forall n b b' s,
  numeric_value n -> b -->* b' -> locally_closed s ->
  tm_natrec n b s -->* tm_natrec n b' s.
Proof.
  intros n b b' s Hn H Hs. induction H.
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_RecBase; eassumption.
    + exact IHmulti.
Qed.

Lemma multi_rec_step : forall n b s s',
  numeric_value n -> value b -> s -->* s' ->
  tm_natrec n b s -->* tm_natrec n b s'.
Proof.
  intros n b s s' Hn Hb H. induction H.
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_RecStep; eassumption.
    + exact IHmulti.
Qed.

(* Optional reference theorem statement.
Theorem fundamental : forall Gamma t T,
  <{ Gamma |-- t \in T }> ->
  forall rho,
    proper_substitution rho ->
    related_substitution Gamma rho ->
    expression_relation T (msubst rho t).
*)

Lemma expression_application : forall A B f a,
  expression_relation (Ty_Arrow A B) f ->
  expression_relation A a ->
  expression_relation B (tm_app f a).
Proof.
  intros A B f a [Hlf [vf [Hf HF]]] [Hla [va [Ha HA]]].
  destruct HF as [Hfv Hfun].
  destruct Hfun as [body [-> Hbody]].
  destruct (Hbody va HA) as [Hlopen [v [Hbodysteps HV]]].
  split.
  - apply lc_app; assumption.
  - exists v. split.
    eapply multi_trans.
    + eapply multi_trans.
      * apply multi_app1; [exact Hf|exact Hla].
      * apply multi_app2; [exact Hfv|exact Ha].
    + eapply multi_step.
      * apply ST_AppAbs.
        -- apply value_regular. exact Hfv.
        -- apply value_relation_value with (T := A). exact HA.
      * exact Hbodysteps.
    + exact HV.
Qed.

Lemma rec_value_relation : forall T n b s,
  numeric_value n ->
  value_relation T b ->
  value_relation (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  expression_relation T (tm_natrec n b s).
Proof.
  intros T n b s Hn. induction Hn; intros Hb Hs.
  - eapply expression_expansion.
    + apply lc_rec; [apply numeric_value_lc; apply nv_zero|apply value_relation_term with (T:=T); exact Hb|apply value_relation_term with (T:=Ty_Arrow Ty_Nat (Ty_Arrow T T)); exact Hs].
    + eapply multi_step. apply ST_RecZero.
      * apply value_relation_value with (T:=T); exact Hb.
      * apply value_relation_value with (T:=Ty_Arrow Ty_Nat (Ty_Arrow T T)); exact Hs.
      * apply multi_refl.
    + apply value_is_expression. exact Hb.
  - assert (Hrec : expression_relation T (tm_natrec t b s)).
    { apply IHHn; assumption. }
    assert (Hsn : expression_relation (Ty_Arrow T T)
         (tm_app s t)).
    { eapply expression_application; [apply value_is_expression; exact Hs|].
      apply value_is_expression. simpl. split.
      - apply v_nat. assumption.
      - assumption. }
    assert (Hresult : expression_relation T
         (tm_app (tm_app s t) (tm_natrec t b s))).
    { eapply expression_application; eassumption. }
    eapply expression_expansion.
    + apply lc_rec; [apply numeric_value_lc; apply nv_succ; assumption|apply value_relation_term with (T:=T); exact Hb|apply value_relation_term with (T:=Ty_Arrow Ty_Nat (Ty_Arrow T T)); exact Hs].
    + eapply multi_step. apply ST_RecSucc.
      * exact Hn.
      * apply value_relation_value with (T:=T); exact Hb.
      * apply value_relation_value with (T:=Ty_Arrow Ty_Nat (Ty_Arrow T T)); exact Hs.
      * apply multi_refl.
    + exact Hresult.
Qed.

Theorem fundamental : forall Gamma t T,
  <{ Gamma |-- t \in T }> ->
  forall rho,
    proper_substitution rho ->
    related_substitution Gamma rho ->
    expression_relation T (msubst rho t).
Proof.
  intros Gamma t T Hty.
  induction Hty; intros rho Hproper Hrelated; simpl.
  - apply value_is_expression. apply Hrelated with (x:=x); assumption.
  - apply value_is_expression. split.
    + apply v_abs. change (locally_closed (msubst rho (tm_abs T1 t1))).
      eapply msubst_preserves_term; [exact Hproper|].
      eapply typing_regular. eapply T_Abs with (L:=L). exact H.
    + exists (msubst rho t1). split; [reflexivity|].
      intros arg Harg.
      set (x := fresh (L ++ free_vars t1)).
      assert (Hx : ~ In x (L ++ free_vars t1)).
      { unfold x. apply fresh_notin. }
      apply notin_app_split in Hx as [HxL Hxfv].
      specialize (H x HxL).
      pose proof (H0 x HxL
        (subst_update rho x arg)
        (proper_update rho x arg Hproper (value_relation_term T1 arg Harg))
        (related_update Gamma rho x T1 arg Hrelated Harg)) as Hopenrel.
      rewrite msubst_open_update in Hopenrel.
      2: exact Hxfv.
      2: exact Hproper.
      2: exact (value_relation_term T1 arg Harg).
      destruct Hopenrel as [Hlc [v [Hsteps Hv]]].
      split; [exact Hlc|]. exists v. auto.
  - eapply expression_application; eauto.
  - apply value_is_expression. simpl. split; [apply v_true|left; reflexivity].
  - apply value_is_expression. simpl. split; [apply v_false|right; reflexivity].
  - apply value_is_expression. simpl. split; [apply v_nat; constructor|constructor].
  - destruct (IHHty rho Hproper Hrelated) as [Hlc [v [Hs Hv]]].
    simpl. eapply expression_expansion.
    + apply lc_succ. exact Hlc.
    + apply multi_succ. exact Hs.
    + apply value_is_expression. simpl. split.
      * apply v_nat. destruct Hv as [Hvv Hnum]. constructor; exact Hnum.
      * destruct Hv as [_ Hnum]. constructor; exact Hnum.
  - destruct (IHHty1 rho Hproper Hrelated) as [Hln [vn [Hn Hvn]]].
    destruct (IHHty2 rho Hproper Hrelated) as [Hlb [vb [Hb Hvb]]].
    destruct (IHHty3 rho Hproper Hrelated) as [Hls [vs [Hs Hvs]]].
    assert (Hnum : numeric_value vn).
    { simpl in Hvn. tauto. }
    assert (Hbase : value_relation T vb) by exact Hvb.
    assert (Hstep : value_relation (Ty_Arrow Ty_Nat (Ty_Arrow T T)) vs) by exact Hvs.
    assert (Hrecval : expression_relation T (tm_natrec vn vb vs)).
    { eapply rec_value_relation; eassumption. }
    eapply expression_expansion.
    + change (locally_closed (msubst rho (tm_natrec n b s))).
      eapply msubst_preserves_term; [exact Hproper|].
      eapply typing_regular. eapply T_Rec; eassumption.
    + eapply multi_trans.
      * eapply multi_rec_arg; eauto using value_relation_term.
      * eapply multi_trans.
        -- eapply multi_rec_base; eauto using value_relation_term.
        -- eapply multi_rec_step; eauto using value_relation_value.
    + exact Hrecval.
Qed.

Lemma halting_implies_strong_normalization : forall t v,
  t -->* v -> value v -> strongly_normalizing t.
Proof.
  intros t v Hsteps.
  induction Hsteps; intros Hv.
  - constructor. intros u Hstep.
    exfalso. eapply value_no_step; eauto.
  - constructor. intros u Hfirst.
    assert (u = y) by (eapply step_deterministic; eauto).
    subst u. apply IHHsteps. exact Hv.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> -> strongly_normalizing t.
Proof.
  intros t T Hty.
  pose proof (fundamental empty t T Hty id_substitution
    id_substitution_proper empty_related) as Hrel.
  rewrite msubst_id in Hrel.
  destruct Hrel as [_ [v [Hsteps Hv]]].
  apply halting_implies_strong_normalization with (v:=v).
  - exact Hsteps.
  - apply value_relation_value with (T:=T). exact Hv.
Qed.

End STLCNormalizationRecursionEasyTask.
