(** STLC call-by-value strong-normalization benchmark, Easy variant.
    No if-then-else, non-determinism, or recursion is included. *)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Relations.Relation_Definitions.
From Stdlib Require Import Lia.

Import ListNotations.

Module STLCNormalizationNoneEasyTask.

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

Fixpoint free_vars (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_app t1 t2 => free_vars t1 ++ free_vars t2
  | tm_abs _ t1 => free_vars t1
  | tm_true => []
  | tm_false => []
  end.

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

(** Provided logical relation. *)

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
  end.

Definition proper_substitution (rho : term_substitution) : Prop :=
  forall x, locally_closed (rho x).

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
  unfold locally_closed. intros.
  eapply lc_at_weaken; eauto. lia.
Qed.

Lemma value_regular : forall v,
  value v -> locally_closed v.
Proof.
  intros v Hv. inversion Hv; subst.
  - assumption.
  - unfold locally_closed. apply lc_true.
  - unfold locally_closed. apply lc_false.
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
Qed.

Lemma open_rec_term : forall t j u,
  locally_closed t ->
  open_rec j u t = t.
Proof.
  unfold locally_closed. intros.
  eapply open_rec_lc_at; eauto. lia.
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

Lemma id_substitution_proper :
  proper_substitution id_substitution.
Proof.
  unfold proper_substitution, id_substitution, locally_closed.
  intros. apply lc_fvar.
Qed.

(** Supplied fundamental theorem. *)

Fixpoint reducible (T : ty) (t : tm) : Prop :=
  locally_closed t /\ strongly_normalizing t /\
  match T with
  | Ty_Bool => True
  | Ty_Arrow A B => forall u, reducible A u ->
      reducible B (tm_app t u)
  end.

Lemma sn_of_step : forall t t',
  strongly_normalizing t -> t --> t' -> strongly_normalizing t'.
Proof.
  intros t t' H. inversion H; subst. eauto.
Qed.

Lemma lc_at_open_rec : forall t k u,
  lc_at (S k) t -> lc_at k u -> lc_at k (open_rec k u t).
Proof.
  induction t; intros k u Ht Hu; simpl in *.
  - inversion Ht; subst. destruct (Nat.eqb k n) eqn:E.
    + exact Hu.
    + apply lc_bvar. apply Nat.eqb_neq in E. lia.
  - apply lc_fvar.
  - inversion Ht; subst. apply lc_app; eauto.
  - inversion Ht; subst. apply lc_abs. apply IHt.
    + assumption.
    + eapply lc_at_weaken; eauto.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma lc_step : forall t t',
  locally_closed t -> t --> t' -> locally_closed t'.
Proof.
  intros t t' Hlc Hs. induction Hs; unfold locally_closed in *.
  - inversion Hlc; subst. inversion H; subst.
    unfold locally_closed. eapply lc_at_open_rec; eauto using value_regular.
  - inversion Hlc; subst. apply lc_app.
    + eapply IHHs; eauto.
    + assumption.
  - inversion Hlc; subst. apply lc_app; eauto using value_regular.
Qed.

Lemma reducible_lc : forall T t, reducible T t -> locally_closed t.
Proof. intros T t H. destruct T; simpl in H; tauto. Qed.

Lemma reducible_sn : forall T t, reducible T t -> strongly_normalizing t.
Proof. intros T t H. destruct T; simpl in H; tauto. Qed.

Lemma value_no_step : forall v t,
  value v -> ~ (v --> t).
Proof. intros v t Hv Hs. inversion Hv; subst; inversion Hs; subst; eauto. Qed.

Lemma step_deterministic : forall t u v,
  t --> u -> t --> v -> u = v.
Proof.
  intros t u v H1. revert v.
  induction H1; intros z H2; inversion H2; subst; try reflexivity;
    try congruence.
  all: try match goal with Hred : tm_abs _ _ --> _ |- _ => inversion Hred end.
  all: try match goal with Hv : value ?x, Hred : ?x --> _ |- _ =>
    exfalso; exact (value_no_step _ _ Hv Hred) end.
  all: try (f_equal; eauto).
  all: eauto.
Qed.

Lemma sn_reverse_deterministic : forall t u,
  t --> u -> strongly_normalizing u -> strongly_normalizing t.
Proof.
  intros t u Htu Hsn. inversion Hsn as [u' Hnext].
  apply SN_intro. intros v Htv.
  assert (v = u) by (eapply step_deterministic; eauto).
  subst. exact Hsn.
Qed.

Lemma reducible_expand : forall T t t',
  locally_closed t -> ~ value t -> t --> t' ->
  reducible T t' -> reducible T t.
Proof.
  induction T; simpl; intros t t' Hlc Hnv Hstep [Hlc' [Hsn' Hrel']].
  - split; [exact Hlc|]. split.
    + eapply sn_reverse_deterministic; eauto.
    + exact I.
  - split; [exact Hlc|]. split.
    + eapply sn_reverse_deterministic; eauto.
    + intros u Hu.
      eapply IHT2.
      * apply lc_app; [exact Hlc|apply reducible_lc in Hu; exact Hu].
      * intro Hv. inversion Hv.
      * apply ST_App1; [exact Hstep|apply reducible_lc in Hu; exact Hu].
      * apply Hrel'. exact Hu.
Qed.

Lemma reducible_stuck : forall T t,
  locally_closed t -> ~ value t ->
  (forall t', ~ (t --> t')) -> reducible T t.
Proof.
  induction T; simpl; intros t Hlc Hnv Hnostep.
  - split; [exact Hlc|]. split.
    + apply SN_intro. intros t' Hs. exfalso. eapply Hnostep; eauto.
    + exact I.
  - split; [exact Hlc|]. split.
    + apply SN_intro. intros t' Hs. exfalso. eapply Hnostep; eauto.
    + intros u Hu. apply IHT2.
      * apply lc_app; [exact Hlc|apply reducible_lc in Hu; exact Hu].
      * intro Hv. inversion Hv.
      * intros t' Hs. inversion Hs; subst.
        -- exfalso. apply Hnv. constructor. assumption.
        -- exfalso. eapply Hnostep; eauto.
        -- exfalso. apply Hnv. assumption.
Qed.

Lemma lc_at_dec : forall t k, {lc_at k t} + {~ lc_at k t}.
Proof.
  induction t; intros k.
  - destruct (Nat.ltb n k) eqn:E.
    + left. apply lc_bvar. apply Nat.ltb_lt. exact E.
    + apply Nat.ltb_ge in E. right. intro H. inversion H. lia.
  - left. apply lc_fvar.
  - destruct (IHt1 k), (IHt2 k).
    + left. eapply lc_app; eauto.
    + right. intro H. inversion H. contradiction.
    + right. intro H. inversion H. contradiction.
    + right. intro H. inversion H. contradiction.
  - destruct (IHt (S k)).
    + left. apply lc_abs. exact l.
    + right. intro H. inversion H. contradiction.
  - left. apply lc_true.
  - left. apply lc_false.
Defined.

Lemma value_dec : forall t, {value t} + {~ value t}.
Proof.
  destruct t.
  - right. intro H. inversion H.
  - right. intro H. inversion H.
  - right. intro H. inversion H.
  - destruct (lc_at_dec (tm_abs t t0) 0).
    + left. apply v_abs. exact l.
    + right. intro H. inversion H. contradiction.
  - left. constructor.
  - left. constructor.
Defined.

Lemma no_step_app_nonvalue_left : forall t1 t2,
  ~ value t1 -> (forall z, ~ t1 --> z) ->
  forall z, ~ tm_app t1 t2 --> z.
Proof.
  intros t1 t2 Hnv Hnostep z Hs. inversion Hs; subst; eauto.
  all: try (exfalso; apply Hnv; eauto using v_abs).
  all: try (exfalso; eapply Hnostep; eauto).
Qed.

Lemma no_step_bool_app : forall b u,
  (b = tm_true \/ b = tm_false) ->
  (forall z, ~ b --> z) -> (forall z, ~ u --> z) ->
  forall z, ~ tm_app b u --> z.
Proof.
  intros b u Hb Hbn Hun z Hs. inversion Hs; subst; eauto.
  - destruct Hb; subst; discriminate.
  - eapply Hbn; eauto.
  - eapply Hun; eauto.
Qed.

Lemma no_step_app_of_no_steps : forall t1 t2,
  (forall z, ~ t1 --> z) -> (forall z, ~ t2 --> z) ->
  (~ exists A body, t1 = tm_abs A body /\ value t2) ->
  forall z, ~ tm_app t1 t2 --> z.
Proof.
  intros t1 t2 H1 H2 Hnot z Hs. inversion Hs; subst.
  - eapply Hnot. eexists. eexists. split; [reflexivity|assumption].
  - eapply H1; eauto.
  - eapply H2; eauto.
Qed.

Lemma lc_progress_or_stuck : forall t,
  locally_closed t -> value t \/ (exists t', t --> t') \/ (forall t', ~ (t --> t')).
Proof.
  induction t; intros Hlc.
  - unfold locally_closed in Hlc. inversion Hlc; lia.
  - right. right. intros t' Hs. inversion Hs.
  - unfold locally_closed in Hlc. inversion Hlc as [| |k a b H1 H2| | |]; subst.
    destruct (IHt1 H1) as [Hv1|[[t1' Hs1]|Hnone1]].
    + destruct (IHt2 H2) as [Hv2|[[t2' Hs2]|Hnone2]].
      * inversion Hv1; subst.
        -- right. left. eexists. apply ST_AppAbs; eassumption.
        -- right. right. intros z Hz. inversion Hz; subst; try discriminate;
             match goal with
             | Hv : value ?x, Hs : ?x --> ?y |- _ =>
                 exact (value_no_step x y Hv Hs)
             end.
        -- right. right. intros z Hz. inversion Hz; subst; try discriminate;
             match goal with
             | Hv : value ?x, Hs : ?x --> ?y |- _ =>
                 exact (value_no_step x y Hv Hs)
             end.
      * right. left. exists (tm_app t1 t2'). apply ST_App2; assumption.
      * destruct (value_dec t2) as [Hv2|Hnv2].
        -- inversion Hv1; subst.
           ++ right. left. eexists. apply ST_AppAbs; eassumption.
           ++ right. right. eapply no_step_app_of_no_steps.
              ** intros z Hz. eapply value_no_step; [constructor|exact Hz].
              ** exact Hnone2.
              ** intros [A [body [Heq Hval]]]. discriminate.
           ++ right. right. eapply no_step_app_of_no_steps.
              ** intros z Hz. eapply value_no_step; [constructor|exact Hz].
              ** exact Hnone2.
              ** intros [A [body [Heq Hval]]]. discriminate.
        -- right. right. eapply no_step_app_of_no_steps.
           ++ intros z Hz. eapply value_no_step; [exact Hv1|exact Hz].
           ++ exact Hnone2.
           ++ intros [A [body [Heq Hval]]]. apply Hnv2. exact Hval.
    + right. left. exists (tm_app t1' t2). apply ST_App1; assumption.
    + destruct (value_dec t1) as [Hv1|Hnv1].
      * destruct (IHt2 H2) as [Hv2|[[t2' Hs2]|Hnone2]].
        -- inversion Hv1; subst.
           ++ right. left. eexists. apply ST_AppAbs; eassumption.
           ++ right. right. eapply no_step_app_of_no_steps.
              ** intros z Hz. eapply value_no_step; [constructor|exact Hz].
              ** intros z Hz. eapply value_no_step; [exact Hv2|exact Hz].
              ** intros [A [body [Heq Hval]]]. discriminate.
           ++ right. right. eapply no_step_app_of_no_steps.
              ** intros z Hz. eapply value_no_step; [constructor|exact Hz].
              ** intros z Hz. eapply value_no_step; [exact Hv2|exact Hz].
              ** intros [A [body [Heq Hval]]]. discriminate.
        -- right. left. exists (tm_app t1 t2'). apply ST_App2; assumption.
        -- destruct (value_dec t2) as [Hv2|Hnv2].
           ++ inversion Hv1; subst.
              ** right. left. eexists. apply ST_AppAbs; eassumption.
              ** right. right. eapply no_step_app_of_no_steps.
                 --- intros z Hz. eapply value_no_step; [constructor|exact Hz].
                 --- exact Hnone2.
                 --- intros [A [body [Heq Hval]]]. discriminate.
              ** right. right. eapply no_step_app_of_no_steps.
                 --- intros z Hz. eapply value_no_step; [constructor|exact Hz].
                 --- exact Hnone2.
                 --- intros [A [body [Heq Hval]]]. discriminate.
           ++ right. right. eapply no_step_app_of_no_steps.
              ** intros z Hz. eapply value_no_step; [exact Hv1|exact Hz].
              ** exact Hnone2.
              ** intros [A [body [Heq Hval]]]. apply Hnv2. exact Hval.
      * right. right. eapply no_step_app_nonvalue_left; eauto.
  - left. apply v_abs. exact Hlc.
  - left. constructor.
  - left. constructor.
Qed.

Lemma reducible_step : forall T t t',
  reducible T t -> t --> t' -> reducible T t'.
Proof.
  induction T; simpl; intros t t' [Hlc [Hsn Hrel]] Hstep.
  - split; [eapply lc_step|]; [exact Hlc|exact Hstep|].
    split; [eapply sn_of_step|]; [exact Hsn|exact Hstep|exact I].
  - split; [eapply lc_step|]; [exact Hlc|exact Hstep|].
    split; [eapply sn_of_step|]; [exact Hsn|exact Hstep|].
    intros u Hu.
    pose proof (reducible_lc _ _ Hu) as Hulc.
    eapply IHT2.
    + apply Hrel; exact Hu.
    + apply ST_App1; [exact Hstep|exact Hulc].
Qed.

Lemma reducible_abs_app : forall A B body u,
  locally_closed (tm_abs A body) ->
  (forall u', reducible A u' -> reducible B (open body u')) ->
  reducible A u -> reducible B (tm_app (tm_abs A body) u).
Proof.
  intros A B body u Habs Hbody Hu.
  pose proof (reducible_sn _ _ Hu) as Husn.
  revert Hbody Hu.
  induction Husn as [u Hnext IH]; intros Hbody Hu.
  destruct (value_dec u) as [Hv|Hnv].
  - eapply reducible_expand with (t' := open body u).
    + apply lc_app; [exact Habs|apply reducible_lc in Hu; exact Hu].
    + intro Hval. inversion Hval.
    + apply ST_AppAbs; assumption.
    + apply Hbody. exact Hu.
  - destruct (lc_progress_or_stuck u (reducible_lc _ _ Hu)) as [Hv|[[u' Hstep]|Hnone]].
    + contradiction.
    + eapply reducible_expand with (t' := tm_app (tm_abs A body) u').
      * apply lc_app; [exact Habs|apply reducible_lc in Hu; exact Hu].
      * intro Hval. inversion Hval.
      * apply ST_App2; [constructor; exact Habs|exact Hstep].
      * apply (IH u' Hstep Hbody). eapply reducible_step; eauto.
    + apply reducible_stuck.
      * apply lc_app; [exact Habs|apply reducible_lc in Hu; exact Hu].
      * intro Hval. inversion Hval.
      * intros z Hz. inversion Hz; subst.
        -- exfalso. apply Hnv. assumption.
        -- exfalso. eapply value_no_step; eauto using v_abs.
        -- exfalso. eapply Hnone; eauto.
Qed.

Lemma sn_app_abs : forall A body u,
  locally_closed (tm_abs A body) ->
  (forall u', reducible A u' ->
      strongly_normalizing (open body u')) ->
  reducible A u ->
  strongly_normalizing (tm_app (tm_abs A body) u).
Proof.
  intros A body u Habs Hbody Hu.
  pose proof (reducible_sn _ _ Hu) as Husn.
  revert Hbody Hu.
  induction Husn as [u Hnext IH]; intros Hbody Hurel.
  apply SN_intro. intros t' Hstep. inversion Hstep; subst.
  - eapply Hbody; eauto.
  - match goal with Hred : tm_abs _ _ --> _ |- _ => inversion Hred end.
  - eapply (IH t2' H3 Hbody).
    eapply reducible_step; eauto.
Qed.

Lemma msubst_open : forall rho t u,
  proper_substitution rho ->
  msubst rho (open t u) = open (msubst rho t) (msubst rho u).
Proof.
  intros rho t. unfold open. generalize 0.
  induction t; intros k u Hproper; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. apply open_rec_term. apply Hproper.
  - rewrite IHt1, IHt2 by assumption. reflexivity.
  - rewrite IHt by assumption. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma msubst_update_fresh : forall rho x u t,
  ~ In x (free_vars t) ->
  msubst (subst_update rho x u) t = msubst rho t.
Proof.
  intros rho x u t. induction t; simpl; intros H; try reflexivity.
  - destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply H. simpl. auto.
    + unfold subst_update. rewrite E. reflexivity.
  - apply notin_app_split in H as [H1 H2]. rewrite IHt1, IHt2; auto.
  - f_equal. apply IHt. exact H.
Qed.

Lemma subst_update_same : forall rho x u,
  subst_update rho x u x = u.
Proof.
  intros. unfold subst_update. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma msubst_open_fvar : forall rho t x,
  proper_substitution rho ->
  msubst rho (open t (tm_fvar x)) = open (msubst rho t) (rho x).
Proof.
  intros. rewrite msubst_open by assumption. simpl. reflexivity.
Qed.

Definition context_related (Gamma : context) (rho : term_substitution) : Prop :=
  forall x T, Gamma x = Some T -> reducible T (rho x).

Lemma context_related_update : forall Gamma rho x T u,
  context_related Gamma rho -> reducible T u ->
  context_related (update Gamma x T) (subst_update rho x u).
Proof.
  intros Gamma rho x T u Hctx Hu y U Hy.
  unfold update in Hy. unfold subst_update.
  destruct (Nat.eqb x y) eqn:Heq.
  - apply Nat.eqb_eq in Heq. subst y.
    inversion Hy; subst. exact Hu.
  - apply Hctx with (x:=y) (T:=U). exact Hy.
Qed.

Lemma reducible_fvar : forall T x, reducible T (tm_fvar x).
Proof.
  intros. apply reducible_stuck.
  - unfold locally_closed. apply lc_fvar.
  - intro H. inversion H.
  - intros t' Hs. inversion Hs.
Qed.

Lemma msubst_id_identity : forall t, msubst id_substitution t = t.
Proof.
  induction t; simpl; try rewrite IHt; try rewrite IHt1; try rewrite IHt2; reflexivity.
Qed.

Theorem fundamental : forall Gamma t T,
  <{ Gamma |-- t \in T }> ->
  forall rho, context_related Gamma rho -> proper_substitution rho ->
  reducible T (msubst rho t).
Proof.
  intros Gamma t T Hty. induction Hty; intros rho Hctx Hproper.
  - simpl. apply Hctx with (x:=x). assumption.
  - simpl. set (x := fresh (L ++ free_vars t1)).
    assert (HxL : ~ In x L).
    { unfold x. intro Hin. apply fresh_notin with (L:=L ++ free_vars t1).
      apply in_or_app. left. exact Hin. }
    assert (HxF : ~ In x (free_vars t1)).
    { unfold x. intro Hin. apply fresh_notin with (L:=L ++ free_vars t1).
      apply in_or_app. right. exact Hin. }
    assert (Heq_open : forall u, proper_substitution (subst_update rho x u) ->
      msubst (subst_update rho x u) (open t1 (tm_fvar x)) =
      open (msubst rho t1) u).
    { intros u Hpu. rewrite msubst_open by exact Hpu. simpl.
      rewrite subst_update_same. rewrite msubst_update_fresh by exact HxF.
      reflexivity. }
    assert (Hrho_x : proper_substitution
       (subst_update rho x (tm_fvar x))).
    { apply proper_update; [exact Hproper|]. unfold locally_closed. apply lc_fvar. }
    assert (Hctx_x : context_related (update Gamma x T1)
       (subst_update rho x (tm_fvar x))).
    { apply context_related_update; [exact Hctx|apply reducible_fvar]. }
    pose proof (H0 x HxL (subst_update rho x (tm_fvar x)) Hctx_x Hrho_x) as Hr_x.
    rewrite (Heq_open (tm_fvar x) Hrho_x) in Hr_x.
    assert (Hbody_lc : lc_at 1 (msubst rho t1)).
    { apply lc_at_open_inv with (u:=tm_fvar x).
      unfold locally_closed. apply reducible_lc in Hr_x. exact Hr_x. }
    assert (Habs_lc : locally_closed (tm_abs T1 (msubst rho t1))).
    { unfold locally_closed. apply lc_abs. exact Hbody_lc. }
    split; [exact Habs_lc|]. split.
    + apply SN_intro. intros t' Hs. inversion Hs.
    + intros u Hu. apply reducible_abs_app; [exact Habs_lc| |exact Hu].
      intros u' Hu'.
      assert (Hrho_u : proper_substitution (subst_update rho x u')).
      { apply proper_update; [exact Hproper|]. apply reducible_lc in Hu'. exact Hu'. }
      assert (Hctx_u : context_related (update Gamma x T1)
         (subst_update rho x u')).
      { apply context_related_update; assumption. }
      pose proof (H0 x HxL (subst_update rho x u') Hctx_u Hrho_u) as Hr.
      rewrite (Heq_open u' Hrho_u) in Hr. exact Hr.
  - simpl. specialize (IHHty1 rho Hctx Hproper) as Hf.
    specialize (IHHty2 rho Hctx Hproper) as Ha.
    simpl in Hf. destruct Hf as [_ [_ Hfun]].
    exact (Hfun (msubst rho t2) Ha).
  - simpl. split; [unfold locally_closed; apply lc_true|].
    split; [apply SN_intro; intros t' Hs; inversion Hs|exact I].
  - simpl. split; [unfold locally_closed; apply lc_false|].
    split; [apply SN_intro; intros t' Hs; inversion Hs|exact I].
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  assert (Hctx : context_related empty id_substitution).
  { intros x U Hlookup. discriminate. }
  pose proof (fundamental empty t T Hty id_substitution Hctx
                id_substitution_proper) as Hr.
  rewrite msubst_id_identity in Hr.
  exact (reducible_sn T t Hr).
Qed.

End STLCNormalizationNoneEasyTask.
