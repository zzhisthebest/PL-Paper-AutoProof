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

Fixpoint reducible (T : ty) (t : tm) : Prop :=
  locally_closed t /\ strongly_normalizing t /\
  match T with
  | Ty_Bool => True
  | Ty_Arrow A B => forall v, reducible A v -> reducible B (tm_app t v)
  end.

Lemma sn_step : forall t t',
  strongly_normalizing t -> t --> t' -> strongly_normalizing t'.
Proof.
  intros t t' Hsn Hstep. inversion Hsn as [t0 Hall]; subst.
  eauto.
Qed.

Lemma lc_step : forall t t',
  locally_closed t -> t --> t' -> locally_closed t'.
Proof.
  intros t t' Hlc Hstep. revert Hlc. induction Hstep; intros Hlc.
  - unfold locally_closed in *. inversion Hlc; subst. inversion H; subst.
    eapply open_preserves_term; eauto.
  - unfold locally_closed in *. inversion Hlc; subst. econstructor; eauto.
  - unfold locally_closed in *. inversion Hlc; subst. econstructor; eauto.
  - unfold locally_closed in *. inversion Hlc; subst. assumption.
  - unfold locally_closed in *. inversion Hlc; subst. assumption.
  - unfold locally_closed in *. inversion Hlc; subst. econstructor; eauto.
  - unfold locally_closed in *. inversion Hlc; subst. assumption.
  - unfold locally_closed in *. inversion Hlc; subst. assumption.
Qed.

Lemma reducible_lc : forall T t, reducible T t -> locally_closed t.
Proof. induction T; simpl; intros t H; tauto. Qed.

Lemma reducible_sn : forall T t, reducible T t -> strongly_normalizing t.
Proof. induction T; simpl; intros t H; tauto. Qed.

Lemma msubst_lc_at : forall k t,
  lc_at k t -> forall rho, proper_substitution rho -> lc_at k (msubst rho t).
Proof.
  intros k t Hlc. induction Hlc; intros rho Hproper; simpl.
  - constructor. lia.
  - apply term_lc_at. apply Hproper.
  - constructor; eauto.
  - constructor. eauto.
  - constructor.
  - constructor.
  - constructor; eauto.
  - constructor; eauto.
Qed.

Lemma msubst_preserves_lc : forall t rho,
  locally_closed t -> proper_substitution rho -> locally_closed (msubst rho t).
Proof.
  intros. unfold locally_closed in *. eapply msubst_lc_at; eauto.
Qed.

Lemma msubst_open_rec : forall t rho k u,
  proper_substitution rho ->
  msubst rho (open_rec k u t) = open_rec k (msubst rho u) (msubst rho t).
Proof.
  induction t; intros rho k u Hproper; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - rewrite open_rec_term by apply Hproper. reflexivity.
  - rewrite IHt1, IHt2 by assumption. reflexivity.
  - rewrite IHt by assumption. reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2, IHt3 by assumption. reflexivity.
  - rewrite IHt1, IHt2 by assumption. reflexivity.
Qed.

Lemma msubst_open : forall t rho u,
  proper_substitution rho ->
  msubst rho (open t u) = open (msubst rho t) (msubst rho u).
Proof. intros. unfold open. apply msubst_open_rec; assumption. Qed.

Lemma msubst_update_fresh : forall t rho x v,
  ~ In x (free_vars t) ->
  msubst (subst_update rho x v) t = msubst rho t.
Proof.
  induction t; simpl; intros rho x v Hfresh; try reflexivity.
  - unfold subst_update. destruct (Nat.eqb x a) eqn:E; [|reflexivity].
    exfalso. apply Nat.eqb_eq in E. subst. apply Hfresh. simpl. auto.
  - f_equal.
    + apply IHt1. intro Hin. apply Hfresh. apply in_or_app. left. exact Hin.
    + apply IHt2. intro Hin. apply Hfresh. apply in_or_app. right. exact Hin.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal.
    + apply IHt1. intro Hin. apply Hfresh. repeat rewrite in_app_iff. auto.
    + apply IHt2. intro Hin. apply Hfresh. repeat rewrite in_app_iff. auto.
    + apply IHt3. intro Hin. apply Hfresh. repeat rewrite in_app_iff. auto.
  - f_equal.
    + apply IHt1. intro Hin. apply Hfresh. apply in_app_iff. auto.
    + apply IHt2. intro Hin. apply Hfresh. apply in_app_iff. auto.
Qed.

Lemma msubst_open_fresh : forall t rho x v,
  proper_substitution rho -> locally_closed v ->
  ~ In x (free_vars t) ->
  msubst (subst_update rho x v) (open t (tm_fvar x)) =
  open (msubst rho t) v.
Proof.
  intros. rewrite msubst_open.
  - rewrite msubst_update_fresh by assumption.
    simpl. unfold subst_update. rewrite Nat.eqb_refl. reflexivity.
  - apply proper_update; assumption.
Qed.

Lemma msubst_id_lc : forall t,
  locally_closed t -> msubst id_substitution t = t.
Proof.
  intros t Hlc. induction Hlc; simpl; try rewrite IHHlc; try rewrite IHHlc1; try rewrite IHHlc2; try rewrite IHHlc3; reflexivity.
Qed.

Lemma reducible_step : forall T t t',
  reducible T t -> t --> t' -> reducible T t'.
Proof.
  induction T; simpl; intros t t' [Hlc [Hsn Hrel]] Hstep.
  - split.
    + eapply lc_step; eauto.
    + split; [eapply sn_step; eauto| exact I].
  - split.
    + eapply lc_step; eauto.
    + split; [eapply sn_step; eauto|].
      intros v Hv.
      eapply IHT2.
      * apply Hrel. exact Hv.
      * apply ST_App1; [exact Hstep|].
        apply reducible_lc with (T:=T1). exact Hv.
Qed.

Lemma reducible_app : forall A f a,
  strongly_normalizing f -> reducible A a ->
  (forall v, reducible A v -> strongly_normalizing (tm_app f v)) ->
  strongly_normalizing (tm_app f a).
Proof.
  intros A f a Hf Ha Hfun. revert A a Ha Hfun. induction Hf.
  intros A a Ha Hfun.
  pose proof (reducible_lc A a Ha) as Hal.
  pose proof (reducible_sn A a Ha) as Hasn.
  revert Ha Hfun Hal.
  induction Hasn; intros Ha Hfun Hal.
  apply SN_intro. intros t' Hstep. inversion Hstep; subst.
  - eapply sn_step.
    + apply Hfun. exact Ha.
    + econstructor; eauto.
  - apply (H0 t1' H5 A t0 Ha).
    intro v. intros Hv.
    eapply sn_step.
    + apply Hfun. exact Hv.
    + apply ST_App1; [eassumption|eapply reducible_lc; exact Hv].
  - exact (H2 t2' H7 (@reducible_step A t0 t2' Ha H7) Hfun (@lc_step t0 t2' Hal H7)).
Qed.

Lemma sn_app_nonvalue : forall A B t v,
  ~ value t -> reducible A v ->
  (forall t', t --> t' -> reducible (Ty_Arrow A B) t') ->
  strongly_normalizing (tm_app t v).
Proof.
  intros A B t v Hnv Hv Hred. apply SN_intro. intros q Hq.
  inversion Hq; subst.
  - exfalso. apply Hnv. eauto using value.
  - destruct (Hred t1' H1) as [_ [_ Hfun]]. eapply reducible_sn. apply Hfun. exact Hv.
  - exfalso. apply Hnv. assumption.
Qed.

Lemma reducible_expansion_nonvalue : forall T t,
  locally_closed t -> ~ value t ->
  (forall t', t --> t' -> reducible T t') -> reducible T t.
Proof.
  induction T; simpl; intros t Hlc Hnv Hred.
  - split; [exact Hlc|]. split.
    + apply SN_intro. intros t' Hs. apply reducible_sn with Ty_Bool.
      eapply Hred; eauto.
    + exact I.
  - split; [exact Hlc|]. split.
    + apply SN_intro. intros t' Hs. apply reducible_sn with (Ty_Arrow T1 T2).
      eapply Hred; eauto.
    + intros v Hv. apply IHT2.
      * apply lc_app; [exact Hlc|apply reducible_lc with T1; exact Hv].
      * intro Hval. inversion Hval.
      * intros q Hq. inversion Hq; subst.
        -- exfalso. apply Hnv. econstructor; eassumption.
        -- destruct (Hred t1' H1) as [_ [_ Happ]]. apply Happ. exact Hv.
        -- exfalso. apply Hnv. eauto using value.
Qed.

Lemma reducible_abs_app : forall A B T body,
  locally_closed (tm_abs T body) ->
  (forall v, reducible A v -> reducible B (open body v)) ->
  forall v, reducible A v -> reducible B (tm_app (tm_abs T body) v).
Proof.
  intros A B T body Habs Hbody.
  assert (Hall : forall v, strongly_normalizing v -> reducible A v ->
      reducible B (tm_app (tm_abs T body) v)).
  { intros v Hsn. induction Hsn as [v Hnext IH]. intros Hv.
    eapply reducible_expansion_nonvalue.
    - apply lc_app; [exact Habs|apply reducible_lc with A; exact Hv].
    - intro Hval. inversion Hval.
    - intros q Hq. inversion Hq; subst.
      + apply Hbody. exact Hv.
      + exfalso. eapply value_no_step; [constructor; exact Habs|eassumption].
      + eapply IH; [eassumption|eapply reducible_step; eassumption].
  }
  intros v Hv. apply Hall; [eapply reducible_sn; eauto|exact Hv].
Qed.

Lemma reducible_if : forall T c t e,
  reducible Ty_Bool c -> reducible T t -> reducible T e ->
  reducible T (tm_if c t e).
Proof.
  intros T c t e Hc Ht He.
  assert (Hall : forall c, strongly_normalizing c -> reducible Ty_Bool c ->
      reducible T (tm_if c t e)).
  { intros c0 Hsn. induction Hsn as [c0 Hnext IH]. intros Hc0.
    eapply reducible_expansion_nonvalue.
    - apply lc_if; [apply reducible_lc with Ty_Bool|apply reducible_lc with T|apply reducible_lc with T]; assumption.
    - intro Hv. inversion Hv.
    - intros q Hq. inversion Hq; subst.
      + exact Ht.
      + exact He.
      + apply IH.
        * exact H2.
        * eapply reducible_step; eauto.
  }
  apply Hall; [eapply reducible_sn; eauto|exact Hc].
Qed.

Lemma reducible_choice : forall T t1 t2,
  reducible T t1 -> reducible T t2 -> reducible T (tm_choice t1 t2).
Proof.
  intros T t1 t2 H1 H2. eapply reducible_expansion_nonvalue.
  - apply lc_choice; apply reducible_lc with T; assumption.
  - intro Hv. inversion Hv.
  - intros q Hq. inversion Hq; subst; assumption.
Qed.

Lemma has_type_lc : forall Gamma t T,
  <{ Gamma |-- t \in T }> -> locally_closed t.
Proof.
  intros Gamma t T Hty. induction Hty.
  - apply lc_fvar.
  - apply lc_abs. specialize (H (fresh L) (fresh_notin L)).
    eapply lc_at_open_inv with (u:=tm_fvar (fresh L)).
    apply H0. apply fresh_notin.
  - apply lc_app; assumption.
  - apply lc_true.
  - apply lc_false.
  - apply lc_if; assumption.
  - apply lc_choice; assumption.
Qed.

Definition related_context (Gamma : context) (rho : term_substitution) : Prop :=
  forall x T, Gamma x = Some T -> reducible T (rho x).

Lemma sn_if : forall c t e,
  strongly_normalizing c -> strongly_normalizing t -> strongly_normalizing e ->
  strongly_normalizing (tm_if c t e).
Proof.
  intros c t e Hc. revert t e.
  induction Hc as [c Hsteps IHc]. intros t e Ht He.
  apply SN_intro. intros q Hq. inversion Hq; subst.
  - exact Ht.
  - exact He.
  - eapply IHc; eauto.
Qed.

Lemma sn_choice : forall t1 t2,
  strongly_normalizing t1 -> strongly_normalizing t2 ->
  strongly_normalizing (tm_choice t1 t2).
Proof.
  intros t1 t2 H1 H2. apply SN_intro. intros q Hq. inversion Hq; subst; eauto.
Qed.

Theorem fundamental : forall Gamma t T,
  <{ Gamma |-- t \in T }> -> forall rho,
  related_context Gamma rho ->
  proper_substitution rho ->
  reducible T (msubst rho t).
Proof.
  intros Gamma t T Hty. induction Hty; intros rho Hrel Hproper.
  - simpl. apply Hrel with (x:=x). assumption.
  - assert (HabsLC : locally_closed (tm_abs T1 (msubst rho t1))).
    { change (locally_closed (msubst rho (tm_abs T1 t1))).
      eapply msubst_preserves_lc.
      - apply lc_abs. pose proof (@has_type_lc _ _ _ (H (fresh L) (fresh_notin L))) as Hlcbody.
        unfold locally_closed in Hlcbody.
        eapply lc_at_open_inv with (u:=tm_fvar (fresh L)). exact Hlcbody.
      - exact Hproper. }
    simpl. split; [exact HabsLC|]. split.
      * apply SN_intro. intros q Hq. exfalso.
        eapply value_no_step; [constructor; exact HabsLC|exact Hq].
      * assert (Hbodyall : forall v, reducible T1 v ->
            reducible T2 (open (msubst rho t1) v)).
        { intros v Hv.
        assert (Hfresh : ~ In (fresh (L ++ free_vars t1)) (L ++ free_vars t1))
          by apply fresh_notin.
        assert (HnotL : ~ In (fresh (L ++ free_vars t1)) L).
        { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
        assert (HnotFV : ~ In (fresh (L ++ free_vars t1)) (free_vars t1)).
        { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
        pose proof (H (fresh (L ++ free_vars t1)) HnotL) as Hbodyty.
        pose proof (H0 (fresh (L ++ free_vars t1)) HnotL
          (subst_update rho (fresh (L ++ free_vars t1)) v)) as Hbodyred.
        assert (Hrel' : related_context (update Gamma (fresh (L ++ free_vars t1)) T1)
                          (subst_update rho (fresh (L ++ free_vars t1)) v)).
        { intros y U Hy. unfold update in Hy. destruct (Nat.eqb (fresh (L ++ free_vars t1)) y) eqn:E.
          - apply Nat.eqb_eq in E. subst y. inversion Hy; subst. unfold subst_update.
            rewrite Nat.eqb_refl. exact Hv.
          - unfold subst_update. rewrite E. apply Hrel with (x:=y) (T:=U). exact Hy. }
        assert (Hproper' : proper_substitution (subst_update rho (fresh (L ++ free_vars t1)) v)).
        { apply proper_update; [exact Hproper|apply reducible_lc with T1; exact Hv]. }
        specialize (Hbodyred Hrel' Hproper').
        rewrite msubst_open_fresh in Hbodyred; [|exact Hproper|apply reducible_lc with T1; exact Hv|exact HnotFV].
        exact Hbodyred. }
        intros v Hv. eapply reducible_abs_app; eauto.
  - pose proof (IHHty1 rho Hrel Hproper) as Hfun.
    pose proof (IHHty2 rho Hrel Hproper) as Harg.
    destruct Hfun as [_ [_ Happly]]. simpl in Happly.
    apply Happly. exact Harg.
  - simpl. split; [apply lc_true|].
    split; [apply SN_intro; intros q Hq; inversion Hq|exact I].
  - simpl. split; [apply lc_false|].
    split; [apply SN_intro; intros q Hq; inversion Hq|exact I].
  - simpl. apply reducible_if.
    + apply IHHty1; assumption.
    + apply IHHty2; assumption.
    + apply IHHty3; assumption.
  - simpl. apply reducible_choice.
    + apply IHHty1; assumption.
    + apply IHHty2; assumption.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  pose proof (fundamental empty t T Hty id_substitution) as Hred.
  assert (Hctx : related_context empty id_substitution).
  { intros x U Hlookup. unfold empty in Hlookup. discriminate. }
  specialize (Hred Hctx id_substitution_proper).
  rewrite msubst_id_lc in Hred.
  - eapply reducible_sn. exact Hred.
  - eapply has_type_lc. exact Hty.
Qed.

End STLCNormalizationIfNondeterminismEasyTask.
