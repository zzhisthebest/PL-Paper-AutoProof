(** STLC call-by-value strong-normalization benchmark, Easy variant.
    Non-deterministic choice is included; if-then-else and recursion are not. *)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Relations.Relation_Definitions.
From Stdlib Require Import Lia.

Import ListNotations.

Module STLCNormalizationNondeterminismEasyTask.

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
Notation "'choice' t1 'or' t2" := (tm_choice t1 t2)
  (in custom stlc_tm at level 200,
   t1 custom stlc_tm,
   t2 custom stlc_tm at level 200,
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
  | tm_choice t1 t2 =>
      tm_choice (open_rec k u t1) (open_rec k u t2)
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
  | lc_choice : forall k t1 t2,
      lc_at k t1 ->
      lc_at k t2 ->
      lc_at k (tm_choice t1 t2).

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
  | ST_ChoiceLeft : forall t1 t2,
      locally_closed t1 ->
      locally_closed t2 ->
      tm_choice t1 t2 --> t1
  | ST_ChoiceRight : forall t1 t2,
      locally_closed t1 ->
      locally_closed t2 ->
      tm_choice t1 t2 --> t2
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
  | T_Choice : forall Gamma t1 t2 T,
      <{ Gamma |-- $(t1) \in T }> ->
      <{ Gamma |-- $(t2) \in T }> ->
      <{ Gamma |-- choice $(t1) or $(t2) \in T }>
where "<{ Gamma '|--' t '\in' T }>" := (has_type Gamma t T)
  : stlc_scope.

(** Target theorem: strong normalization for the supplied CBV relation. *)

Inductive strongly_normalizing : tm -> Prop :=
  | SN_intro : forall t,
      (forall t', t --> t' -> strongly_normalizing t') ->
      strongly_normalizing t.

(** Supplied logical relation and proof infrastructure. *)

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
  | tm_choice t1 t2 => tm_choice (msubst rho t1) (msubst rho t2)
  end.

Fixpoint free_vars (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_app t1 t2 => free_vars t1 ++ free_vars t2
  | tm_abs _ t1 => free_vars t1
  | tm_true => []
  | tm_false => []
  | tm_choice t1 t2 => free_vars t1 ++ free_vars t2
  end.

Fixpoint max_atom (L : list atom) : atom :=
  match L with
  | [] => 0
  | x :: L' => Nat.max x (max_atom L')
  end.

Definition fresh (L : list atom) : atom := S (max_atom L).

Definition proper_substitution (rho : term_substitution) : Prop :=
  forall x, locally_closed (rho x).

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

Lemma open_rec_preserves_lc_at : forall t k u,
  lc_at (S k) t ->
  locally_closed u ->
  lc_at k (open_rec k u t).
Proof.
  induction t; intros k u Hlc Hu; simpl in *; inversion Hlc; subst;
    eauto using lc_at.
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
    rewrite IHHlc2 by assumption. reflexivity.
  - rewrite IHHlc by lia. reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHHlc1 by assumption.
    rewrite IHHlc2 by assumption. reflexivity.
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

Lemma value_no_step : forall v,
  value v -> forall t, ~ (v --> t).
Proof.
  intros v Hv t Hstep. inversion Hv; subst; inversion Hstep.
Qed.

Lemma value_multi_eq : forall v t,
  value v -> v -->* t -> t = v.
Proof.
  intros v t Hv Hmulti. inversion Hmulti; subst.
  - reflexivity.
  - exfalso. eapply value_no_step; eauto.
Qed.

(** Supplied fundamental theorem. *)

(* Reducibility is indexed by the type.  In addition to termination, the
   relation records closure, which the choice rules require. *)
Fixpoint reducible (T : ty) (t : tm) : Prop :=
  match T with
  | Ty_Bool => locally_closed t /\ strongly_normalizing t
  | Ty_Arrow A B => locally_closed t /\ strongly_normalizing t /\
      (forall u, reducible A u -> reducible B (tm_app t u))
  end.

Definition realizes (Gamma : context) (rho : term_substitution) : Prop :=
  proper_substitution rho /\
  (forall x T, Gamma x = Some T -> reducible T (rho x)).

Lemma sn_from_steps : forall t,
  (forall t', t --> t' -> strongly_normalizing t') -> strongly_normalizing t.
Proof. constructor; auto. Qed.

Lemma sn_step_inv : forall t t',
  strongly_normalizing t -> t --> t' -> strongly_normalizing t'.
Proof. intros t t' H; inversion H; subst; auto. Qed.

Lemma lc_step : forall t t', t --> t' ->
  locally_closed t -> locally_closed t'.
Proof.
  intros t t' Hs. induction Hs; intros Hlc.
  - eapply open_preserves_term.
    + inversion H; subst. assumption.
    + eapply value_regular; eassumption.
  - inversion Hlc; subst. constructor; [eapply IHHs; eassumption|assumption].
  - inversion Hlc; subst. constructor; [assumption|eapply IHHs; eassumption].
  - inversion Hlc; subst. assumption.
  - inversion Hlc; subst. assumption.
Qed.

Lemma reducible_lc : forall T t, reducible T t -> locally_closed t.
Proof. intros T; destruct T; simpl; intros t H; tauto. Qed.

Lemma reducible_step : forall T t t',
  reducible T t -> t --> t' -> reducible T t'.
Proof.
  induction T; intros t t' Hr Hs; simpl in *.
  - destruct Hr as [Hlc Hsn]. split; [eapply lc_step|eapply sn_step_inv]; eauto.
  - destruct Hr as [Hlc [Hsn Happ]]. split.
    + eapply lc_step; eauto.
    + split.
      * eapply sn_step_inv; eauto.
      * intros u Hu. eapply IHT2.
        -- apply Happ. exact Hu.
        -- apply ST_App1; [exact Hs|eapply reducible_lc; eauto].
Qed.

Lemma reducible_sn : forall T t, reducible T t -> strongly_normalizing t.
Proof. intros T; destruct T; simpl; intros t H; tauto. Qed.

Lemma reducible_expand : forall T t,
  locally_closed t -> (forall t', t --> t' -> reducible T t') ->
  ~ value t -> reducible T t.
Proof.
  induction T as [|A B IHA IHB]; intros t Hlc Hred Hnv; simpl.
  - split; [assumption|]. constructor. intros t' Hs.
    eapply reducible_sn. eapply Hred; eauto.
  - split; [assumption|]. split.
    + constructor. intros t' Hs. eapply reducible_sn. eapply Hred; eauto.
    + intros u Hu.
      assert (Husn : strongly_normalizing u) by (eapply reducible_sn; eauto).
      revert Hu. induction Husn as [u Hsteps IH]; intros Hu.
      apply IHB.
      * constructor; [assumption|eapply reducible_lc; eauto].
      * intros z Hz. inversion Hz; subst.
        -- exfalso. apply Hnv. eapply v_abs; eassumption.
        -- specialize (Hred t1' H1) as Hrt.
           destruct Hrt as [_ [_ Hfun]]. apply Hfun. exact Hu.
        -- eapply IH; eauto using reducible_step.
      * intro Hv. inversion Hv.
Qed.

Lemma reducible_fvar : forall T x, reducible T (tm_fvar x).
Proof.
  intros T. induction T as [|A B IHA IHB]; intros x; simpl.
  - split; [apply lc_fvar|]. constructor. intros t Hs. inversion Hs.
  - split; [apply lc_fvar|]. split.
    + constructor. intros t Hs. inversion Hs.
    + intros u Hu. eapply reducible_expand.
      * constructor; [apply lc_fvar|eapply reducible_lc; eauto].
      * intros z Hz. inversion Hz; subst; try solve [inversion H1]; try solve [inversion H2].
      * intro Hv. inversion Hv.
Qed.

Lemma reducible_app_abs : forall A B T b u,
  locally_closed (tm_abs T b) -> reducible A u ->
  (forall v, reducible A v -> reducible B (open b v)) ->
  reducible B (tm_app (tm_abs T b) u).
Proof.
  intros A B T b u Hlc Hu Hbody.
  assert (Husn : strongly_normalizing u) by (eapply reducible_sn; eauto).
  revert Hu. induction Husn as [u Hsteps IH]; intros Hu.
  eapply reducible_expand.
  - constructor; [exact Hlc|eapply reducible_lc; eauto].
  - intros z Hz. inversion Hz; subst.
    + eapply Hbody; eauto.
    + exfalso. eapply value_no_step; eauto using v_abs.
    + eapply IH; eauto using reducible_step.
  - intro Hv. inversion Hv.
Qed.

Lemma sn_app_abs : forall A B T b u,
  locally_closed (tm_abs T b) -> strongly_normalizing u -> reducible A u ->
  (forall v, reducible A v -> reducible B (open b v)) ->
  strongly_normalizing (tm_app (tm_abs T b) u).
Proof.
  intros A B T b u Hlc Hu Hru. revert b T Hlc Hru.
  induction Hu as [u Hsteps IH]; intros b T Hlc Hru Hbody.
  constructor. intros z Hz. inversion Hz; subst.
  - eapply reducible_sn. eapply Hbody; eauto.
  - exfalso. eapply value_no_step; eauto using v_abs.
  - eapply IH; eauto using reducible_step.
Qed.

Lemma sn_choice : forall a b,
  locally_closed a -> locally_closed b ->
  strongly_normalizing a -> strongly_normalizing b ->
  strongly_normalizing (tm_choice a b).
Proof.
  intros a b Hla Hlb Ha Hb. constructor. intros z Hz.
  inversion Hz; subst; assumption.
Qed.

Lemma sn_choice_app : forall a b u,
  locally_closed a -> locally_closed b -> locally_closed u ->
  strongly_normalizing (tm_app a u) ->
  strongly_normalizing (tm_app b u) ->
  strongly_normalizing (tm_app (tm_choice a b) u).
Proof.
  intros a b u Hla Hlb Hu Hab Hbb. constructor. intros z Hz.
  inversion Hz; subst.
  - inversion H1; subst; assumption.
  - inversion H1.
Qed.

Lemma msubst_open_rec_update : forall t k rho x u,
  ~ In x (free_vars t) -> proper_substitution rho -> locally_closed u ->
  msubst (subst_update rho x u) (open_rec k (tm_fvar x) t) =
  open_rec k u (msubst rho t).
Proof.
  induction t; intros k rho x u Hfresh Hr Hu; simpl in *.
  - destruct (Nat.eqb k n) eqn:E; simpl.
    + unfold subst_update. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - assert (a <> x) by (intro E; subst; apply Hfresh; simpl; auto).
    assert (Nat.eqb x a = false) as E by (apply Nat.eqb_neq; congruence).
    unfold subst_update. rewrite E. rewrite open_rec_term; auto using Hr.
  - apply notin_app_split in Hfresh as [H1 H2].
    rewrite (IHt1 k rho x u H1 Hr Hu), (IHt2 k rho x u H2 Hr Hu). reflexivity.
  - f_equal. apply (IHt (S k)); auto.
  - reflexivity.
  - reflexivity.
  - apply notin_app_split in Hfresh as [H1 H2].
    rewrite (IHt1 k rho x u H1 Hr Hu), (IHt2 k rho x u H2 Hr Hu). reflexivity.
Qed.

Lemma msubst_open_update : forall t rho x u,
  ~ In x (free_vars t) -> proper_substitution rho -> locally_closed u ->
  msubst (subst_update rho x u) (open t (tm_fvar x)) =
  open (msubst rho t) u.
Proof.
  intros. unfold open. apply msubst_open_rec_update; assumption.
Qed.

Lemma realizes_update : forall Gamma rho x A u,
  realizes Gamma rho -> reducible A u ->
  realizes (update Gamma x A) (subst_update rho x u).
Proof.
  intros Gamma rho x A u [Hp Hr] Hu. split.
  - eapply proper_update; eauto using reducible_lc.
  - unfold update, subst_update. intros y T Hlookup.
    destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst y. simpl in Hlookup. inversion Hlookup; subst. exact Hu.
    + simpl in Hlookup. eapply Hr; eauto.
Qed.

Lemma realizes_proper : forall Gamma rho,
  realizes Gamma rho -> proper_substitution rho.
Proof.
  intros Gamma rho [Hp Hr]. exact Hp.
Qed.

Theorem fundamental : forall Gamma t T,
  <{ Gamma |-- t \in T }> -> forall rho,
  realizes Gamma rho -> reducible T (msubst rho t).
Proof.
  intros Gamma t T Hty. induction Hty; intros rho Hreal; simpl.
  - destruct Hreal as [_ Hreal]. eapply Hreal; eauto.
  - set (x := fresh (L ++ free_vars t1)).
    assert (Hnot : ~ In x (L ++ free_vars t1)) by (unfold x; apply fresh_notin).
    apply notin_app_split in Hnot as [HnotL HnotFV].
    set (body := msubst rho t1).
    assert (Hproper : proper_substitution rho) by (eapply realizes_proper; eauto).
    assert (Hbody0 : reducible T2 (open body (tm_fvar x))).
    { specialize (H0 x HnotL (subst_update rho x (tm_fvar x)) (realizes_update Gamma rho x T1
          (tm_fvar x) Hreal (reducible_fvar T1 x))).
      pose proof (msubst_open_update t1 rho x (tm_fvar x)
        HnotFV Hproper (lc_fvar 0 x)) as Heq.
      rewrite Heq in H0. unfold body. exact H0. }
    assert (Habs_lc : locally_closed (tm_abs T1 body)).
    { apply lc_abs. assert (Hopenlc : lc_at 0 (open body (tm_fvar x)))
        by exact (reducible_lc _ _ Hbody0).
      eapply lc_at_open_inv; exact Hopenlc. }
    split.
    + exact Habs_lc.
    + split.
      * constructor. intros z Hz. inversion Hz.
      * intros u Hu. eapply reducible_app_abs with (A := T1) (B := T2).
        -- exact Habs_lc.
        -- exact Hu.
        -- intros v Hv. specialize (H0 x HnotL (subst_update rho x v)
             (realizes_update Gamma rho x T1 v Hreal Hv)).
           pose proof (msubst_open_update t1 rho x v HnotFV Hproper
             (reducible_lc _ _ Hv)) as Heq.
           rewrite Heq in H0. unfold body. exact H0.
  - destruct (IHHty1 rho Hreal) as [_ [_ Hfun]].
    apply Hfun. apply IHHty2. exact Hreal.
  - split; [constructor|constructor; intros t H; inversion H].
  - split; [constructor|constructor; intros t H; inversion H].
  - pose proof (IHHty1 rho Hreal) as Hr1.
    pose proof (IHHty2 rho Hreal) as Hr2.
    eapply reducible_expand.
    + constructor; [eapply reducible_lc; eauto|eapply reducible_lc; eauto].
    + intros t' Hs. inversion Hs; subst; assumption.
    + intro Hv. inversion Hv.
Qed.

Lemma msubst_id : forall t, msubst id_substitution t = t.
Proof. induction t; simpl; f_equal; auto. Qed.

Theorem strong_normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  assert (Hreal : realizes empty id_substitution).
  { split; [apply id_substitution_proper|]. intros x U Hlookup. discriminate. }
  pose proof (fundamental empty t T Hty id_substitution Hreal) as Hred.
  replace (msubst id_substitution t) with t in Hred.
  - eapply reducible_sn; eauto.
  - symmetry. apply msubst_id.
Qed.

End STLCNormalizationNondeterminismEasyTask.
