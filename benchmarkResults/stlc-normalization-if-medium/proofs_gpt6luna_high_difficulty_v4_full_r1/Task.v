(** STLC call-by-value strong-normalization benchmark, Easy variant.
    If-then-else is included; non-determinism and recursion are not. *)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Relations.Relation_Definitions.
From Stdlib Require Import Lia.

Import ListNotations.

Module STLCNormalizationIfEasyTask.

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

Fixpoint free_vars (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_app t1 t2 => free_vars t1 ++ free_vars t2
  | tm_abs _ t1 => free_vars t1
  | tm_true => []
  | tm_false => []
  | tm_if t1 t2 t3 => free_vars t1 ++ free_vars t2 ++ free_vars t3
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
  | tm_if t1 t2 t3 =>
      tm_if (msubst rho t1) (msubst rho t2) (msubst rho t3)
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

Lemma multi_if : forall t1 t1' t2 t3,
  t1 -->* t1' ->
  locally_closed t2 ->
  locally_closed t3 ->
  tm_if t1 t2 t3 -->* tm_if t1' t2 t3.
Proof.
  intros t1 t1' t2 t3 Hs Ht2 Ht3.
  induction Hs.
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_If; eauto.
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
  - inversion Hlc; subst. eauto using lc_at.
Qed.

Lemma lc_at_open_rec : forall t j,
  lc_at (S j) t -> forall u, lc_at j u -> lc_at j (open_rec j u t).
Proof.
  induction t as [n|x|t1 IH1 t2 IH2|T t IH| | |t1 IH1 t2 IH2 t3 IH3];
    intros j Ht u Hu; simpl.
  - inversion Ht; subst. destruct (Nat.eqb j n) eqn:E.
    + exact Hu.
    + apply lc_bvar. apply Nat.eqb_neq in E. lia.
  - constructor.
  - inversion Ht; subst. eapply lc_app; [eapply IH1|eapply IH2]; eauto.
  - inversion Ht; subst. apply lc_abs. eapply IH; eauto.
    eapply lc_at_weaken; eauto; lia.
  - constructor.
  - constructor.
  - inversion Ht; subst. eapply lc_if; [eapply IH1|eapply IH2|eapply IH3]; eauto.
Qed.

Lemma lc_step : forall t t', locally_closed t -> t --> t' -> locally_closed t'.
Proof.
  intros t t' Hlc Hst. induction Hst; unfold locally_closed in *.
  - inversion Hlc; subst. inversion H; subst.
    match goal with Hb : lc_at 1 ?b |- _ =>
      eapply lc_at_open_rec with (t:=b) (j:=0); [exact Hb|]
    end.
    eapply value_regular; exact H0.
  - inversion Hlc; subst. eapply lc_app; eauto.
  - inversion Hlc; subst. eapply lc_app; eauto.
  - inversion Hlc; assumption.
  - inversion Hlc; assumption.
  - inversion Hlc; subst. eapply lc_if; eauto.
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
  - rewrite IHHlc1 by assumption.
    rewrite IHHlc2 by assumption.
    rewrite IHHlc3 by assumption.
    reflexivity.
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

Lemma sn_step_inv : forall t t',
  strongly_normalizing t -> t --> t' -> strongly_normalizing t'.
Proof. intros t t' Hsn Hstep. inversion Hsn; subst; eauto. Qed.

Lemma sn_app_left : forall t t',
  strongly_normalizing (tm_app t tm_true) -> t --> t' ->
  strongly_normalizing (tm_app t' tm_true).
Proof.
  intros. eapply sn_step_inv; [exact H|]. apply ST_App1; auto.
  unfold locally_closed. apply lc_true.
Qed.

Lemma msubst_open_fvar_rec : forall t k x rho,
  proper_substitution rho ->
  msubst rho (open_rec k (tm_fvar x) t) =
  open_rec k (rho x) (msubst rho t).
Proof.
  induction t as [n|x|t1 IH1 t2 IH2|T t IH| | |t1 IH1 t2 IH2 t3 IH3];
    intros k z rho Hproper; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - unfold proper_substitution in Hproper.
    rewrite (open_rec_term (rho x) k (rho z)) by apply Hproper.
    reflexivity.
  - rewrite IH1, IH2; auto.
  - rewrite IH; auto.
  - reflexivity.
  - reflexivity.
  - rewrite IH1, IH2, IH3; auto.
Qed.

Lemma msubst_subst_update_fresh : forall rho x v t,
  ~ In x (free_vars t) ->
  msubst (subst_update rho x v) t = msubst rho t.
Proof.
  induction t as [n|y|t1 IH1 t2 IH2|T t IH| | |t1 IH1 t2 IH2 t3 IH3];
    intros H; simpl in *.
  - reflexivity.
  - simpl in H. destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply H. simpl. auto.
    + unfold subst_update. rewrite E. reflexivity.
  - apply notin_app_split in H as [H1 H2]. rewrite IH1, IH2; auto.
  - f_equal. apply IH. exact H.
  - reflexivity.
  - reflexivity.
  - apply notin_app_split in H as [H1 H23].
    apply notin_app_split in H23 as [H2 H3].
    rewrite IH1, IH2, IH3; auto.
Qed.

Lemma msubst_open_subst : forall t x v rho,
  proper_substitution rho ->
  locally_closed v ->
  ~ In x (free_vars t) ->
  msubst (subst_update rho x v) (open t (tm_fvar x)) =
  open (msubst rho t) v.
Proof.
  intros t x v rho Hp Hv Hfresh.
  unfold open.
  rewrite msubst_open_fvar_rec.
  - rewrite msubst_subst_update_fresh by exact Hfresh.
    unfold subst_update. rewrite Nat.eqb_refl. reflexivity.
  - eapply proper_update; eauto.
Qed.

Fixpoint reducible (T : ty) (t : tm) : Prop :=
  locally_closed t /\ strongly_normalizing t /\
  match T with
  | Ty_Bool => True
  | Ty_Arrow A B => forall u, reducible A u -> reducible B (tm_app t u)
  end.

Definition env_related (Gamma : context) (rho : term_substitution) : Prop :=
  forall x T, Gamma x = Some T -> reducible T (rho x).

Definition neutral (t : tm) : Prop :=
  locally_closed t /\ (forall t', ~ t --> t') /\ ~ value t.

Lemma reducible_lc : forall T t, reducible T t -> locally_closed t.
Proof.
  intros [|A B] t H; simpl in H; tauto.
Qed.

Lemma reducible_sn : forall T t, reducible T t -> strongly_normalizing t.
Proof.
  intros [|A B] t H; simpl in H; tauto.
Qed.

Lemma reducible_step : forall T t t',
  reducible T t -> t --> t' -> reducible T t'.
Proof.
  induction T as [|A IHA B IHB]; intros t t' Hred Hst.
  - change (locally_closed t /\ strongly_normalizing t /\ True) in Hred.
    destruct Hred as [Hlc [Hsn _]].
    change (locally_closed t' /\ strongly_normalizing t' /\ True).
    split; [eapply lc_step; eauto|]. split; [eapply sn_step_inv; eauto|exact I].
  - change (locally_closed t /\ strongly_normalizing t /\
      (forall u, reducible A u -> reducible B (tm_app t u))) in Hred.
    destruct Hred as [Hlc [Hsn Hrel]].
    change (locally_closed t' /\ strongly_normalizing t' /\
      (forall u, reducible A u -> reducible B (tm_app t' u))).
    split; [eapply lc_step; eauto|]. split; [eapply sn_step_inv; eauto|].
    intros u Hu. eapply IHB.
    + apply Hrel. exact Hu.
    + apply ST_App1; [exact Hst|apply reducible_lc with (T:=A); exact Hu].
Qed.

Lemma reducible_arrow_app : forall A B t u,
  reducible (Ty_Arrow A B) t -> reducible A u ->
  reducible B (tm_app t u).
Proof.
  intros. simpl in H. eapply H; eassumption.
Qed.

Lemma sn_from_steps : forall t,
  (forall t', t --> t' -> strongly_normalizing t') ->
  strongly_normalizing t.
Proof. intros; constructor; auto. Qed.

Lemma reducible_expand : forall T t,
  locally_closed t -> strongly_normalizing t -> ~ value t ->
  (forall t', t --> t' -> reducible T t') -> reducible T t.
Proof.
  induction T as [|A IHA B IHB]; intros t Hlc Hsn Hnv Hred.
  - change (locally_closed t /\ strongly_normalizing t /\ True).
    split; [exact Hlc|]. split; [exact Hsn|exact I].
  - change (locally_closed t /\ strongly_normalizing t /\
      (forall u, reducible A u -> reducible B (tm_app t u))).
    split; [exact Hlc|]. split; [exact Hsn|].
    intros u Hu.
    assert (Happsn : strongly_normalizing (tm_app t u)).
    { apply sn_from_steps. intros z Hz. inversion Hz; subst.
      - exfalso. apply Hnv. econstructor; eauto.
      - eapply reducible_sn. eapply reducible_arrow_app; [eapply Hred; eassumption|exact Hu].
      - exfalso. apply Hnv. eassumption.
    }
    eapply IHB.
    + unfold locally_closed. eapply lc_app; [exact Hlc|].
      exact (reducible_lc _ _ Hu).
    + exact Happsn.
    + intro Hval. inversion Hval.
    + intros z Hz. inversion Hz; subst.
      * exfalso. apply Hnv. econstructor; eauto.
      * eapply reducible_arrow_app; [eapply Hred; eassumption|exact Hu].
      * exfalso. apply Hnv. eassumption.
Qed.

Lemma sn_if : forall t t1 t2,
  strongly_normalizing t -> strongly_normalizing t1 ->
  strongly_normalizing t2 -> locally_closed t1 -> locally_closed t2 ->
  strongly_normalizing (tm_if t t1 t2).
Proof.
  intros t t1 t2 Hsn.
  induction Hsn as [t Hsteps IH]; intros Hsn1 Hsn2 Hlc1 Hlc2.
  constructor. intros z Hz. inversion Hz; subst.
  - assumption.
  - assumption.
  - eapply IH; eauto.
Qed.

Lemma reducible_if : forall T c t1 t2,
  locally_closed c -> strongly_normalizing c ->
  reducible T t1 -> reducible T t2 ->
  reducible T (tm_if c t1 t2).
Proof.
  intros T c t1 t2 Hlc Hsn.
  induction Hsn as [c Hnext IH]; intros Hred1 Hred2.
  eapply reducible_expand.
  - unfold locally_closed. eapply lc_if.
    + exact Hlc.
    + exact (reducible_lc _ _ Hred1).
    + exact (reducible_lc _ _ Hred2).
  - assert (Hsnc : strongly_normalizing c).
    { constructor. exact Hnext. }
    eapply sn_if; [exact Hsnc| | | |].
    + apply reducible_sn with (T:=T). exact Hred1.
    + apply reducible_sn with (T:=T). exact Hred2.
    + apply reducible_lc with (T:=T). exact Hred1.
    + apply reducible_lc with (T:=T). exact Hred2.
  - intro Hv. inversion Hv.
  - intros z Hz. inversion Hz; subst.
    + exact Hred1.
    + exact Hred2.
    + eapply IH.
      * eassumption.
      * eapply lc_step; [exact Hlc|eassumption].
      * exact Hred1.
      * exact Hred2.
Qed.

Lemma reducible_abs_app : forall A B body,
  locally_closed (tm_abs A body) ->
  (forall u, reducible A u -> reducible B (open body u)) ->
  forall u, reducible A u -> reducible B (tm_app (tm_abs A body) u).
Proof.
  intros A B body Habs Hbody.
  assert (P : forall u, strongly_normalizing u -> reducible A u ->
      reducible B (tm_app (tm_abs A body) u)).
  { intros u Hsn. induction Hsn as [u Hnext IH]. intros Hu.
    assert (Hlc : locally_closed (tm_app (tm_abs A body) u)).
    { unfold locally_closed. eapply lc_app; [exact Habs|].
      eapply reducible_lc; eauto. }
    assert (Happsn : strongly_normalizing (tm_app (tm_abs A body) u)).
    { apply sn_from_steps. intros z Hz. inversion Hz; subst.
      - apply reducible_sn with (T:=B). apply Hbody. exact Hu.
      - exfalso. inversion H1.
      - apply reducible_sn with (T:=B). apply IH; [eassumption|].
        eapply reducible_step; eauto.
    }
    eapply reducible_expand; [exact Hlc|exact Happsn| |].
    - intro Hv. inversion Hv.
    - intros z Hz. inversion Hz; subst.
      + apply Hbody. exact Hu.
      + exfalso. inversion H1.
      + apply IH; [eassumption|]. eapply reducible_step; eauto.
  }
  intros u Hu. apply P; [eapply reducible_sn; eauto|exact Hu].
Qed.

Lemma neutral_fvar : forall x, neutral (tm_fvar x).
Proof.
  intros. split; [unfold locally_closed; apply lc_fvar|]. split.
  - intros t' H; inversion H.
  - intro H; inversion H.
Qed.

Lemma neutral_app : forall t u,
  neutral t -> locally_closed u -> neutral (tm_app t u).
Proof.
  intros t u [Hlc [Hstep Hval]] Hu. split.
  - unfold locally_closed in *. eapply lc_app; eauto.
  - split.
    + intros z Hz. inversion Hz; subst; eauto.
      all: try (exfalso; eapply Hstep; eassumption).
      all: try (exfalso; eapply Hval; eassumption).
      all: try (exfalso; apply Hval; econstructor; eauto).
    + intro Hv. inversion Hv.
Qed.

Lemma reducible_neutral : forall T t,
  neutral t -> reducible T t.
Proof.
  induction T as [|A IHA B IHB]; intros t Hn.
  - destruct Hn as [Hlc [Hstep Hval]]. split; [exact Hlc|]. split.
    + constructor. intros t' H; exfalso; eapply Hstep; eauto.
    + exact I.
  - destruct Hn as [Hlc [Hstep Hval]]. split; [exact Hlc|]. split.
    + constructor. intros t' H; exfalso; eapply Hstep; eauto.
    + intros u Hu. apply IHB.
      assert (Hnt : neutral t) by (repeat split; assumption).
      eapply neutral_app; [exact Hnt|].
      eapply reducible_lc; eauto.
Qed.

Lemma env_related_update : forall Gamma rho x A u,
  env_related Gamma rho -> reducible A u ->
  env_related (update Gamma x A) (subst_update rho x u).
Proof.
  intros Gamma rho x A u Henv Hu y T Hlook.
  unfold update, subst_update in *.
  destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. subst y. simpl in Hlook. inversion Hlook; subst T.
    exact Hu.
  - specialize (Henv y T Hlook). exact Henv.
Qed.

Lemma msubst_id : forall t, msubst id_substitution t = t.
Proof. unfold id_substitution. induction t; simpl; try rewrite IHt; try rewrite IHt1;
  try rewrite IHt2; try rewrite IHt3; reflexivity. Qed.

Theorem fundamental : forall Gamma t T,
  has_type Gamma t T -> forall rho,
  proper_substitution rho -> env_related Gamma rho ->
  reducible T (msubst rho t).
Proof.
  intros Gamma t T HT. induction HT; intros rho Hproper Henv.
  - simpl. eapply Henv; eauto.
  - simpl. assert (Hfresh : ~ In (fresh (L ++ free_vars t1)) L).
    { intro Hin. apply fresh_notin with (L:=L ++ free_vars t1).
      apply in_or_app. left. exact Hin. }
    assert (Hfreshfv : ~ In (fresh (L ++ free_vars t1)) (free_vars t1)).
    { intro Hin. apply fresh_notin with (L:=L ++ free_vars t1).
      apply in_or_app. right. exact Hin. }
    set (x := fresh (L ++ free_vars t1)).
    assert (Hxl : ~ In x L) by (unfold x; exact Hfresh).
    assert (Hxfv : ~ In x (free_vars t1)) by (unfold x; exact Hfreshfv).
    assert (Hbody : forall u, reducible T1 u ->
        reducible T2 (open (msubst rho t1) u)).
    { intros u Hu.
      assert (Hproper' : proper_substitution (subst_update rho x u)).
      { apply proper_update; [exact Hproper|]. eapply reducible_lc; eauto. }
      assert (Henv' : env_related (update Gamma x T1) (subst_update rho x u)).
      { eapply env_related_update; eauto. }
      specialize (H0 x Hxl (subst_update rho x u) Hproper' Henv').
      rewrite (msubst_open_subst t1 x u rho Hproper (reducible_lc _ _ Hu) Hxfv)
        in H0.
      exact H0.
    }
    assert (Hfx : reducible T1 (tm_fvar x)).
    { apply reducible_neutral. apply neutral_fvar. }
    pose proof (Hbody (tm_fvar x) Hfx) as Hopened.
    pose proof (reducible_lc _ _ Hopened) as Hopenlc.
    unfold locally_closed, open in Hopenlc.
    assert (Hbodylc : lc_at 1 (msubst rho t1)).
    { eapply lc_at_open_inv; exact Hopenlc. }
    split.
    + unfold locally_closed. apply lc_abs. exact Hbodylc.
    + split.
      * constructor. intros z Hz. inversion Hz.
      * intros u Hu. simpl. eapply reducible_abs_app.
        -- unfold locally_closed. apply lc_abs. exact Hbodylc.
        -- exact Hbody.
        -- exact Hu.
  - simpl. specialize (IHHT1 rho Hproper Henv).
    specialize (IHHT2 rho Hproper Henv).
    change (reducible (Ty_Arrow T1 T2) (msubst rho t1)) in IHHT1.
    eapply reducible_arrow_app; eauto.
  - simpl. split; [unfold locally_closed; apply lc_true|].
    split; [constructor; intros z Hz; inversion Hz|exact I].
  - simpl. split; [unfold locally_closed; apply lc_false|].
    split; [constructor; intros z Hz; inversion Hz|exact I].
  - simpl. specialize (IHHT1 rho Hproper Henv).
    specialize (IHHT2 rho Hproper Henv).
    specialize (IHHT3 rho Hproper Henv).
    destruct IHHT1 as [Hclc [Hsnc _]].
    eapply reducible_if; eauto.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  assert (Henv : env_related empty id_substitution).
  { intros x U Hlookup. discriminate. }
  pose proof (fundamental empty t T Hty id_substitution
    id_substitution_proper Henv) as Hred.
  rewrite msubst_id in Hred.
  eapply reducible_sn. exact Hred.
Qed.

End STLCNormalizationIfEasyTask.
