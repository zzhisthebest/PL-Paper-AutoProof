(** STLC call-by-value strong-normalization benchmark.
    Non-deterministic choice is included; if-then-else and recursion are not. *)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Relations.Relation_Definitions.
From Stdlib Require Import Lia.

Module STLCNormalizationNondeterminismHardTask.

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

(** Local closure and opening. *)

Lemma lc_weaken : forall k t, lc_at k t -> forall j, k <= j -> lc_at j t.
Proof.
  intros k t H; induction H; intros j Hj; try (constructor; eauto; fail).
  - constructor; lia.
  - constructor. apply IHlc_at. lia.
Qed.

Lemma open_lc : forall t k u,
  lc_at (S k) t -> lc_at k u -> lc_at k (open_rec k u t).
Proof.
  induction t; intros k u Ht Hu; inversion Ht; subst; simpl;
    try (constructor; eauto; fail).
  - destruct (Nat.eqb_spec k n); subst; auto.
    constructor; lia.
  - constructor. eapply IHt; eauto.
    eapply lc_weaken; eauto.
Qed.

Lemma open_lc_reverse : forall t k x,
  lc_at k (open_rec k (tm_fvar x) t) -> lc_at (S k) t.
Proof.
  induction t; intros k x H; simpl in H;
    try (inversion H; subst; constructor; eauto; fail).
  - destruct (Nat.eqb_spec k n); subst.
    + constructor; lia.
    + inversion H; subst. constructor; lia.
Qed.

Lemma value_lc : forall v, value v -> locally_closed v.
Proof. intros v H; inversion H; subst; auto; constructor. Qed.

Lemma step_lc : forall t t', t --> t' -> locally_closed t -> locally_closed t'.
Proof.
  intros t t' H; induction H; intro Hlc; inversion Hlc; subst.
  - inversion H; subst. apply open_lc; auto.
  - constructor; auto. apply IHstep; assumption.
  - constructor; auto. apply IHstep; assumption.
  - assumption.
  - assumption.
Qed.

Lemma sn_step : forall t t', strongly_normalizing t -> t --> t' ->
  strongly_normalizing t'.
Proof. intros t t' Hsn Hstep; inversion Hsn; eauto. Qed.

Lemma list_bound : forall (L : list nat) n,
  In n L -> n <= fold_right Nat.max 0 L.
Proof.
  induction L as [|a L IH]; intros n H; simpl in *.
  - contradiction.
  - destruct H as [H | H]; subst.
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; exact H | apply Nat.le_max_r].
Qed.

Lemma fresh_atom : forall L : list atom, exists x, ~ In x L.
Proof.
  intro L. exists (S (fold_right Nat.max 0 L)).
  intro H. pose proof (list_bound L _ H). lia.
Qed.

Lemma typing_lc : forall Gamma t T, has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T H; induction H; try (constructor; eauto; fail).
  - destruct (fresh_atom L) as [x Hx].
    specialize (H0 x Hx).
    constructor. apply open_lc_reverse with (x := x). exact H0.
Qed.

Fixpoint fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ => nil
  | tm_fvar x => x :: nil
  | tm_app t1 t2 => fv t1 ++ fv t2
  | tm_abs _ b => fv b
  | tm_true | tm_false => nil
  | tm_choice t1 t2 => fv t1 ++ fv t2
  end.

Definition renv := atom -> tm.
Definition extend (rho : renv) (x : atom) (u : tm) : renv :=
  fun y => if Nat.eqb x y then u else rho y.

Fixpoint instantiate (rho : renv) (t : tm) : tm :=
  match t with
  | tm_bvar n => tm_bvar n
  | tm_fvar x => rho x
  | tm_app t1 t2 => tm_app (instantiate rho t1) (instantiate rho t2)
  | tm_abs T b => tm_abs T (instantiate rho b)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_choice t1 t2 => tm_choice (instantiate rho t1) (instantiate rho t2)
  end.

Lemma instantiate_lc : forall k t rho,
  lc_at k t -> (forall x, locally_closed (rho x)) ->
  lc_at k (instantiate rho t).
Proof.
  intros k t rho Ht; induction Ht; intro Hr; simpl;
    try (constructor; eauto).
  eapply lc_weaken; [apply Hr | lia].
Qed.

Lemma open_lc_identity : forall t k u,
  lc_at k t -> open_rec k u t = t.
Proof.
  induction t; intros k u H; inversion H; subst; simpl;
    try (f_equal; eauto; fail); auto.
  destruct (Nat.eqb_spec k n); subst; lia || reflexivity.
Qed.

Lemma instantiate_open : forall t k rho x u,
  ~ In x (fv t) ->
  (forall y, locally_closed (rho y)) ->
  instantiate (extend rho x u) (open_rec k (tm_fvar x) t) =
  open_rec k u (instantiate rho t).
Proof.
  induction t; intros k rho x u Hfresh Hr; simpl in *; try reflexivity.
  - destruct (Nat.eqb_spec k n); subst; simpl.
    + unfold extend. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - assert (x <> a) by (intro Heq; subst; apply Hfresh; simpl; auto).
    unfold extend. destruct (Nat.eqb_spec x a); [congruence|].
    symmetry. apply open_lc_identity. eapply lc_weaken; [apply Hr | lia].
  - assert (H1 : ~ In x (fv t1)) by (intro H; apply Hfresh; apply in_or_app; left; exact H).
    assert (H2 : ~ In x (fv t2)) by (intro H; apply Hfresh; apply in_or_app; right; exact H).
    rewrite (IHt1 k rho x u H1 Hr), (IHt2 k rho x u H2 Hr). reflexivity.
  - f_equal. apply IHt. exact Hfresh. exact Hr.
  - assert (H1 : ~ In x (fv t1)) by (intro H; apply Hfresh; apply in_or_app; left; exact H).
    assert (H2 : ~ In x (fv t2)) by (intro H; apply Hfresh; apply in_or_app; right; exact H).
    rewrite (IHt1 k rho x u H1 Hr), (IHt2 k rho x u H2 Hr). reflexivity.
Qed.

(** The type-indexed candidate.  Its arrow clause speaks about applications,
    so it covers all call-by-value evaluation paths of a function. *)
Fixpoint reducible (T : ty) (t : tm) : Prop :=
  locally_closed t /\ strongly_normalizing t /\
  match T with
  | Ty_Bool => True
  | Ty_Arrow A B => forall u, reducible A u -> reducible B (tm_app t u)
  end.

Lemma reducible_lc : forall T t, reducible T t -> locally_closed t.
Proof. intros T t H; destruct T; simpl in H; exact (proj1 H). Qed.

Lemma reducible_sn : forall T t, reducible T t -> strongly_normalizing t.
Proof. intros T t H; destruct T; simpl in H; exact (proj1 (proj2 H)). Qed.

Lemma reducible_step : forall T t t', reducible T t -> t --> t' -> reducible T t'.
Proof.
  induction T as [|A IHA B IHB]; intros t t' Hr Hstep;
    destruct Hr as [Hlc [Hsn Hfun]]; simpl in *.
  - split.
    + eapply step_lc; eauto.
    + split; [eapply sn_step; eauto | exact I].
  - split.
    + eapply step_lc; eauto.
    + split.
      * eapply sn_step; eauto.
      * intros u Hu. apply IHB with (t := tm_app t u).
        -- apply Hfun; auto.
        -- apply ST_App1; auto. apply reducible_lc with A; auto.
Qed.

Lemma value_no_step : forall v t', value v -> v --> t' -> False.
Proof. intros v t' Hv Hs; inversion Hv; subst; inversion Hs. Qed.

Lemma neutral_expand : forall T t,
  locally_closed t -> ~ value t ->
  (forall t', t --> t' -> reducible T t') -> reducible T t.
Proof.
  induction T as [|A IHA B IHB]; intros t Hlc Hnv Hnext; simpl.
  - split; [exact Hlc |]. split; [|exact I].
    constructor. intros t' Hs.
    apply reducible_sn with Ty_Bool. apply Hnext; auto.
  - split; [exact Hlc |]. split.
    + constructor. intros t' Hs.
      apply reducible_sn with (Ty_Arrow A B). apply Hnext; auto.
    + intros u Hu. apply IHB.
      * constructor; auto. apply reducible_lc with A; auto.
      * intro Hv. inversion Hv.
      * intros q Hs. inversion Hs; subst.
        -- exfalso. apply Hnv. constructor. assumption.
        -- destruct (Hnext _ H1) as [_ [_ Hf]]. apply Hf; auto.
        -- exfalso. apply Hnv. assumption.
Qed.

Lemma beta_expand : forall A B b u,
  locally_closed (tm_abs A b) -> reducible A u ->
  (forall w, reducible A w -> reducible B (open b w)) ->
  reducible B (tm_app (tm_abs A b) u).
Proof.
  intros A B b u Habs Hu Hbody.
  pose proof (reducible_sn A u Hu) as Hsn.
  revert Hu.
  induction Hsn as [u Hsteps IH]; intro Hu.
  apply neutral_expand.
  - constructor; auto. apply reducible_lc with A; auto.
  - intro Hv. inversion Hv.
  - intros q Hs. inversion Hs; subst.
    + apply Hbody; auto.
    + exfalso. eapply value_no_step; eauto. constructor; auto.
    + apply IH; auto. eapply reducible_step; eauto.
Qed.

Definition env_reducible (Gamma : context) (rho : renv) : Prop :=
  (forall x, locally_closed (rho x)) /\
  (forall x T, Gamma x = Some T -> reducible T (rho x)).

Lemma fundamental : forall Gamma t T, has_type Gamma t T ->
  forall rho, env_reducible Gamma rho -> reducible T (instantiate rho t).
Proof.
  intros Gamma t T Htyping.
  induction Htyping as
    [Gamma x T Hlookup
    |L Gamma A B body Hopen IHopen
    |Gamma t1 t2 A B Hty1 IH1 Hty2 IH2
    |Gamma
    |Gamma
    |Gamma t1 t2 T Hty1 IH1 Hty2 IH2];
    intros rho Henv; simpl.
  - apply (proj2 Henv x T Hlookup).
  - assert (Habs : locally_closed (tm_abs A (instantiate rho body))).
    { change (lc_at 0 (instantiate rho (tm_abs A body))).
      apply instantiate_lc.
      - apply (typing_lc Gamma (tm_abs A body) (Ty_Arrow A B)).
        apply T_Abs with (L := L). exact Hopen.
      - exact (proj1 Henv). }
    simpl in Habs.
    split; [exact Habs |]. split.
    + constructor. intros q Hs. inversion Hs.
    + intros u Hu. apply beta_expand; auto.
      intros w Hw.
      destruct (fresh_atom (L ++ fv body)) as [x Hfresh].
      assert (HxL : ~ In x L).
      { intro H; apply Hfresh; apply in_or_app; left; exact H. }
      assert (HxF : ~ In x (fv body)).
      { intro H; apply Hfresh; apply in_or_app; right; exact H. }
      assert (Hext : env_reducible (update Gamma x A) (extend rho x w)).
      { split.
        - intro y. unfold extend. destruct (Nat.eqb_spec x y); subst.
          + apply reducible_lc with A; exact Hw.
          + apply (proj1 Henv).
        - intros y U Hy. unfold update in Hy. unfold extend.
          destruct (Nat.eqb_spec x y); subst.
          + inversion Hy; subst. exact Hw.
          +
            apply (proj2 Henv y U Hy). }
      pose proof (IHopen x HxL (extend rho x w) Hext) as Hr.
      unfold open in Hr.
      rewrite (instantiate_open body 0 rho x w HxF (proj1 Henv)) in Hr.
      exact Hr.
  - specialize (IH1 rho Henv). specialize (IH2 rho Henv).
    destruct IH1 as [_ [_ Hfun]]. apply Hfun. exact IH2.
  - split; [constructor |]. split; [constructor; intros q Hs; inversion Hs | exact I].
  - split; [constructor |]. split; [constructor; intros q Hs; inversion Hs | exact I].
  - specialize (IH1 rho Henv). specialize (IH2 rho Henv).
    apply neutral_expand.
    + constructor; apply reducible_lc with T; assumption.
    + intro Hv. inversion Hv.
    + intros q Hs. inversion Hs; subst; assumption.
Qed.

Theorem strong_normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  pose (rho := fun x : atom => tm_fvar x).
  assert (Henv : env_reducible empty rho).
  { split.
    - intro x. constructor.
    - intros x U Hlookup. discriminate Hlookup. }
  pose proof (fundamental empty t T Hty rho Henv) as Hr.
  assert (Hinst : forall s, instantiate rho s = s).
  { intro s; unfold rho; induction s; simpl; congruence. }
  rewrite Hinst in Hr. apply reducible_sn with T. exact Hr.
Qed.

End STLCNormalizationNondeterminismHardTask.
