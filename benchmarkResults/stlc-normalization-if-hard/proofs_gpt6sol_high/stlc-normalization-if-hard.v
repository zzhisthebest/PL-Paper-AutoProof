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

Lemma value_no_step : forall v u, value v -> v --> u -> False.
Proof.
  intros v u Hv Hs. inversion Hv; subst; inversion Hs; subst;
    try match goal with H : tm_abs _ _ --> _ |- _ => inversion H end;
    try match goal with H : tm_true --> _ |- _ => inversion H end;
    try match goal with H : tm_false --> _ |- _ => inversion H end.
Qed.

Lemma value_sn : forall v, value v -> strongly_normalizing v.
Proof.
  intros v Hv. constructor. intros u Hs. exfalso. eapply value_no_step; eauto.
Qed.

Lemma sn_step : forall t u, strongly_normalizing t -> t --> u -> strongly_normalizing u.
Proof. intros t u H Hs. inversion H; subst; eauto. Qed.

Lemma value_or_not : forall t, locally_closed t -> value t \/ ~ value t.
Proof.
  intros t Hlc. destruct t; try (right; intro Hv; inversion Hv; fail);
    try (left; constructor; assumption); try (left; constructor).
Qed.

Fixpoint reducible (T : ty) (t : tm) : Prop :=
  locally_closed t /\ strongly_normalizing t /\
  match T with
  | Ty_Bool =>
      forall v, t -->* v -> value v -> v = tm_true \/ v = tm_false
  | Ty_Arrow A B =>
      forall v, value v -> reducible A v -> reducible B (tm_app t v)
  end.

Lemma reducible_lc : forall T t, reducible T t -> locally_closed t.
Proof. intros T t H. destruct T; exact (proj1 H). Qed.

Lemma reducible_sn : forall T t, reducible T t -> strongly_normalizing t.
Proof. intros T t H. destruct T; exact (proj1 (proj2 H)). Qed.

Lemma multi_prefix : forall t u v, t --> u -> u -->* v -> t -->* v.
Proof. intros; econstructor; eauto. Qed.

Lemma lc_weaken : forall t k j, lc_at k t -> k <= j -> lc_at j t.
Proof.
  intros t k j H. revert j.
  induction H; intros j Hle; eauto using lc_at;
    [apply lc_bvar; lia | apply lc_abs; apply IHlc_at; lia].
Qed.

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v Hv. inversion Hv; subst; [assumption | apply lc_true | apply lc_false].
Qed.

Lemma lc_open_rec : forall t k u,
  lc_at (S k) t -> lc_at k u -> lc_at k (open_rec k u t).
Proof.
  induction t; intros k u Ht Hu; inversion Ht; subst; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + exact Hu.
    + apply Nat.eqb_neq in E. apply lc_bvar. lia.
  - apply lc_fvar.
  - apply lc_app; eauto.
  - apply lc_abs. apply IHt with (u:=u); auto.
      eapply lc_weaken; eauto; lia.
  - apply lc_true.
  - apply lc_false.
  - apply lc_if; eauto.
Qed.

Lemma step_lc : forall t u, locally_closed t -> t --> u -> locally_closed u.
Proof.
  intros t u Hlc Hs. revert Hlc.
  induction Hs; intros Hlc; inversion Hlc; subst;
    eauto using lc_app, lc_if, value_lc.
  match goal with H : lc_at 0 (tm_abs _ _) |- _ => inversion H; subst end.
  eapply lc_open_rec; eauto using value_lc.
  all: unfold locally_closed in *; eauto using lc_app, lc_if, value_lc.
Qed.

Lemma reducible_step : forall T t u, reducible T t -> t --> u -> reducible T u.
Proof.
  induction T as [|A IHA B IHB]; intros t u H Hs;
    destruct H as [Hlc [Hsn Hrest]]; simpl in *.
  - split.
    + eapply step_lc; eauto.
    + split. { eapply sn_step; eauto. }
      intros v Hmulti Hv. apply (Hrest v); eauto using multi_prefix.
  - split.
    + eapply step_lc; eauto.
    + split. { eapply sn_step; eauto. }
      intros v Hv Hr. apply (IHB (tm_app t v));
        [apply Hrest; assumption | apply ST_App1; eauto using reducible_lc].
Qed.

Lemma reducible_expand : forall T t,
  locally_closed t -> ~ value t ->
  (forall u, t --> u -> reducible T u) -> reducible T t.
Proof.
  induction T as [|A IHA B IHB]; intros t Hlc Hnv Hnext; simpl.
  - split; [assumption|]. split.
    + constructor. intros u Hs. apply reducible_sn with Ty_Bool. eauto.
    + intros v Hmulti Hv. inversion Hmulti; subst.
      * contradiction.
      * apply (proj2 (proj2 (Hnext _ H))) with (v:=v); assumption.
  - split; [assumption|]. split.
    + constructor. intros u Hs. apply reducible_sn with (Ty_Arrow A B). eauto.
    + intros v Hv Hr. apply IHB.
      * apply lc_app; [exact Hlc | exact (reducible_lc _ _ Hr)].
      * intro Hval. inversion Hval.
      * intros u Hs. inversion Hs; subst.
        -- contradiction Hnv. constructor; assumption.
        -- assert (Hred : reducible (Ty_Arrow A B) t1')
             by (apply Hnext; assumption).
           exact ((proj2 (proj2 Hred)) v Hv Hr).
        -- exfalso. exact (value_no_step v t2' Hv H3).
Qed.

Lemma true_reducible : reducible Ty_Bool tm_true.
Proof.
  simpl. split; [apply lc_true|]. split; [apply value_sn; constructor|].
  intros v Hmulti Hv. inversion Hmulti; subst; auto.
  exfalso. exact (value_no_step tm_true y v_true H).
Qed.

Lemma false_reducible : reducible Ty_Bool tm_false.
Proof.
  simpl. split; [apply lc_false|]. split; [apply value_sn; constructor|].
  intros v Hmulti Hv. inversion Hmulti; subst; auto.
  exfalso. exact (value_no_step tm_false y v_false H).
Qed.

Lemma app_reducible : forall A B t1 t2,
  reducible (Ty_Arrow A B) t1 -> reducible A t2 ->
  reducible B (tm_app t1 t2).
Proof.
  intros A B t1 t2 H1 H2.
  pose proof (reducible_sn _ _ H1) as Hsn1.
  revert t2 H1 H2.
  induction Hsn1 as [t1 Hstep1 IH1]; intros t2 H1 H2.
  pose proof (reducible_sn _ _ H2) as Hsn2.
  revert H1 H2.
  induction Hsn2 as [t2 Hstep2 IH2]; intros H1 H2.
  destruct (value_or_not t1 (reducible_lc _ _ H1)) as [Hv1|Hnv1];
  destruct (value_or_not t2 (reducible_lc _ _ H2)) as [Hv2|Hnv2].
  - exact ((proj2 (proj2 H1)) t2 Hv2 H2).
  - apply reducible_expand.
    + apply lc_app; [exact (reducible_lc _ _ H1) | exact (reducible_lc _ _ H2)].
    + intro Hv. inversion Hv.
    + intros u Hs. inversion Hs; subst.
      * contradiction Hnv2; assumption.
      * exfalso. eapply (value_no_step t1); [exact Hv1 | eassumption].
      * apply IH2; eauto using reducible_step.
  - apply reducible_expand.
    + apply lc_app; [exact (reducible_lc _ _ H1) | exact (reducible_lc _ _ H2)].
    + intro Hv. inversion Hv.
    + intros u Hs. inversion Hs; subst.
      * contradiction Hnv1. constructor; assumption.
      * apply IH1; eauto using reducible_step.
      * exfalso. eapply (value_no_step t2); [exact Hv2 | eassumption].
  - apply reducible_expand.
    + apply lc_app; [exact (reducible_lc _ _ H1) | exact (reducible_lc _ _ H2)].
    + intro Hv. inversion Hv.
    + intros u Hs. inversion Hs; subst.
      * contradiction Hnv1. constructor; assumption.
      * apply IH1; eauto using reducible_step.
      * contradiction Hnv1; assumption.
Qed.

Lemma if_reducible : forall T c t1 t2,
  reducible Ty_Bool c -> reducible T t1 -> reducible T t2 ->
  reducible T (tm_if c t1 t2).
Proof.
  intros T c t1 t2 Hc H1 H2.
  pose proof (reducible_sn _ _ Hc) as Hsn.
  revert Hc.
  induction Hsn as [c Hstep IH]; intros Hc.
  destruct (value_or_not c (reducible_lc _ _ Hc)) as [Hv|Hnv].
  - destruct ((proj2 (proj2 Hc)) c (multi_refl _ _) Hv) as [Heq|Heq];
      subst c; apply reducible_expand.
    + apply lc_if; [apply lc_true | exact (reducible_lc _ _ H1) |
                       exact (reducible_lc _ _ H2)].
    + intro Hval. inversion Hval.
    + intros u Hs. inversion Hs; subst; eauto;
        exfalso; eapply (value_no_step tm_true); [constructor | eassumption].
    + apply lc_if; [apply lc_false | exact (reducible_lc _ _ H1) |
                        exact (reducible_lc _ _ H2)].
    + intro Hval. inversion Hval.
    + intros u Hs. inversion Hs; subst; eauto;
        exfalso; eapply (value_no_step tm_false); [constructor | eassumption].
  - apply reducible_expand.
    + apply lc_if; [exact (reducible_lc _ _ Hc) |
                       exact (reducible_lc _ _ H1) | exact (reducible_lc _ _ H2)].
    + intro Hval. inversion Hval.
    + intros u Hs. inversion Hs; subst.
      * contradiction Hnv. constructor.
      * contradiction Hnv. constructor.
      * apply IH; eauto using reducible_step.
Qed.

Fixpoint free_atoms (t : tm) : list atom :=
  match t with
  | tm_bvar _ => nil
  | tm_fvar x => x :: nil
  | tm_app t1 t2 => free_atoms t1 ++ free_atoms t2
  | tm_abs _ body => free_atoms body
  | tm_true | tm_false => nil
  | tm_if c t1 t2 => free_atoms c ++ free_atoms t1 ++ free_atoms t2
  end.

Definition fresh (xs : list atom) : atom :=
  S (fold_right Nat.max 0 xs).

Lemma in_fold_max : forall xs x, In x xs -> x <= fold_right Nat.max 0 xs.
Proof.
  induction xs as [|y ys IH]; intros x H; simpl in *.
  - contradiction.
  - destruct H as [->|H]; [lia | specialize (IH _ H); lia].
Qed.

Lemma fresh_not_in : forall xs, ~ In (fresh xs) xs.
Proof.
  intros xs H. pose proof (in_fold_max xs (fresh xs) H).
  unfold fresh in *; lia.
Qed.

Lemma fresh_not_in_app : forall (x : atom) (xs ys : list atom),
  ~ In x (xs ++ ys) -> ~ In x xs /\ ~ In x ys.
Proof.
  intros x xs ys H. split; intro Hin; apply H; apply in_or_app;
    [left | right]; assumption.
Qed.

Lemma lc_open_id : forall t k j u,
  lc_at k t -> k <= j -> open_rec j u t = t.
Proof.
  induction t; intros k j u Hlc Hle; inversion Hlc; subst; simpl;
    try (f_equal; eauto; fail).
  - destruct (Nat.eqb j n) eqn:E; [apply Nat.eqb_eq in E; lia | reflexivity].
  - f_equal. apply IHt with (k:=S k); auto; lia.
Qed.

Lemma lc_open_reverse : forall t k u,
  lc_at k (open_rec k u t) -> lc_at (S k) t.
Proof.
  induction t; intros k u Hlc; simpl in Hlc.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. apply lc_bvar. lia.
    + inversion Hlc; subst. apply lc_bvar. lia.
  - apply lc_fvar.
  - inversion Hlc; subst. apply lc_app; eauto.
  - inversion Hlc; subst. apply lc_abs; eauto.
  - apply lc_true.
  - apply lc_false.
  - inversion Hlc; subst. apply lc_if; eauto.
Qed.

Lemma typing_lc : forall Gamma t T, has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T Htyping. induction Htyping; unfold locally_closed in *;
    eauto using lc_fvar, lc_app, lc_true, lc_false, lc_if.
  apply lc_abs.
  pose (x := fresh L).
  assert (Hfresh : ~ In x L) by (unfold x; apply fresh_not_in).
  apply (lc_open_reverse t1 0 (tm_fvar x)).
  exact (H0 x Hfresh).
Qed.

Definition substitution := atom -> tm.

Fixpoint subst (rho : substitution) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => rho x
  | tm_app t1 t2 => tm_app (subst rho t1) (subst rho t2)
  | tm_abs T body => tm_abs T (subst rho body)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if c t1 t2 => tm_if (subst rho c) (subst rho t1) (subst rho t2)
  end.

Definition extend (rho : substitution) (x : atom) (v : tm) : substitution :=
  fun y => if Nat.eqb x y then v else rho y.

Lemma subst_lc : forall t k rho,
  lc_at k t -> (forall x, locally_closed (rho x)) -> lc_at k (subst rho t).
Proof.
  induction t; intros k rho Hlc Henv; inversion Hlc; subst; simpl;
    eauto using lc_bvar, lc_app, lc_abs, lc_true, lc_false, lc_if.
  eapply lc_weaken; [apply Henv | lia].
Qed.

Lemma subst_open_rec : forall t k rho x v,
  ~ In x (free_atoms t) ->
  (forall y, locally_closed (rho y)) ->
  subst (extend rho x v) (open_rec k (tm_fvar x) t) =
  open_rec k v (subst rho t).
Proof.
  induction t; intros k rho x v Hfresh Henv; simpl in *.
  - destruct (Nat.eqb k n) eqn:E; simpl.
    + unfold extend. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - assert (x <> a) by (intro Heq; subst; apply Hfresh; left; reflexivity).
    unfold extend. assert (E : Nat.eqb x a = false)
      by (apply Nat.eqb_neq; assumption). rewrite E.
    symmetry. eapply lc_open_id; [apply Henv | lia].
  - apply fresh_not_in_app in Hfresh. destruct Hfresh as [Hfirst Hsecond].
    f_equal; eauto.
  - f_equal. apply IHt; assumption.
  - reflexivity.
  - reflexivity.
  - apply fresh_not_in_app in Hfresh. destruct Hfresh as [Hc Hbranches].
    apply fresh_not_in_app in Hbranches. destruct Hbranches as [Hfirst Hsecond].
    f_equal; eauto.
Qed.

Definition interprets (Gamma : context) (rho : substitution) : Prop :=
  (forall x, locally_closed (rho x)) /\
  (forall x T, Gamma x = Some T -> value (rho x) /\ reducible T (rho x)).

Lemma interprets_extend : forall Gamma rho x A v,
  interprets Gamma rho -> value v -> reducible A v ->
  interprets (update Gamma x A) (extend rho x v).
Proof.
  intros Gamma rho x A v [Hlc Hgood] Hv Hr. split.
  - intros y. unfold extend. destruct (Nat.eqb x y); eauto using value_lc.
  - intros y T Hlookup. unfold update in Hlookup.
    unfold extend. destruct (Nat.eqb x y) eqn:E.
    + inversion Hlookup; subst. auto.
    + apply Hgood; assumption.
Qed.

Lemma fundamental : forall Gamma t T,
  has_type Gamma t T ->
  forall rho, interprets Gamma rho -> reducible T (subst rho t).
Proof.
  intros Gamma t T Htyping.
  induction Htyping as
    [Gamma x T Hlookup
    |L Gamma A B body Hbody IHbody
    |Gamma t1 t2 A B Ht1 IH1 Ht2 IH2
    |Gamma |Gamma
    |Gamma c t1 t2 T Hc IHc Ht1 IH1 Ht2 IH2];
    intros rho Henv; simpl.
  - exact (proj2 ((proj2 Henv) x T Hlookup)).
  - pose (x := fresh (L ++ free_atoms body)).
    assert (Hfresh : ~ In x (L ++ free_atoms body))
      by (unfold x; apply fresh_not_in).
    apply fresh_not_in_app in Hfresh. destruct Hfresh as [HfreshL HfreshBody].
    assert (Habs : locally_closed (tm_abs A (subst rho body))).
    { apply lc_abs. apply subst_lc.
      - eapply lc_open_reverse.
        exact (typing_lc _ _ _ (Hbody x HfreshL)).
      - exact (proj1 Henv). }
    simpl. split; [exact Habs|]. split.
    + apply value_sn. constructor. exact Habs.
    + intros v Hv Hr. apply reducible_expand.
      * apply lc_app; [exact Habs | exact (reducible_lc _ _ Hr)].
      * intro Hval. inversion Hval.
      * intros u Hs. inversion Hs; subst.
        -- unfold open. rewrite <- (subst_open_rec body 0 rho x v HfreshBody
                        (proj1 Henv)).
           apply IHbody; [exact HfreshL |].
           eapply interprets_extend; eauto.
        -- exfalso. eapply (value_no_step (tm_abs A (subst rho body)));
             [constructor; exact Habs | eassumption].
        -- exfalso. eapply (value_no_step v); [exact Hv | eassumption].
  - eapply app_reducible; [apply IH1 | apply IH2]; exact Henv.
  - exact true_reducible.
  - exact false_reducible.
  - eapply if_reducible; [apply IHc | apply IH1 | apply IH2]; exact Henv.
Qed.

Lemma subst_id : forall t, subst (fun x => tm_fvar x) t = t.
Proof. induction t; simpl; congruence. Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Htyping. apply (reducible_sn T).
  rewrite <- subst_id.
  apply (fundamental empty t T Htyping (fun x => tm_fvar x)).
  split.
  - intro x. apply lc_fvar.
  - intros x U Hlookup. discriminate Hlookup.
Qed.

End STLCCBVNormalizationTask.
