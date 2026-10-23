(** STLC call-by-value strong-normalization benchmark.
    No if-then-else, non-determinism, or recursion is included. *)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Relations.Relation_Definitions.

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

Fixpoint fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ => nil
  | tm_fvar x => x :: nil
  | tm_app t1 t2 => fv t1 ++ fv t2
  | tm_abs _ t1 => fv t1
  | tm_true => nil
  | tm_false => nil
  end.

Fixpoint fresh (L : list atom) : atom :=
  match L with
  | nil => 0
  | x :: L' => S (Nat.max x (fresh L'))
  end.

Lemma in_lt_fresh : forall L x, In x L -> x < fresh L.
Proof.
  induction L as [|a L IH]; simpl; intros x H.
  - contradiction.
  - destruct H as [H|H].
    + subst x. apply Nat.le_lt_trans with (Nat.max a (fresh L)).
      * apply Nat.le_max_l.
      * apply Nat.lt_succ_diag_r.
    + apply Nat.lt_trans with (fresh L).
      * apply IH; exact H.
      * apply Nat.le_lt_trans with (Nat.max a (fresh L)).
        -- apply Nat.le_max_r.
        -- apply Nat.lt_succ_diag_r.
Qed.

Lemma not_in_fresh : forall L, ~ In (fresh L) L.
Proof.
  intros L H. exact (Nat.lt_irrefl _ (in_lt_fresh L (fresh L) H)).
Qed.

Lemma exists_not_in : forall (L : list atom), exists x, ~ In x L.
Proof.
  intro L. exists (fresh L). apply not_in_fresh.
Qed.

Lemma lc_weaken_one : forall k t, lc_at k t -> lc_at (S k) t.
Proof.
  induction 1; constructor; eauto.
Qed.

Lemma lc_weaken : forall k t, lc_at 0 t -> lc_at k t.
Proof.
  intros k t H. induction k as [|k IH].
  - exact H.
  - apply lc_weaken_one. exact IH.
Qed.

Lemma lc_open_inv : forall k u t,
    lc_at k (open_rec k u t) -> lc_at (S k) t.
Proof.
  intros k u t H. revert k u H.
  induction t as [i|x|t1 IH1 t2 IH2|T t1 IH| |];
    intros k u H; simpl in H.
  - destruct (Nat.eqb k i) eqn:E.
    + constructor. apply Nat.eqb_eq in E. subst i. apply Nat.lt_succ_diag_r.
    + inversion H. constructor. apply Nat.lt_trans with k.
      * assumption.
      * apply Nat.lt_succ_diag_r.
  - constructor.
  - inversion H; constructor; eauto.
  - inversion H. constructor. apply (IH (S k) u). exact H2.
  - constructor.
  - constructor.
Qed.

Lemma le_eq_or_lt : forall i k, i <= k -> i = k \/ i < k.
Proof.
  intros i k H. induction H.
  - left; reflexivity.
  - right. apply Nat.le_lt_trans with m.
    + assumption.
    + apply Nat.lt_succ_diag_r.
Qed.

Lemma lt_succ_eq_or_lt : forall i k, i < S k -> i = k \/ i < k.
Proof.
  intros i k H. apply le_eq_or_lt.
  apply le_S_n. exact H.
Qed.

Lemma lc_open_rec : forall k t u,
    lc_at (S k) t -> lc_at k u -> lc_at k (open_rec k u t).
Proof.
  intros k t u Ht Hu. revert k u Ht Hu.
  induction t as [i|x|t1 IH1 t2 IH2|T t1 IH| |];
    intros k u Ht Hu; simpl.
  - inversion Ht. destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst i. exact Hu.
    + constructor. apply (lt_succ_eq_or_lt i k) in H1. destruct H1 as [Heq|Hlt].
      * subst i. rewrite Nat.eqb_refl in E. discriminate.
      * exact Hlt.
  - constructor.
  - inversion Ht. constructor; eauto.
  - inversion Ht. constructor. eapply IH; eauto.
    apply lc_weaken_one. exact Hu.
  - constructor.
  - constructor.
Qed.

Lemma lc_open : forall t u, lc_at 1 t -> locally_closed u -> locally_closed (open t u).
Proof.
  intros t u Ht Hu. apply lc_open_rec; assumption.
Qed.

Lemma lc_app_inv : forall t1 t2, locally_closed (tm_app t1 t2) ->
    locally_closed t1 /\ locally_closed t2.
Proof.
  intros t1 t2 H. inversion H. split; assumption.
Qed.

Lemma lc_abs_inv : forall T t, locally_closed (tm_abs T t) -> lc_at 1 t.
Proof.
  intros T t H. inversion H. assumption.
Qed.

Lemma lc_fv_subst : forall (rho : atom -> tm) k t,
    lc_at k t -> (forall x, locally_closed (rho x)) ->
    lc_at k (let fix sub (s : tm) : tm :=
      match s with
      | tm_bvar i => tm_bvar i
      | tm_fvar x => rho x
      | tm_app s1 s2 => tm_app (sub s1) (sub s2)
      | tm_abs T s1 => tm_abs T (sub s1)
      | tm_true => tm_true
      | tm_false => tm_false
      end in sub t).
Proof.
  intros rho k t Hlc Hrho. revert k Hlc.
  induction t as [i|x|t1 IH1 t2 IH2|T t1 IH| |];
    intros k Hlc; simpl.
  - constructor. inversion Hlc. exact H1.
  - apply lc_weaken. apply Hrho.
  - inversion Hlc. constructor; eauto.
  - inversion Hlc. constructor. apply IH; eauto.
  - constructor.
  - constructor.
Qed.

Fixpoint subst (rho : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => rho x
  | tm_app t1 t2 => tm_app (subst rho t1) (subst rho t2)
  | tm_abs T t1 => tm_abs T (subst rho t1)
  | tm_true => tm_true
  | tm_false => tm_false
  end.

Definition extend (rho : atom -> tm) (x : atom) (u : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then u else rho y.

Lemma open_rec_lc : forall k u t, lc_at k t -> open_rec k u t = t.
Proof.
  intros k u t H. revert k u H.
  induction t as [i|x|t1 IH1 t2 IH2|T t1 IH| |];
    intros k u H; simpl.
  - destruct (Nat.eqb k i) eqn:E.
    + exfalso. apply Nat.eqb_eq in E. subst k. inversion H. exact (Nat.lt_irrefl _ H2).
    + reflexivity.
  - reflexivity.
  - inversion H. rewrite IH1, IH2; auto.
  - inversion H. f_equal. apply IH; assumption.
  - reflexivity.
  - reflexivity.
Qed.

Lemma subst_open_rec : forall (rho : atom -> tm) x u k t,
    ~ In x (fv t) ->
    (forall y, locally_closed (rho y)) ->
    subst (extend rho x u) (open_rec k (tm_fvar x) t) =
    open_rec k u (subst rho t).
Proof.
  intros rho x u k t. revert k.
  induction t as [i|y|t1 IH1 t2 IH2|T t1 IH| |];
    intros k Hfresh Hrho; cbn [subst extend open_rec] in *.
  - destruct (Nat.eqb k i) eqn:E.
    + cbn [subst open_rec]. unfold extend. rewrite Nat.eqb_refl. reflexivity.
    + cbn [subst open_rec]. unfold extend. reflexivity.
  - destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst y. exfalso. apply Hfresh. simpl. auto.
    + cbn [subst open_rec]. unfold extend. rewrite E. symmetry.
      apply open_rec_lc. apply lc_weaken. apply Hrho.
  - assert (Hfresh1 : ~ In x (fv t1)).
    { intro H. apply Hfresh. apply in_or_app. left. exact H. }
    assert (Hfresh2 : ~ In x (fv t2)).
    { intro H. apply Hfresh. apply in_or_app. right. exact H. }
    simpl. rewrite (IH1 k Hfresh1 Hrho). rewrite (IH2 k Hfresh2 Hrho). reflexivity.
  - simpl in Hfresh. rewrite (IH (S k) Hfresh Hrho). reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Fixpoint reducible (T : ty) (t : tm) : Prop :=
  match T with
  | Ty_Bool => locally_closed t /\ strongly_normalizing t
  | Ty_Arrow A B =>
      locally_closed t /\ strongly_normalizing t /\
      (forall u, reducible A u -> reducible B (tm_app t u))
  end.

Lemma red_lc : forall T t, reducible T t -> locally_closed t.
Proof. intros T t H; destruct T; simpl in H; tauto. Qed.

Lemma red_sn : forall T t, reducible T t -> strongly_normalizing t.
Proof. intros T t H; destruct T; simpl in H; tauto. Qed.

Definition satisfies (Gamma : context) (rho : atom -> tm) : Prop :=
  (forall x, locally_closed (rho x)) /\
  (forall x T, Gamma x = Some T -> reducible T (rho x)).

Lemma satisfies_update : forall Gamma rho x T u,
    satisfies Gamma rho -> reducible T u ->
    satisfies (update Gamma x T) (extend rho x u).
Proof.
  intros Gamma rho x T u [Hlc Hty] Hu. split.
  - intro y. unfold extend. destruct (Nat.eqb x y) eqn:E.
    + apply red_lc with T. exact Hu.
    + apply Hlc.
  - intros y S Hy. unfold update in Hy. destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst y. inversion Hy; subst S.
      unfold extend. rewrite Nat.eqb_refl. exact Hu.
    + unfold extend. rewrite E. apply Hty. exact Hy.
Qed.

Lemma subst_lc : forall (rho : atom -> tm) k t,
    lc_at k t -> (forall x, locally_closed (rho x)) ->
    lc_at k (subst rho t).
Proof.
  intros rho k t Hlc Hrho. revert k Hlc.
  induction t as [i|x|t1 IH1 t2 IH2|T t1 IH| |];
    intros k Hlc; simpl.
  - inversion Hlc. constructor. assumption.
  - apply lc_weaken. apply Hrho.
  - inversion Hlc. constructor; eauto.
  - inversion Hlc. constructor. eapply IH; eauto.
  - constructor.
  - constructor.
Qed.

Lemma fv_open_rec_preserve : forall k t x y,
    In y (fv t) -> x <> y -> In y (fv (open_rec k (tm_fvar x) t)).
Proof.
  intros k t x y. revert k x y.
  induction t as [i|z|t1 IH1 t2 IH2|T t1 IH| |];
    intros k x y Hy Hxy; simpl in *.
  - contradiction.
  - destruct Hy as [Heq|Heq].
    + subst y. simpl. auto.
    + contradiction.
  - apply in_app_or in Hy. apply in_or_app.
    destruct Hy as [Hy|Hy]; [left; eapply IH1|right; eapply IH2]; eauto.
  - apply IH; eauto.
  - contradiction.
  - contradiction.
Qed.

Lemma typing_fv : forall Gamma t T, has_type Gamma t T ->
    forall y, In y (fv t) -> exists S, Gamma y = Some S.
Proof.
  intros Gamma t T H.
  induction H as [Gamma x T Hctx
                 | L Gamma T1 T2 t1 Habs IHabs
                 | Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
                 | Gamma
                 | Gamma].
  - intros y Hy. simpl in Hy. destruct Hy as [->|[]]. exists T. exact Hctx.
  - intros y Hy. simpl in Hy. destruct (exists_not_in (L ++ fv t1)) as [z Hz].
    assert (HzL : ~ In z L).
    { intro Hnot. apply Hz. apply in_or_app. left. exact Hnot. }
    assert (Hzy : z <> y).
    { intro E. apply Hz. apply in_or_app. right. rewrite E. exact Hy. }
    pose proof (fv_open_rec_preserve 0 t1 z y Hy Hzy) as Hyopen.
    destruct (IHabs z HzL y Hyopen) as [S HS].
    exists S. unfold update in HS. destruct (Nat.eqb z y) eqn:E.
    + exfalso. apply Hzy. apply Nat.eqb_eq. exact E.
    + exact HS.
  - intros y Hy. simpl in Hy. apply in_app_or in Hy. destruct Hy as [Hy|Hy].
    + destruct (IH1 y Hy) as [S HS]. exists S. exact HS.
    + destruct (IH2 y Hy) as [S HS]. exists S. exact HS.
  - intros y Hy; contradiction.
  - intros y Hy; contradiction.
Qed.

Lemma subst_no_fv : forall (rho : atom -> tm) t,
    (forall x, ~ In x (fv t)) -> subst rho t = t.
Proof.
  intros rho t. induction t as [i|x|t1 IH1 t2 IH2|T t1 IH| |]; intro H; simpl in *.
  - reflexivity.
  - exfalso. apply (H x). simpl. auto.
  - assert (H1 : forall x, ~ In x (fv t1)).
    { intros x Hx. apply (H x). apply in_or_app. left. exact Hx. }
    assert (H2 : forall x, ~ In x (fv t2)).
    { intros x Hx. apply (H x). apply in_or_app. right. exact Hx. }
    rewrite (IH1 H1), (IH2 H2). reflexivity.
  - apply f_equal. apply IH. exact H.
  - reflexivity.
  - reflexivity.
Qed.

Lemma typing_lc0 : forall Gamma t T, has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T H.
  induction H as [Gamma x T Hctx
                 | L Gamma T1 T2 t1 Hty IHty
                 | Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
                 | Gamma
                 | Gamma].
  - constructor.
  - apply lc_abs. destruct (exists_not_in L) as [x Hx].
    apply lc_open_inv with (u := tm_fvar x). apply IHty. exact Hx.
  - constructor; assumption.
  - constructor.
  - constructor.
Qed.

Lemma red_apply0 : forall A B f u,
    reducible (Ty_Arrow A B) f -> reducible A u ->
    reducible B (tm_app f u).
Proof.
  intros A B f u Hf Hu. apply (proj2 (proj2 Hf)); exact Hu.
Qed.

Lemma red_apply : forall A B f u,
    reducible (Ty_Arrow A B) f -> reducible A u ->
    reducible B (tm_app f u).
Proof.
  intros A B f u Hf Hu. apply (proj2 (proj2 Hf)); exact Hu.
Qed.

Lemma value_no_step : forall v v', value v -> ~ step v v'.
Proof.
  intros v v' Hv Hs. destruct Hv; inversion Hs.
Qed.

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v Hv. destruct Hv.
  - exact H.
  - constructor.
  - constructor.
Qed.

Lemma lc_step : forall t t', locally_closed t -> t --> t' -> locally_closed t'.
Proof.
  intros t t' Hlc Hstep.
  induction Hstep as [T t v Habs Hv | t1 t1' t2 Hs Hlc2 IH |
                         v1 t2 t2' Hv Hs IH].
  - apply lc_open.
    + apply (lc_abs_inv T t). exact (proj1 (lc_app_inv _ _ Hlc)).
    + apply value_lc; assumption.
  - apply lc_app_inv in Hlc. constructor.
    + apply Hlc2; exact (proj1 Hlc).
    + exact (proj2 Hlc).
  - apply lc_app_inv in Hlc. constructor.
    + apply value_lc; assumption.
    + apply IH; exact (proj2 Hlc).
Qed.

Lemma red_step : forall T t t', reducible T t -> t --> t' -> reducible T t'.
Proof.
  induction T as [|A IHB]; intros t t' Hred Hstep; simpl in *.
  - split.
    + inversion Hred as [Hlc Hsn]. apply lc_step with t; assumption.
    + inversion Hred as [Hlc Hsn].
      inversion Hsn as [t0 Hnext]. exact (Hnext _ Hstep).
  - destruct Hred as [Hlc [Hsn Hfun]]. split; [|split].
    + apply lc_step with t; assumption.
    + inversion Hsn as [t0 Hnext]. exact (Hnext _ Hstep).
    + intros u Hu. apply IHT1 with (t := tm_app t u).
      * apply Hfun; exact Hu.
      * apply ST_App1. exact Hstep. apply (red_lc A u). exact Hu.
Qed.

Lemma neutral_closure : forall T t,
    locally_closed t ->
    (forall t', t --> t' -> reducible T t') ->
    ~ value t -> reducible T t.
Proof.
  induction T as [|A IHB]; intros t Hlc Hall Hneutral; simpl.
  - split.
    + exact Hlc.
    + constructor. intros t' Hstep. apply (red_sn Ty_Bool t'). apply Hall; exact Hstep.
  - split.
    + exact Hlc.
    + split.
      * constructor. intros t' Hstep. apply (red_sn (Ty_Arrow A T1) t'). apply Hall; exact Hstep.
      * intros u Hu. apply IHT1.
        -- constructor.
           ++ exact Hlc.
           ++ apply (red_lc A u). exact Hu.
        -- intros q Hq. inversion Hq; subst.
           ++ exfalso. apply Hneutral. eauto using v_abs.
           ++ eauto using red_apply.
           ++ exfalso. apply Hneutral. eauto.
        -- intro Hv. inversion Hv.
Qed.

Lemma beta_expand : forall A B body u,
    locally_closed (tm_abs A body) ->
    reducible A u ->
    (forall w, reducible A w -> reducible B (open body w)) ->
    reducible B (tm_app (tm_abs A body) u).
Proof.
  intros A B body u Habs Hu Hbody.
  pose proof (red_sn A u Hu) as Husn.
  pose proof (red_lc A u Hu) as Hulc.
  revert B body Habs Hbody.
  induction Husn as [u Hsteps IH]; intros B body Habs Hbody.
  apply neutral_closure.
  - constructor; [exact Habs|exact Hulc].
  - intros q Hq. inversion Hq; subst.
    + apply Hbody; assumption.
    + exfalso. eapply value_no_step; eauto using v_abs.
    + apply IH.
      * exact H3.
      * eapply red_step; eauto.
      * apply (lc_step u t2'); [exact Hulc|exact H3].
      * exact Habs.
      * exact Hbody.
  - intro Hv. inversion Hv.
Qed.

Lemma typing_lc : forall Gamma t T, has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T H.
  induction H as [Gamma x T Hctx
                 | L Gamma T1 T2 t1 Hty IHty
                 | Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
                 | Gamma
                 | Gamma].
  - constructor.
  - apply lc_abs. destruct (exists_not_in L) as [x Hx].
    apply lc_open_inv with (u := tm_fvar x).
    apply IHty. exact Hx.
  - constructor; assumption.
  - constructor.
  - constructor.
Qed.

Lemma fundamental : forall Gamma t T rho,
    has_type Gamma t T -> satisfies Gamma rho -> reducible T (subst rho t).
Proof.
  intros Gamma t T rho H. revert rho.
  induction H as [Gamma x T Hctx
                 | L Gamma T1 T2 t1 Habs IHabs
                 | Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
                 | Gamma
                 | Gamma].
  - intros rho Hsat. simpl. apply (proj2 Hsat x T). exact Hctx.
  - intros rho Hsat.
    destruct (exists_not_in (L ++ fv t1)) as [z Hz].
    assert (HzL : ~ In z L).
    { intro Hnot. apply Hz. apply in_or_app. left. exact Hnot. }
    assert (Hzfv : ~ In z (fv t1)).
    { intro Hnot. apply Hz. apply in_or_app. right. exact Hnot. }
    assert (Hlcbody : lc_at 1 t1).
    { apply lc_open_inv with (u := tm_fvar z).
      apply (typing_lc (update Gamma z T1) (open t1 (tm_fvar z)) T2).
      apply Habs. exact HzL. }
    assert (Hlcabs : locally_closed (tm_abs T1 (subst rho t1))).
    { apply lc_abs. apply subst_lc with (rho := rho) (k := 1).
      - exact Hlcbody.
      - exact (proj1 Hsat). }
    assert (Hsnabs : strongly_normalizing (tm_abs T1 (subst rho t1))).
    { constructor. intros q Hq. inversion Hq. }
    cbn [subst]. split; [exact Hlcabs|split; [exact Hsnabs|]].
    intros u Hu. apply beta_expand.
    + exact Hlcabs.
    + exact Hu.
    + intros w Hw.
      pose proof (IHabs z HzL
        (extend rho z w)
        (satisfies_update Gamma rho z T1 w Hsat Hw)) as HH.
      unfold open in HH.
      rewrite (subst_open_rec rho z w 0 t1 Hzfv (proj1 Hsat)) in HH.
      exact HH.
  - intros rho Hsat. cbn [subst]. apply red_apply with (A := T1).
    + apply IH1. exact Hsat.
    + apply IH2. exact Hsat.
  - intros rho Hsat. split.
    + constructor.
    + constructor. intros q Hq. inversion Hq.
  - intros rho Hsat. split.
    + constructor.
    + constructor. intros q Hq. inversion Hq.

Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  pose (rho0 := (fun _ : atom => tm_true)).
  assert (Hsat : satisfies empty rho0).
  { split.
    - intro x. constructor.
    - intros x S Hx. unfold empty in Hx. discriminate. }
  pose proof (fundamental empty t T rho0 Hty Hsat) as Hred.
  assert (Hfv : forall x, ~ In x (fv t)).
  { intros x Hx.
    destruct (typing_fv empty t T Hty x Hx) as [S HS].
    unfold empty in HS. discriminate. }
  rewrite (subst_no_fv rho0 t Hfv) in Hred.
  exact (red_sn T t Hred).
Qed.

End STLCNormalizationNoneHardTask.
