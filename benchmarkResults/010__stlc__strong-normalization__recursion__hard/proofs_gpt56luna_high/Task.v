(** STLC call-by-value strong-normalization benchmark, Hard variant.
    System T-style natural-number recursion; no if-then-else or choice. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Relations.Relation_Definitions Lia Classical_Prop.
Import ListNotations.

Module STLCNormalizationRecursionHardTask.

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

(*****************************************************************)
(* Reducibility candidates.  The extra local-closure component is
   useful here because the operational semantics deliberately puts
   local-closure side conditions on congruence rules. *)

Fixpoint term_subst (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_app t1 t2 => tm_app (term_subst sigma t1) (term_subst sigma t2)
  | tm_abs T t1 => tm_abs T (term_subst sigma t1)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (term_subst sigma t1)
  | tm_natrec n b s =>
      tm_natrec (term_subst sigma n) (term_subst sigma b) (term_subst sigma s)
  end.

Definition term_update (sigma : atom -> tm) (x : atom) (v : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then v else sigma y.

Fixpoint reducible (T : ty) (t : tm) : Prop :=
  locally_closed t /\
  strongly_normalizing t /\
  match T with
  | Ty_Bool => True
  | Ty_Nat => True
  | Ty_Arrow A B => forall v, reducible A v ->
      reducible B (tm_app t v)
  end.

Definition valid_subst (Gamma : context) (sigma : atom -> tm) : Prop :=
  forall x T, Gamma x = Some T -> reducible T (sigma x).

Lemma red_lc : forall T t, reducible T t -> locally_closed t.
Proof.
  intros T t H; destruct T; simpl in H; tauto.
Qed.

Lemma red_sn : forall T t, reducible T t -> strongly_normalizing t.
Proof.
  intros T t H; destruct T; simpl in H; tauto.
Qed.

Lemma numeric_lc : forall t, numeric_value t -> locally_closed t.
Proof.
  intros t H; induction H.
  - unfold locally_closed; eapply lc_zero.
  - unfold locally_closed; eapply lc_succ; exact IHnumeric_value.
Qed.

Lemma value_lc : forall t, value t -> locally_closed t.
Proof.
  intros t H; induction H.
  - exact H.
  - unfold locally_closed; eapply lc_true.
  - unfold locally_closed; eapply lc_false.
  - apply numeric_lc; exact H.
Qed.

Lemma numeric_no_step_pre : forall n n', numeric_value n -> ~ step n n'.
Proof.
  intros n n' Hn; revert n'; induction Hn as [| n Hn IH]; intros n'.
  - intros Hs; inversion Hs.
  - intros Hs; inversion Hs; subst.
    exact (IH _ H0).
Qed.

Lemma value_no_step : forall v v', value v -> ~ step v v'.
Proof.
  intros v v' Hv; induction Hv.
  - intros Hs; inversion Hs.
  - intros Hs; inversion Hs.
  - intros Hs; inversion Hs.
  - intros Hs; eapply numeric_no_step_pre; eauto.
Qed.

Lemma numeric_no_step : forall n n', numeric_value n -> ~ step n n'.
Proof.
  intros n n' Hn; revert n'; induction Hn as [| n Hn IH]; intros n'.
  - intros Hs; inversion Hs.
  - intros Hs; inversion Hs; subst.
    exact (IH _ H0).
Qed.

Lemma lc_weaken : forall k t, lc_at k t -> forall j, k <= j -> lc_at j t.
Proof.
  intros k t H; induction H as
      [k i Hik | k x | k t1 t2 H1 IH1 H2 IH2 | k T t H IH
      | k | k | k | k t H IH | k n b s Hn IHn Hb IHb Hs IHs];
    intros j Hkj.
  - apply lc_bvar; lia.
  - apply lc_fvar.
  - apply lc_app; [apply IH1 | apply IH2]; assumption.
  - apply lc_abs. apply IH. lia.
  - apply lc_true.
  - apply lc_false.
  - apply lc_zero.
  - apply lc_succ. apply IH; assumption.
  - apply lc_rec; [apply IHn | apply IHb | apply IHs]; assumption.
Qed.

Lemma lc_open_rec : forall k t u,
    lc_at (S k) t -> lc_at k u -> lc_at k (open_rec k u t).
Proof.
  intros k t; revert k.
  induction t as [i|x|t1 IH1 t2 IH2|A t IH| | | |t IH|n IHn b IHb s IHs];
    intros k u Ht Hu; simpl in *; inversion Ht; subst.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E; subst; exact Hu.
    + apply lc_bvar; apply Nat.eqb_neq in E; lia.
  - apply lc_fvar.
  - apply lc_app; [apply IH1 | apply IH2]; assumption.
  - apply lc_abs. eapply IH.
    + exact H1.
    + eapply lc_weaken; [exact Hu | lia].
  - apply lc_true.
  - apply lc_false.
  - apply lc_zero.
  - apply lc_succ. apply IH; assumption.
  - apply lc_rec; [apply IHn | apply IHb | apply IHs]; assumption.
Qed.

Lemma open_rec_lc : forall k t u, lc_at k t -> open_rec k u t = t.
Proof.
  intros k t u H; generalize dependent k.
  induction t as [i|x|t1 IH1 t2 IH2|A t IH| | | |t IH|n IHn b IHb s IHs];
    intros k H; simpl in *; inversion H; subst.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E; lia.
    + reflexivity.
  - reflexivity.
  - rewrite IH1, IH2; auto.
  - f_equal; eapply IH; eauto.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - f_equal; eapply IH; eauto.
  - rewrite IHn, IHb, IHs; auto.
Qed.

Lemma open_lc : forall t u, locally_closed t -> open t u = t.
Proof.
  intros t u H; unfold locally_closed in H; unfold open.
  apply open_rec_lc; exact H.
Qed.

Lemma lc_step : forall t t', step t t' ->
    locally_closed t -> locally_closed t'.
Proof.
  intros t t' H; induction H as
    [T b v Hab Hv
    | t1 t1' t2 Hs IH Hlc2
    | v1 t2 t2' Hv Hs IH
    | t t' Hs IH
    | n n' b s Hs IH Hlb Hls
    | n b b' s Hn Hs IH Hls
    | n b s s' Hn Hb Hs IH
    | b s Hb Hs
    | n b s Hn Hb Hs]; intros Hlc; unfold locally_closed in *;
    inversion Hlc; subst.
  - inversion Hab; subst; eapply lc_open_rec; eauto using value_lc.
  - apply lc_app; eauto.
  - apply lc_app; eauto using value_lc.
  - apply lc_succ; eauto.
  - apply lc_rec; eauto.
  - apply lc_rec; eauto.
  - apply lc_rec; eauto.
  - eauto using value_lc.
  - apply lc_app.
    + apply lc_app.
      * apply value_lc; exact Hs.
      * apply numeric_lc; exact Hn.
    + apply lc_rec.
      * apply numeric_lc; exact Hn.
      * apply value_lc; exact Hb.
      * apply value_lc; exact Hs.
Qed.

Lemma subst_lc : forall k t sigma,
    lc_at k t -> (forall x, locally_closed (sigma x)) ->
    lc_at k (term_subst sigma t).
Proof.
  intros k t; revert k.
  induction t as [i|x|t1 IH1 t2 IH2|A t IH| | | |t IH|n IHn b IHb s IHs];
    intros k sigma Ht Hs; simpl in *; inversion Ht; subst.
  - apply lc_bvar; assumption.
  - eapply lc_weaken; [apply Hs|lia].
  - apply lc_app; [apply IH1 | apply IH2]; assumption.
  - apply lc_abs. eapply IH; [exact H1 | assumption].
  - apply lc_true.
  - apply lc_false.
  - apply lc_zero.
  - apply lc_succ. eapply IH; eauto.
  - apply lc_rec; [apply IHn | apply IHb | apply IHs]; assumption.
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
  end.

Fixpoint tm_bound (t : tm) : nat :=
  match t with
  | tm_bvar _ => 0
  | tm_fvar x => S x
  | tm_app t1 t2 => max (tm_bound t1) (tm_bound t2)
  | tm_abs _ t1 => tm_bound t1
  | tm_true | tm_false | tm_zero => 0
  | tm_succ t1 => tm_bound t1
  | tm_natrec n b s => max (tm_bound n) (max (tm_bound b) (tm_bound s))
  end.

Fixpoint list_bound (L : list atom) : nat :=
  match L with [] => 0 | x :: L => max (S x) (list_bound L) end.

Lemma fv_bound : forall t x, In x (fv t) -> x < tm_bound t.
Proof.
  induction t as [i|a|t1 IH1 t2 IH2|A t IH| | | |t IH|n IHn b IHb s IHs];
    simpl; intros x H.
  - contradiction.
  - simpl in H; destruct H as [<-|H]; [lia|contradiction].
  - rewrite in_app_iff in H; destruct H as [H|H].
    + apply Nat.lt_le_trans with (tm_bound t1); [apply IH1; exact H|lia].
    + apply Nat.lt_le_trans with (tm_bound t2); [apply IH2; exact H|lia].
  - apply IH; exact H.
  - contradiction.
  - contradiction.
  - contradiction.
  - apply IH; exact H.
  - repeat rewrite in_app_iff in H; destruct H as [H|[H|H]].
    + apply Nat.lt_le_trans with (tm_bound n); [apply IHn; exact H|lia].
    + apply Nat.lt_le_trans with (tm_bound b); [apply IHb; exact H|lia].
    + apply Nat.lt_le_trans with (tm_bound s); [apply IHs; exact H|lia].
Qed.

Lemma list_bound_In : forall L x, In x L -> x < list_bound L.
Proof.
  induction L as [|a L IH]; intros x H.
  - contradiction.
  - simpl in H; destruct H as [<-|H].
    + apply Nat.lt_le_trans with (S a); [lia | exact (Nat.le_max_l _ _)].
    + apply Nat.lt_le_trans with (list_bound L);
        [apply IH; exact H | exact (Nat.le_max_r _ _)].
Qed.

Lemma fresh_for : forall (L : list atom) t,
  exists x, ~ In x L /\ ~ In x (fv t).
Proof.
  intros L t; exists (max (list_bound L) (tm_bound t)).
  split; intro H.
  - pose proof (list_bound_In L _ H); lia.
  - pose proof (fv_bound t _ H); lia.
Qed.

Lemma subst_open_rec : forall t k sigma x v,
    (forall y, locally_closed (sigma y)) ->
    ~ In x (fv t) ->
    term_subst (term_update sigma x v) (open_rec k (tm_fvar x) t) =
    open_rec k v (term_subst sigma t).
Proof.
  intros t; induction t as [n|a|t1 IH1 t2 IH2|A t IH| | | |t IH|n IHn b IHb s IHs];
    intros k sigma x v Hs Hfresh; simpl in *; try reflexivity.
  - destruct (Nat.eqb k n) eqn:E.
    + unfold term_update; cbn [term_subst]; rewrite Nat.eqb_refl; reflexivity.
    + unfold term_update; cbn [term_subst]; reflexivity.
  - destruct (Nat.eqb x a) eqn:E.
    + exfalso; apply Hfresh; simpl; left; apply Nat.eqb_eq in E; symmetry; exact E.
    + rewrite (open_rec_lc k (sigma a) v).
      * unfold term_update; cbn [term_subst].
        rewrite E; reflexivity.
      * eapply lc_weaken; [apply Hs|lia].
  - f_equal.
    + apply IH1; [exact Hs | intro H; apply Hfresh; apply in_or_app; left; exact H].
    + apply IH2; [exact Hs | intro H; apply Hfresh; apply in_or_app; right; exact H].
  - f_equal; apply IH; auto.
  - f_equal; apply IH; auto.
  - assert (Fn : ~ In x (fv n)).
    { intro H; apply Hfresh.
      exact (@in_or_app atom (fv n) (fv b ++ fv s) x (or_introl H)). }
    assert (Fb : ~ In x (fv b)).
    { intro H; apply Hfresh.
      apply in_or_app; right; apply in_or_app; left; exact H. }
    assert (Fs : ~ In x (fv s)).
    { intro H; apply Hfresh.
      apply in_or_app; right; apply in_or_app; right; exact H. }
    rewrite (IHn k sigma x v Hs Fn).
    rewrite (IHb k sigma x v Hs Fb).
    rewrite (IHs k sigma x v Hs Fs).
    reflexivity.
Qed.

Lemma subst_open : forall t sigma x v,
    (forall y, locally_closed (sigma y)) ->
    ~ In x (fv t) ->
    term_subst (term_update sigma x v) (open t (tm_fvar x)) =
    open (term_subst sigma t) v.
Proof.
  intros; unfold open; apply subst_open_rec; auto.
Qed.

Lemma sn_step : forall t t', strongly_normalizing t -> step t t' ->
    strongly_normalizing t'.
Proof.
  intros t t' H; inversion H; eauto.
Qed.

Lemma red_step : forall T t t', reducible T t -> step t t' -> reducible T t'.
Proof.
  induction T as [| | A IHA B IHB]; intros t t' Hr Hstep;
    destruct Hr as [Hlc [Hsn Hty]]; simpl in *.
  - split; [exact (lc_step _ _ Hstep Hlc)|].
    split; [exact (sn_step _ _ Hsn Hstep)|trivial].
  - split; [exact (lc_step _ _ Hstep Hlc)|].
    split; [exact (sn_step _ _ Hsn Hstep)|trivial].
  - split; [exact (lc_step _ _ Hstep Hlc)|].
    split; [exact (sn_step _ _ Hsn Hstep)|].
    intros v Hv.
    apply IHB with (t := tm_app t v) (t' := tm_app t' v).
    + apply Hty; exact Hv.
    + apply ST_App1; [exact Hstep | exact (red_lc _ _ Hv)].
Qed.

Lemma red_expand_neutral : forall T t,
    locally_closed t -> ~ value t ->
    (forall t', step t t' -> reducible T t') -> reducible T t.
Proof.
  induction T as [| | A IHA B IHB]; intros t Hlc Hnv Hr; simpl.
  - split; [exact Hlc|]. split; [constructor; intros t' Hs; apply (Hr t' Hs)|trivial].
  - split; [exact Hlc|]. split; [constructor; intros t' Hs; apply (Hr t' Hs)|trivial].
  - split; [exact Hlc|]. split; [constructor; intros t' Hs; apply (Hr t' Hs)|].
    intros v Hv.
    assert (Hnvapp : ~ value (tm_app t v)).
    { intro H; inversion H; subst; try (inversion H0). }
    apply IHB.
    + apply lc_app; [exact Hlc | exact (red_lc _ _ Hv)].
    + exact Hnvapp.
    + intros q Hq.
      inversion Hq; subst.
      * exfalso; apply Hnv; constructor; exact H1.
      * apply (proj2 (proj2 (Hr _ H1)) v Hv).
      * exfalso; apply Hnv; exact H1.
Qed.

Lemma app_not_value : forall f a, ~ value (tm_app f a).
Proof.
  intros f a H; inversion H; subst; try (inversion H0).
Qed.

Lemma red_abs_app : forall A B body,
    lc_at 1 body ->
    (forall v, reducible A v -> reducible B (open body v)) ->
    forall v, reducible A v ->
      reducible B (tm_app (tm_abs A body) v).
Proof.
  intros A B body Hbody Hbeta.
  assert (Haux : forall v, strongly_normalizing v -> reducible A v ->
      reducible B (tm_app (tm_abs A body) v)).
  { intros v Sv; induction Sv as [v Hv IH].
    intros Rv.
    apply red_expand_neutral.
    + apply lc_app.
      * apply lc_abs; exact Hbody.
      * exact (red_lc _ _ Rv).
    + apply app_not_value.
    + intros q Hq; inversion Hq; subst.
      * apply Hbeta; exact Rv.
      * exfalso.
        exact (value_no_step _ _
          (v_abs A body (ltac:(unfold locally_closed; apply lc_abs; exact Hbody))) H1).
      * apply IH; [exact H3 | exact (red_step A v t2' Rv H3)].
  }
  intros v Rv; apply Haux; [exact (red_sn _ _ Rv) | exact Rv].
Qed.

Lemma red_abs : forall A B body,
    lc_at 1 body ->
    (forall v, reducible A v -> reducible B (open body v)) ->
    reducible (Ty_Arrow A B) (tm_abs A body).
Proof.
  intros A B body Hbody Hbeta; simpl.
  split; [apply lc_abs; exact Hbody|].
  split.
  - constructor; intros t' H; inversion H.
  - intros v Rv; apply red_abs_app with (body := body); assumption.
Qed.

Lemma red_apply : forall A B f v,
    reducible (Ty_Arrow A B) f -> reducible A v ->
    reducible B (tm_app f v).
Proof.
  intros A B f v Hf Hv; simpl in Hf.
  exact (proj2 (proj2 Hf) v Hv).
Qed.

Lemma numeric_red : forall n, numeric_value n -> reducible Ty_Nat n.
Proof.
  intros n Hn; split; [apply numeric_lc; exact Hn|].
  split; [constructor; intros n' Hs; exfalso; eapply numeric_no_step; eauto|trivial].
Qed.

Lemma rec_not_value : forall n b s, ~ value (tm_natrec n b s).
Proof.
  intros n b s H; inversion H; subst; try (inversion H0).
Qed.

Lemma red_rec_numeric : forall T n b s,
    numeric_value n -> reducible T b ->
    reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
    reducible T (tm_natrec n b s).
Proof.
  intros T n b s Hn; revert b s; induction Hn as [|n Hn IH]; intros b s Rb Rs.
  - assert (Hcomp : forall b0, strongly_normalizing b0 ->
      forall s0, strongly_normalizing s0 -> reducible T b0 ->
      reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s0 ->
      reducible T (tm_natrec tm_zero b0 s0)).
    { intros b0 Sb; induction Sb as [b0 Hb IHb].
      intros s0 Ss; induction Ss as [s0 Hs IHs].
      intros Rb0 Rs0; apply red_expand_neutral.
      + apply lc_rec; [apply lc_zero|apply red_lc with (T := T); exact Rb0|
          apply red_lc with (T := Ty_Arrow Ty_Nat (Ty_Arrow T T)); exact Rs0].
      + apply rec_not_value.
      + intros q Hq; inversion Hq; subst.
        * exfalso; exact (numeric_no_step_pre tm_zero n' nv_zero H2).
        * exact (IHb _ H4 _ (SN_intro _ Hs) (red_step T b0 _ Rb0 H4) Rs0).
        * exact (IHs _ H5 Rb0 (red_step _ s0 _ Rs0 H5)).
        * exact Rb0.
    }
    apply Hcomp; [exact (red_sn _ _ Rb)|exact (red_sn _ _ Rs)|assumption|assumption].
  - assert (Hcomp : forall b0, strongly_normalizing b0 ->
      forall s0, strongly_normalizing s0 -> reducible T b0 ->
      reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s0 ->
      reducible T (tm_natrec (tm_succ n) b0 s0)).
    { intros b0 Sb; induction Sb as [b0 Hb IHb].
      intros s0 Ss; induction Ss as [s0 Hs IHs].
      intros Rb0 Rs0; apply red_expand_neutral.
      + apply lc_rec; [apply lc_succ; apply numeric_lc; exact Hn|
          apply red_lc with (T := T); exact Rb0|
          apply red_lc with (T := Ty_Arrow Ty_Nat (Ty_Arrow T T)); exact Rs0].
      + apply rec_not_value.
      + intros q Hq; inversion Hq; subst.
        * exfalso; exact (numeric_no_step_pre (tm_succ n) n' (nv_succ n Hn) H2).
        * exact (IHb _ H4 _ (SN_intro _ Hs) (red_step T b0 _ Rb0 H4) Rs0).
        * exact (IHs _ H5 Rb0 (red_step _ s0 _ Rs0 H5)).
        * apply red_apply with (A := T) (B := T);
            [ apply red_apply with (A := Ty_Nat) (B := Ty_Arrow T T);
                [ exact Rs0 | apply numeric_red; exact Hn ]
            | apply IH; [exact Rb0 | exact Rs0] ].
    }
    apply Hcomp; [exact (red_sn _ _ Rb)|exact (red_sn _ _ Rs)|assumption|assumption].
Qed.

Lemma lc_open_rec_inv : forall k t x,
    lc_at k (open_rec k (tm_fvar x) t) -> lc_at (S k) t.
Proof.
  intros k t x H; generalize dependent k.
  induction t as [i|a|t1 IH1 t2 IH2|A t IH| | | |t IH|n IHn b IHb s IHs];
    intros k H; simpl in *.
  - destruct (Nat.eqb k i) eqn:E.
    + apply lc_bvar; apply Nat.eqb_eq in E; lia.
    + inversion H; apply lc_bvar; apply Nat.eqb_neq in E; lia.
  - apply lc_fvar.
  - inversion H; subst; apply lc_app; [apply IH1; assumption|apply IH2; assumption].
  - inversion H; subst; apply lc_abs; eapply IH; eauto.
  - apply lc_true.
  - apply lc_false.
  - apply lc_zero.
  - inversion H; subst; apply lc_succ; apply IH; assumption.
  - inversion H; subst; apply lc_rec; [apply IHn|apply IHb|apply IHs]; assumption.
Qed.

Lemma valid_update : forall Gamma sigma x T v,
    valid_subst Gamma sigma -> reducible T v ->
    valid_subst (update Gamma x T) (term_update sigma x v).
Proof.
  intros Gamma sigma x T v Hv Rv y U Hy.
  unfold update in Hy; unfold term_update.
  destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E; subst; inversion Hy; subst U; exact Rv.
  - apply Hv with (x := y) (T := U); exact Hy.
Qed.

Lemma has_type_lc : forall Gamma t T, has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T H; induction H.
  - apply lc_fvar.
  - unfold locally_closed.
    destruct (fresh_for L t1) as [x [HxL Hxt]].
    apply lc_abs.
    apply lc_open_rec_inv with (x := x).
    apply H0; assumption.
  - apply lc_app; assumption.
  - apply lc_true.
  - apply lc_false.
  - apply lc_zero.
  - apply lc_succ; assumption.
  - apply lc_rec; assumption.
Qed.

Lemma sn_succ : forall t, strongly_normalizing t ->
    strongly_normalizing (tm_succ t).
Proof.
  intros t H; induction H as [t H IH].
  constructor; intros q Hq; inversion Hq; subst; apply IH; assumption.
Qed.

Lemma red_rec_general : forall T n b s,
    reducible Ty_Nat n -> reducible T b ->
    reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
    reducible T (tm_natrec n b s).
Proof.
  intros T n b s Rn Rb Rs.
  assert (Haux : forall n, strongly_normalizing n ->
      reducible Ty_Nat n -> reducible T b ->
      reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
      reducible T (tm_natrec n b s)).
  { intros m Sm; induction Sm as [m Hm IHm]; intros Rm Rb0 Rs0.
    destruct (classic (numeric_value m)) as [Hnum|Hnum].
    - apply red_rec_numeric; assumption.
    - apply red_expand_neutral.
      + apply lc_rec; [apply red_lc with (T := Ty_Nat); exact Rm|
          apply red_lc with (T := T); exact Rb0|
          apply red_lc with (T := Ty_Arrow Ty_Nat (Ty_Arrow T T)); exact Rs0].
      + apply rec_not_value.
      + intros q Hq; inversion Hq; subst.
        * apply IHm; [assumption|eapply red_step; [exact Rm|assumption]|exact Rb0|exact Rs0].
        * exfalso; apply Hnum; assumption.
        * exfalso; apply Hnum; assumption.
        * exfalso; apply Hnum; constructor.
        * exfalso; apply Hnum; constructor; assumption.
  }
  apply Haux; [exact (red_sn _ _ Rn)|exact Rn|exact Rb|exact Rs].
Qed.

Lemma fundamental : forall Gamma t T,
    has_type Gamma t T -> forall sigma, valid_subst Gamma sigma ->
      (forall x, locally_closed (sigma x)) ->
      reducible T (term_subst sigma t).
Proof.
  intros Gamma t T H; induction H as
    [Gamma x T Heq
    | L Gamma T1 T2 t1 Hbody IHbody
    | Gamma t1 t2 T1 T2 Hfun IHfun Harg IHarg
    | Gamma | Gamma | Gamma | Gamma n Hn IHn
    | Gamma n b s T Hn IHn Hb IHb Hs IHs];
    intros sigma Hsigma Hsigma_lc.
  - cbn; apply Hsigma with (x := x) (T := T); exact Heq.
  - cbn; apply red_abs.
    + apply subst_lc with (sigma := sigma).
      * destruct (fresh_for L t1) as [x [HxL Hxt]].
        apply lc_open_rec_inv with (x := x).
        apply (has_type_lc _ _ _ (Hbody x HxL)).
      * exact Hsigma_lc.
    + intros v Rv.
      destruct (fresh_for L t1) as [x [HxL Hxt]].
      rewrite <- (subst_open t1 sigma x v).
      * eapply (IHbody x HxL);
          [apply valid_update; assumption |
           (intro y; unfold term_update;
            destruct (Nat.eqb x y) eqn:E;
              [apply red_lc with (T := T1); exact Rv | apply Hsigma_lc])].
      * exact Hsigma_lc.
      * exact Hxt.
  - cbn; apply red_apply with (A := T1) (B := T2);
      [apply IHfun; [exact Hsigma|exact Hsigma_lc] |
       apply IHarg; [exact Hsigma|exact Hsigma_lc]].
  - cbn; split; [apply lc_true|split; [constructor; intros; inversion H|trivial]].
  - cbn; split; [apply lc_false|split; [constructor; intros; inversion H|trivial]].
  - cbn; split; [apply lc_zero|split; [constructor; intros; inversion H|trivial]].
  - cbn; split.
    + apply lc_succ; apply red_lc with (T := Ty_Nat); apply IHn; assumption.
    + split.
      * apply sn_succ; apply red_sn with (T := Ty_Nat);
          apply IHn; assumption.
      * trivial.
  - cbn; apply red_rec_general; [apply IHn|apply IHb|apply IHs]; assumption.
Qed.

Lemma subst_id : forall t,
    term_subst (fun x => tm_fvar x) t = t.
Proof.
  induction t as [| |t1 IH1 t2 IH2|A t IH| | | |t IH|n IHn b IHb s IHs];
    simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IH1, IH2; reflexivity.
  - f_equal; apply IH.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - f_equal; apply IH.
  - rewrite IHn, IHb, IHs; reflexivity.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> -> strongly_normalizing t.
Proof.
  intros t T Ht.
  assert (Hv : valid_subst empty (fun x => tm_fvar x)).
  { unfold valid_subst, empty; intros x U H; discriminate. }
  assert (Hlc : forall x, locally_closed (tm_fvar x)).
  { intro x; apply lc_fvar. }
  pose proof (fundamental empty t T Ht (fun x => tm_fvar x) Hv Hlc) as Hr.
  rewrite subst_id in Hr.
  apply red_sn with (T := T) (t := t); exact Hr.
Qed.

End STLCNormalizationRecursionHardTask.
