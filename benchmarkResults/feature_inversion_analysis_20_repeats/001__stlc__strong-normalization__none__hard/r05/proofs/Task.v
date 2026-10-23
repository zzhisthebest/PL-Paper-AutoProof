(** STLC call-by-value strong-normalization benchmark.
    No if-then-else, non-determinism, or recursion is included. *)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Relations.Relation_Definitions.
From Stdlib Require Import Lia.

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

(** ** Auxiliary definitions and lemmas *)

(* ---------- Freshness and free variables ---------- *)

Fixpoint fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ => nil
  | tm_fvar x => x :: nil
  | tm_app t1 t2 => fv t1 ++ fv t2
  | tm_abs _ t1 => fv t1
  | tm_true => nil
  | tm_false => nil
  end.

Fixpoint max_list (L : list atom) : atom :=
  match L with
  | nil => 0
  | x :: xs => Nat.max x (max_list xs)
  end.

Definition fresh (L : list atom) : atom := S (max_list L).

Lemma max_list_spec : forall x L, In x L -> x <= max_list L.
Proof.
  intros x L H. induction L as [|a l IH]; simpl in *.
  - destruct H.
  - destruct H as [-> | H].
    + apply Nat.le_max_l.
    + apply Nat.le_trans with (m := max_list l).
      * apply IH. exact H.
      * apply Nat.le_max_r.
Qed.

Lemma fresh_notin : forall L, ~ In (fresh L) L.
Proof.
  intros L H. unfold fresh in H. pose proof (max_list_spec _ _ H). lia.
Qed.

(* ---------- Free-variable substitution ---------- *)

Fixpoint subst (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_app t1 t2 => tm_app (subst sigma t1) (subst sigma t2)
  | tm_abs T t1 => tm_abs T (subst sigma t1)
  | tm_true => tm_true
  | tm_false => tm_false
  end.

Definition extend (x : atom) (u : tm) (sigma : atom -> tm) : atom -> tm :=
  fun y => if Nat.eqb x y then u else sigma y.

Lemma extend_eq : forall x u sigma, extend x u sigma x = u.
Proof. intros. unfold extend. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma extend_neq : forall x y u sigma, x <> y -> extend x u sigma y = sigma y.
Proof. intros. unfold extend. apply Nat.eqb_neq in H. rewrite H. reflexivity. Qed.

Lemma subst_id : forall t, subst (fun x => tm_fvar x) t = t.
Proof.
  induction t; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(* ---------- Local closure lemmas ---------- *)

Lemma lc_app_pres : forall t1 t2, locally_closed t1 -> locally_closed t2 ->
  locally_closed (tm_app t1 t2).
Proof. intros. constructor; assumption. Qed.

Lemma lc_at_app_inv : forall k t1 t2,
  lc_at k (tm_app t1 t2) -> lc_at k t1 /\ lc_at k t2.
Proof. intros k t1 t2 H. inversion H. split; assumption. Qed.

Lemma lc_at_abs_inv : forall k T t, lc_at k (tm_abs T t) -> lc_at (S k) t.
Proof. intros k T t H. inversion H. assumption. Qed.

Lemma lc_app_inv : forall t1 t2,
  locally_closed (tm_app t1 t2) -> locally_closed t1 /\ locally_closed t2.
Proof. intros. apply lc_at_app_inv in H. exact H. Qed.

Lemma lc_abs_inv : forall T t, locally_closed (tm_abs T t) -> lc_at 1 t.
Proof. intros. apply lc_at_abs_inv in H. exact H. Qed.

Lemma lc_at_mono : forall k t, lc_at k t -> forall j, k <= j -> lc_at j t.
Proof.
  intros k t. revert k.
  induction t; intros k H j Hkj.
  - inversion H; subst. apply lc_bvar. lia.
  - apply lc_fvar.
  - apply lc_at_app_inv in H. destruct H as [H1 H2].
    apply lc_app.
    + apply IHt1 with (k := k); assumption.
    + apply IHt2 with (k := k); assumption.
  - apply lc_at_abs_inv in H. apply lc_abs.
    apply IHt with (k := S k); [assumption | lia].
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma lc_at_open : forall body k v,
  lc_at (S k) body -> lc_at k v -> lc_at k (open_rec k v body).
Proof.
  induction body; intros k v Hbody Hv; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + exact Hv.
    + inversion Hbody; subst. apply lc_bvar. apply Nat.eqb_neq in E. lia.
  - apply lc_fvar.
  - apply lc_at_app_inv in Hbody. destruct Hbody as [H1 H2].
    apply lc_app.
    + apply IHbody1; assumption.
    + apply IHbody2; assumption.
  - apply lc_at_abs_inv in Hbody.
    apply lc_abs. apply IHbody with (k := S k).
    + exact Hbody.
    + apply lc_at_mono with (k := k); [exact Hv | lia].
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma lc_open_fvar_inv : forall t k x,
  lc_at k (open_rec k (tm_fvar x) t) -> lc_at (S k) t.
Proof.
  induction t; intros k x H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. constructor. lia.
    + inversion H; subst. constructor. apply Nat.eqb_neq in E. lia.
  - constructor.
  - apply lc_at_app_inv in H. destruct H as [H1 H2].
    apply lc_app.
    + apply IHt1 with (x := x). exact H1.
    + apply IHt2 with (x := x). exact H2.
  - apply lc_at_abs_inv in H. apply lc_abs. apply IHt with (x := x). exact H.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma open_rec_lc_at : forall t k u, lc_at k t -> open_rec k u t = t.
Proof.
  induction t; intros k u H; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + exfalso. apply Nat.eqb_eq in E. subst. inversion H. lia.
    + reflexivity.
  - reflexivity.
  - apply lc_at_app_inv in H. destruct H as [H1 H2].
    rewrite IHt1 with (k := k) (u := u); [|exact H1].
    rewrite IHt2 with (k := k) (u := u); [|exact H2].
    reflexivity.
  - apply lc_at_abs_inv in H.
    rewrite IHt with (k := S k) (u := u); [|exact H].
    reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma lc_at_subst : forall t k sigma,
  lc_at k t -> (forall x, locally_closed (sigma x)) -> lc_at k (subst sigma t).
Proof.
  induction t; intros k sigma Hlc Hsig; simpl.
  - exact Hlc.
  - apply lc_at_mono with (k := 0); [apply Hsig | lia].
  - apply lc_at_app_inv in Hlc. destruct Hlc as [H1 H2].
    constructor; [apply IHt1 | apply IHt2]; assumption.
  - apply lc_at_abs_inv in Hlc. constructor. apply IHt with (k := S k); assumption.
  - constructor.
  - constructor.
Qed.

Lemma lc_step : forall t t', step t t' -> locally_closed t -> locally_closed t'.
Proof.
  intros t t' Hstep. induction Hstep; intros Hlc.
  - (* ST_AppAbs *)
    apply lc_app_inv in Hlc. destruct Hlc as [H1 H2].
    apply lc_abs_inv in H1.
    unfold locally_closed. apply lc_at_open with (k := 0); assumption.
  - (* ST_App1 *)
    apply lc_app_inv in Hlc. destruct Hlc as [H1 H2].
    apply lc_app_pres; [apply IHHstep; exact H1 | exact H2].
  - (* ST_App2 *)
    apply lc_app_inv in Hlc. destruct Hlc as [H1 H2].
    apply lc_app_pres; [exact H1 | apply IHHstep; exact H2].
Qed.

(* ---------- Values ---------- *)

Lemma value_lc : forall v, value v -> locally_closed v.
Proof. intros v H. destruct H. - assumption. - constructor. - constructor. Qed.

Lemma no_step_abs : forall T body t', ~ step (tm_abs T body) t'.
Proof. intros T body t' H. inversion H. Qed.

Lemma no_step_true : forall t', ~ step tm_true t'.
Proof. intros t' H. inversion H. Qed.

Lemma no_step_false : forall t', ~ step tm_false t'.
Proof. intros t' H. inversion H. Qed.

(* ---------- Inversion principles for step ---------- *)

Lemma step_app_inv : forall t1 t2 s,
  step (tm_app t1 t2) s ->
  (exists T body v, t1 = tm_abs T body /\ value v /\ t2 = v /\ s = open body v) \/
  (exists t1', step t1 t1' /\ s = tm_app t1' t2) \/
  (exists t2', value t1 /\ step t2 t2' /\ s = tm_app t1 t2').
Proof.
  intros t1 t2 s H. inversion H; subst.
  - left. eexists _, _, _. repeat split; eauto.
  - right; left. eexists. split; eauto.
  - right; right. eexists. split; eauto.
Qed.

Lemma step_abs_app_inv : forall T1 body t s,
  step (tm_app (tm_abs T1 body) t) s ->
  (value t /\ s = open body t) \/
  (exists t', step t t' /\ s = tm_app (tm_abs T1 body) t').
Proof.
  intros T1 body t s H. inversion H; subst.
  - left. split; [assumption | reflexivity].
  - exfalso. eapply no_step_abs. eassumption.
  - right. eexists. split; eauto.
Qed.

(* ---------- Basic strong normalization facts ---------- *)

Lemma SN_step : forall t t', strongly_normalizing t -> step t t' ->
  strongly_normalizing t'.
Proof.
  intros t t' Hsn Hstep. destruct Hsn as [t0 Hred]. apply Hred. exact Hstep.
Qed.

(* ---------- The logical relation ---------- *)

Fixpoint tr (T : ty) : tm -> Prop :=
  match T with
  | Ty_Bool => fun t => locally_closed t /\ strongly_normalizing t
  | Ty_Arrow T1 T2 => fun t =>
      locally_closed t /\ strongly_normalizing t /\
      (forall u, tr T1 u -> tr T2 (tm_app t u))
  end.

Lemma tr_lc : forall T t, tr T t -> locally_closed t.
Proof.
  induction T; intros t H; simpl in H; [destruct H as [H _] | destruct H as [H _]]; exact H.
Qed.

Lemma tr_sn : forall T t, tr T t -> strongly_normalizing t.
Proof.
  induction T; intros t H; simpl in H;
    [destruct H as [_ H] | destruct H as [_ [H _]]]; exact H.
Qed.

Lemma tr_app : forall T1 T2 t u,
  tr (Ty_Arrow T1 T2) t -> tr T1 u -> tr T2 (tm_app t u).
Proof.
  intros T1 T2 t u H Hu. simpl in H. destruct H as [_ [_ Hclos]].
  apply Hclos. exact Hu.
Qed.

Lemma tr_step : forall T t t', tr T t -> step t t' -> tr T t'.
Proof.
  induction T; intros t t' Htr Hstep.
  - simpl in Htr. destruct Htr as [Hlc Hsn]. simpl. split.
    + apply lc_step with (t := t); assumption.
    + apply SN_step with (t := t); assumption.
  - simpl in Htr. destruct Htr as [Hlc [Hsn Hclos]]. simpl. split; [|split].
    + apply lc_step with (t := t); assumption.
    + apply SN_step with (t := t); assumption.
    + intros u Hu.
      apply IHT2 with (t := tm_app t u) (t' := tm_app t' u).
      * apply Hclos. exact Hu.
      * apply ST_App1.
        -- exact Hstep.
        -- apply tr_lc in Hu. exact Hu.
Qed.

(* ---------- Beta expansion ---------- *)

Lemma sn_abs_app : forall T1 body t,
  strongly_normalizing t ->
  tr T1 t ->
  (forall v, tr T1 v -> strongly_normalizing (open body v)) ->
  strongly_normalizing (tm_app (tm_abs T1 body) t).
Proof.
  intros T1 body t Hsn Htr Hbody.
  revert Htr.
  induction Hsn as [t Hstep IH]; intros Htr.
  apply SN_intro. intros s Hs.
  destruct (step_abs_app_inv T1 body t s Hs) as [[Hv Heq] | [t' [Hstep' Heq]]].
  - rewrite Heq. apply Hbody. exact Htr.
  - rewrite Heq. apply IH; [exact Hstep' | apply tr_step with (t := t); assumption].
Qed.

Lemma step_app_nonvalue : forall s w r,
  locally_closed s ->
  ~ value s ->
  step (tm_app s w) r ->
  exists s', step s s' /\ r = tm_app s' w.
Proof.
  intros s w r Hlc Hnv H.
  destruct (step_app_inv s w r H) as
      [[T [body [v [Heq [Hv [Heqw Heqr]]]]]] | [[s' [Hs' Heqr]] | [w' [Hv_s [Hw' Heqr]]]]].
  - exfalso. apply Hnv. rewrite Heq. apply v_abs. rewrite <- Heq. exact Hlc.
  - exists s'. split; assumption.
  - exfalso. apply Hnv. exact Hv_s.
Qed.

Lemma tr_closure_nonvalue : forall T s,
  locally_closed s ->
  strongly_normalizing s ->
  ~ value s ->
  (forall s', step s s' -> tr T s') ->
  tr T s.
Proof.
  induction T; intros s Hlc Hsn Hnv Hred.
  - simpl. split; assumption.
  - simpl. split; [exact Hlc | split; [exact Hsn |]].
    intros w Hw.
    apply IHT2.
    + apply lc_app_pres; [exact Hlc | apply tr_lc in Hw; exact Hw].
    + apply SN_intro. intros r Hr.
      destruct (step_app_nonvalue s w r Hlc Hnv Hr) as [s' [Hs' Heq]].
      rewrite Heq. apply tr_sn with (T := T2). apply tr_app with (T1 := T1).
      * apply Hred. exact Hs'.
      * exact Hw.
    + intro Hv. inversion Hv.
    + intros r Hr.
      destruct (step_app_nonvalue s w r Hlc Hnv Hr) as [s' [Hs' Heq]].
      rewrite Heq. apply tr_app with (T1 := T1).
      * apply Hred. exact Hs'.
      * exact Hw.
Qed.

Lemma tr_abs_app : forall T1 T2 body u,
  locally_closed (tm_abs T1 body) ->
  (forall v, tr T1 v -> tr T2 (open body v)) ->
  tr T1 u ->
  tr T2 (tm_app (tm_abs T1 body) u).
Proof.
  intros T1 T2 body u Hlc Hbody Htr.
  assert (Hsn : strongly_normalizing u) by (apply tr_sn in Htr; exact Htr).
  revert Htr.
  induction Hsn as [u Hstep IH]; intros Htr.
  apply tr_closure_nonvalue with (s := tm_app (tm_abs T1 body) u).
  - apply lc_app_pres; [exact Hlc | apply tr_lc in Htr; exact Htr].
  - apply sn_abs_app with (T1 := T1).
    + apply SN_intro. exact Hstep.
    + exact Htr.
    + intros v Hv. apply tr_sn with (T := T2). apply Hbody. exact Hv.
  - intro Hv. inversion Hv.
  - intros s' Hs'.
    destruct (step_abs_app_inv T1 body u s' Hs') as [[Hv Heq] | [u' [Hstep' Heq]]].
    + rewrite Heq. apply Hbody. exact Htr.
    + rewrite Heq. apply IH; [exact Hstep' | apply tr_step with (t := u); assumption].
Qed.

(* ---------- Substitution and opening ---------- *)

Lemma subst_open_rec_fvar : forall t k sigma x u,
  (forall y, locally_closed (sigma y)) ->
  locally_closed u ->
  ~ In x (fv t) ->
  subst (extend x u sigma) (open_rec k (tm_fvar x) t) = open_rec k u (subst sigma t).
Proof.
  induction t; intros k sigma x u Hsig Hlu Hx; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply extend_eq.
    + reflexivity.
  - assert (Hxa : x <> a).
    { intro E. apply Hx. subst. left. reflexivity. }
    unfold extend. apply Nat.eqb_neq in Hxa. rewrite Hxa.
    rewrite open_rec_lc_at with (k := k); [reflexivity |].
    apply lc_at_mono with (k := 0); [apply Hsig | lia].
  - f_equal.
    + apply IHt1; [exact Hsig | exact Hlu |].
      intro Hc. apply Hx. apply in_app_iff. left. exact Hc.
    + apply IHt2; [exact Hsig | exact Hlu |].
      intro Hc. apply Hx. apply in_app_iff. right. exact Hc.
  - f_equal. apply IHt with (k := S k); [exact Hsig | exact Hlu | exact Hx].
  - reflexivity.
  - reflexivity.
Qed.

Lemma subst_open_fvar : forall t sigma x u,
  (forall y, locally_closed (sigma y)) ->
  locally_closed u ->
  ~ In x (fv t) ->
  subst (extend x u sigma) (open t (tm_fvar x)) = open (subst sigma t) u.
Proof.
  intros. unfold open. apply subst_open_rec_fvar; assumption.
Qed.

(* ---------- Typed terms are locally closed ---------- *)

Lemma has_type_lc : forall Gamma t T, has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T H. induction H as
    [Gamma x T Heq
    | L Gamma T1 T2 t1 Hbody IHbody
    | Gamma t1 t2 T1 T2 Hty1 IH1 Hty2 IH2
    | Gamma | Gamma].
  - apply lc_fvar.
  - unfold locally_closed. apply lc_abs.
    pose proof (fresh_notin (L ++ fv t1)) as Hx.
    assert (HxL : ~ In (fresh (L ++ fv t1)) L).
    { intro Hc. apply Hx. apply in_app_iff. left. exact Hc. }
    pose proof (IHbody (fresh (L ++ fv t1)) HxL) as Hbodylc.
    unfold locally_closed in Hbodylc.
    apply lc_open_fvar_inv with (k := 0) (x := fresh (L ++ fv t1)).
    exact Hbodylc.
  - apply lc_app_pres; assumption.
  - apply lc_true.
  - apply lc_false.
Qed.

(* ---------- The fundamental theorem ---------- *)

Definition env_sem (Gamma : context) (sigma : atom -> tm) : Prop :=
  forall x T, Gamma x = Some T -> tr T (sigma x).

Lemma update_eq : forall Gamma x T, update Gamma x T x = Some T.
Proof. intros. unfold update. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma update_neq : forall Gamma x y T, x <> y -> update Gamma x T y = Gamma y.
Proof. intros. unfold update. apply Nat.eqb_neq in H. rewrite H. reflexivity. Qed.

Lemma fundamental : forall Gamma t T,
  has_type Gamma t T ->
  forall sigma,
    (forall x, locally_closed (sigma x)) ->
    env_sem Gamma sigma ->
    tr T (subst sigma t).
Proof.
  intros Gamma t T Hty.
  induction Hty as
    [Gamma x T Heq
    | L Gamma T1 T2 t1 Hbody IHbody
    | Gamma t1 t2 T1 T2 Hty1 IH1 Hty2 IH2
    | Gamma | Gamma];
    intros sigma Hlcs Henv.
  - (* T_Var *) simpl. apply Henv. exact Heq.
  - (* T_Abs *) simpl.
    assert (Ht1 : lc_at 1 t1).
    { apply lc_abs_inv with (T := T1).
      exact (has_type_lc Gamma (tm_abs T1 t1) (Ty_Arrow T1 T2)
               (T_Abs L Gamma T1 T2 t1 Hbody)). }
    assert (Hlcabs : locally_closed (tm_abs T1 (subst sigma t1))).
    { unfold locally_closed. apply lc_abs.
      apply lc_at_subst with (sigma := sigma); assumption. }
    split.
    + exact Hlcabs.
    + split.
      * apply SN_intro. intros t' Hstep. inversion Hstep.
      * intros u Hu.
        apply tr_abs_app with (body := subst sigma t1).
        -- exact Hlcabs.
        -- intros v Hv.
           pose proof (fresh_notin (L ++ fv t1)) as Hx.
           assert (HxL : ~ In (fresh (L ++ fv t1)) L).
           { intro Hc. apply Hx. apply in_app_iff. left. exact Hc. }
           assert (Hxfv : ~ In (fresh (L ++ fv t1)) (fv t1)).
           { intro Hc. apply Hx. apply in_app_iff. right. exact Hc. }
           specialize (IHbody (fresh (L ++ fv t1)) HxL
                        (extend (fresh (L ++ fv t1)) v sigma)).
           assert (Hlcs' : forall y,
                     locally_closed (extend (fresh (L ++ fv t1)) v sigma y)).
           { intro y. unfold extend.
             destruct (Nat.eqb (fresh (L ++ fv t1)) y) eqn:E.
             - apply tr_lc in Hv. exact Hv.
             - apply Hlcs. }
           assert (Henv' : env_sem (update Gamma (fresh (L ++ fv t1)) T1)
                           (extend (fresh (L ++ fv t1)) v sigma)).
           { intros y T' Hy. unfold update in Hy.
             destruct (Nat.eqb (fresh (L ++ fv t1)) y) eqn:E.
             - apply Nat.eqb_eq in E. subst y. injection Hy as HTeq. subst T'.
               rewrite extend_eq. exact Hv.
             - apply Nat.eqb_neq in E. rewrite extend_neq; [|exact E].
               apply Henv. exact Hy. }
           specialize (IHbody Hlcs' Henv').
           assert (Heq : subst (extend (fresh (L ++ fv t1)) v sigma)
                           (open t1 (tm_fvar (fresh (L ++ fv t1)))) =
                         open (subst sigma t1) v).
           { apply subst_open_fvar; [exact Hlcs | | exact Hxfv].
             apply tr_lc in Hv. exact Hv. }
           rewrite Heq in IHbody. exact IHbody.
        -- exact Hu.
  - (* T_App *) simpl.
    apply tr_app with (T1 := T1).
    + exact (IH1 sigma Hlcs Henv).
    + exact (IH2 sigma Hlcs Henv).
  - (* T_True *) simpl. split.
    + apply lc_true.
    + apply SN_intro. intros t' Hstep. inversion Hstep.
  - (* T_False *) simpl. split.
    + apply lc_false.
    + apply SN_intro. intros t' Hstep. inversion Hstep.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  assert (Htr : tr T (subst (fun x => tm_fvar x) t)).
  { apply (fundamental empty t T Hty).
    - intro x. apply lc_fvar.
    - intros x T' Hx. unfold empty in Hx. discriminate Hx. }
  rewrite subst_id in Htr.
  apply tr_sn in Htr.
  exact Htr.
Qed.

End STLCNormalizationNoneHardTask.
