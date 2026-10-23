(** STLC call-by-value strong-normalization benchmark.
    Non-deterministic choice is included; if-then-else and recursion are not. *)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Relations.Relation_Definitions.

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

Fixpoint subst (rho : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => rho x
  | tm_app t1 t2 => tm_app (subst rho t1) (subst rho t2)
  | tm_abs T t1 => tm_abs T (subst rho t1)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_choice t1 t2 => tm_choice (subst rho t1) (subst rho t2)
  end.

Fixpoint reducible (T : ty) (t : tm) : Prop :=
  match T with
  | Ty_Bool => locally_closed t /\ strongly_normalizing t
  | Ty_Arrow A B => locally_closed t /\ strongly_normalizing t /\
      (forall u, reducible A u -> reducible B (tm_app t u))
  end.

Transparent reducible.
Lemma reducible_lc : forall T t, reducible T t -> locally_closed t.
Proof.
  destruct T; intros t H.
  - change (locally_closed t /\ strongly_normalizing t) in H.
    exact (proj1 H).
  - change (locally_closed t /\ strongly_normalizing t /\
      (forall u, reducible T1 u -> reducible T2 (tm_app t u))) in H.
    exact (proj1 H).
Qed.
Opaque reducible.

Definition realizes (Gamma : context) (rho : atom -> tm) : Prop :=
  (forall x T, Gamma x = Some T -> reducible T (rho x)) /\
  (forall x, locally_closed (rho x)).

Lemma lc_mono : forall k t, lc_at k t -> lc_at (S k) t.
Proof.
  intros k t H; induction H; try constructor; try lia; eauto.
Qed.

Lemma lc_open_rec : forall k t u,
  lc_at (S k) t -> lc_at k u -> lc_at k (open_rec k u t).
Proof.
  intros k t; revert k; induction t; intros k u Hlc Hu;
    inversion Hlc; subst; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst; exact Hu.
    + apply lc_bvar. apply Nat.eqb_neq in E; lia.
  - constructor.
  - constructor; [eapply IHt1 | eapply IHt2]; eauto.
  - constructor. eapply IHt; [eassumption | eapply lc_mono; eassumption].
  - constructor.
  - constructor.
  - constructor; [eapply IHt1 | eapply IHt2]; eauto.
Qed.

Lemma step_lc : forall t t', t --> t' -> locally_closed t -> locally_closed t'.
Proof.
  intros t t' H; induction H; intros Hlc.
  - unfold locally_closed in *. inversion Hlc; subst.
    inversion H4; subst. eapply lc_open_rec; eauto.
  - unfold locally_closed in *. inversion Hlc; subst. constructor; eauto.
  - unfold locally_closed in *. inversion Hlc; subst. constructor; eauto.
  - unfold locally_closed in *. inversion Hlc; subst. assumption.
  - unfold locally_closed in *. inversion Hlc; subst. assumption.
Qed.

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v H; destruct H.
  - assumption.
  - unfold locally_closed; constructor.
  - unfold locally_closed; constructor.
Qed.

Lemma sn_step : forall t t', t --> t' -> strongly_normalizing t ->
  strongly_normalizing t'.
Proof. intros t t' H Hsn; inversion Hsn as [z Hnext]; subst; eauto. Qed.

Lemma value_sn : forall v, value v -> strongly_normalizing v.
Proof. intros v Hv; destruct Hv; constructor; intros y Hstep'; inversion Hstep'. Qed.

Lemma reducible_step : forall T t t', t --> t' -> reducible T t -> reducible T t'.
Proof.
  Transparent reducible.
  intros T; induction T as [|A IHA B IHB]; intros t t' H HR.
  - change (locally_closed t /\ strongly_normalizing t) in HR.
    Opaque reducible. destruct HR as [Hlc SN]. Transparent reducible. split.
    + eapply step_lc; eauto.
    + eapply sn_step; eauto.
  - change (locally_closed t /\ strongly_normalizing t /\
      (forall u, reducible A u -> reducible B (tm_app t u))) in HR.
    Opaque reducible.
    destruct HR as [Hlc [SN Hred]].
    change (locally_closed t' /\ strongly_normalizing t' /\
      (forall u, reducible A u -> reducible B (tm_app t' u))).
    Opaque reducible.
    split.
    + eapply step_lc; eauto.
    + split.
      * eapply sn_step; eauto.
      * intros u Hu. eapply IHB.
        -- apply ST_App1; [exact H | apply reducible_lc with (T := A); exact Hu].
        -- apply Hred; assumption.
Qed.
Opaque reducible.

Lemma lc_open_irrel : forall depth k t u,
  lc_at depth t -> depth <= k -> open_rec k u t = t.
Proof.
  intros depth k t u H; revert depth k u H.
  induction t; intros d k' u Hlc Hle; inversion Hlc; subst; simpl.
  - assert (k' <> n) as Hneq by lia. apply Nat.eqb_neq in Hneq. rewrite Hneq; reflexivity.
  - reflexivity.
  - f_equal; [eapply IHt1 | eapply IHt2]; eauto.
  - f_equal. eapply IHt; eauto; lia.
  - reflexivity.
  - reflexivity.
  - f_equal; [eapply IHt1 | eapply IHt2]; eauto.
Qed.

Lemma subst_open_rec : forall k t u rho,
  (forall x, locally_closed (rho x)) ->
  subst rho (open_rec k u t) = open_rec k (subst rho u) (subst rho t).
Proof.
  intros k t; revert k; induction t; intros k u rho Hrho; simpl.
  - destruct (Nat.eqb k n); simpl; reflexivity.
  - unfold locally_closed in Hrho. rewrite (lc_open_irrel 0 k (rho a) (subst rho u) (Hrho a)) by lia. reflexivity.
  - rewrite IHt1, IHt2; try assumption; reflexivity.
  - rewrite IHt with (k := S k) (rho := rho); try assumption; reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2; try assumption; reflexivity.
Qed.

Lemma subst_open : forall t u rho,
  (forall x, locally_closed (rho x)) ->
  subst rho (open t u) = open (subst rho t) (subst rho u).
Proof. intros t u rho Hrho; unfold open; apply subst_open_rec; exact Hrho. Qed.

Lemma lc_open_inv : forall k t x,
  lc_at k (open_rec k (tm_fvar x) t) -> lc_at (S k) t.
Proof.
  intros k t; revert k; induction t; intros k x Hlc; simpl in Hlc.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst. constructor; lia.
    + inversion Hlc; subst. constructor. apply Nat.eqb_neq in E; lia.
  - constructor.
  - inversion Hlc; subst. constructor; [eapply IHt1 | eapply IHt2]; eassumption.
  - inversion Hlc; subst. constructor. eapply IHt. eassumption.
  - constructor.
  - constructor.
  - inversion Hlc; subst. constructor; [eapply IHt1 | eapply IHt2]; eassumption.
Qed.

Fixpoint fv (t : tm) : list atom :=
  match t with
  | tm_bvar n => nil
  | tm_fvar x => cons x nil
  | tm_app t1 t2 => fv t1 ++ fv t2
  | tm_abs T t1 => fv t1
  | tm_true => nil
  | tm_false => nil
  | tm_choice t1 t2 => fv t1 ++ fv t2
  end.

Lemma subst_agree : forall t rho1 rho2,
  (forall x, In x (fv t) -> rho1 x = rho2 x) -> subst rho1 t = subst rho2 t.
Proof.
  induction t; intros rho1 rho2 H; simpl; try reflexivity.
  - apply H. simpl; auto.
  - f_equal.
    + apply IHt1. intros x Hx. apply H. apply in_or_app; auto.
    + apply IHt2. intros x Hx. apply H. apply in_or_app; auto.
  - f_equal. apply IHt. exact H.
  - f_equal.
    + apply IHt1. intros x Hx. apply H. apply in_or_app; auto.
    + apply IHt2. intros x Hx. apply H. apply in_or_app; auto.
Qed.

Lemma in_le_max : forall xs x, In x xs -> x <= fold_right Nat.max 0 xs.
Proof.
  induction xs as [|a xs IH]; simpl; intros x Hin; [contradiction|].
  destruct Hin as [->|Hin].
  - apply Nat.le_max_l.
  - eapply Nat.le_trans; [eapply IH; exact Hin | apply Nat.le_max_r].
Qed.

Lemma fresh_atom : forall xs : list atom, exists x, ~ In x xs.
Proof.
  intros xs. exists (S (fold_right Nat.max 0 xs)).
  intros Hin. pose proof (in_le_max xs _ Hin). lia.
Qed.

Lemma lc_lift_n : forall k t, lc_at 0 t -> lc_at k t.
Proof.
  intros k; induction k; intros t H.
  - exact H.
  - apply lc_mono. apply IHk. exact H.
Qed.

Lemma subst_lc : forall rho k t,
  (forall x, locally_closed (rho x)) -> lc_at k t -> lc_at k (subst rho t).
Proof.
  intros rho k t; revert k; induction t; intros k Hrho Hlc;
    inversion Hlc; subst; simpl.
  - constructor; assumption.
  - unfold locally_closed in Hrho. apply lc_lift_n. apply Hrho.
  - constructor; [eapply IHt1 | eapply IHt2]; eauto.
  - constructor. eapply IHt; eauto.
  - constructor.
  - constructor.
  - constructor; [eapply IHt1 | eapply IHt2]; eauto.
Qed.

Lemma typing_lc : forall Gamma t T, has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T H; induction H.
  - unfold locally_closed; constructor.
  - destruct (fresh_atom L) as [x Hx].
    apply lc_abs. eapply lc_open_inv.
    match goal with
    | IH : forall y, ~ In y L -> locally_closed (open ?body (tm_fvar y)) |- _ =>
        apply (IH x Hx)
    end.
  - unfold locally_closed in *. constructor; assumption.
  - unfold locally_closed; constructor.
  - unfold locally_closed; constructor.
  - unfold locally_closed in *. constructor; assumption.
Qed.

Definition branch_pair (z z1 z2 : tm) : Prop :=
  locally_closed z /\ ~ value z /\
  (forall w, z --> w -> w = z1 \/ w = z2) /\
  (z --> z1) /\ (z --> z2).

Lemma branch_pair_app : forall z z1 z2 u,
  branch_pair z z1 z2 -> locally_closed u ->
  branch_pair (tm_app z u) (tm_app z1 u) (tm_app z2 u).
Proof.
  intros z z1 z2 u [Hz [Hnv [Hsteps [H1 H2]]]] Hu.
  repeat split.
  - unfold locally_closed in *. constructor; assumption.
  - intros Hv; inversion Hv.
  - intros w Hstep. inversion Hstep; subst.
    + exfalso. apply Hnv. constructor. exact H3.
    + destruct (Hsteps _ H3) as [E|E]; [left; subst; reflexivity | right; subst; reflexivity].
    + contradiction.
  - apply ST_App1; assumption.
  - apply ST_App1; assumption.
Qed.

Lemma branch_pair_choice : forall x y,
  locally_closed x -> locally_closed y ->
  branch_pair (tm_choice x y) x y.
Proof.
  intros x y Hx Hy. repeat split.
  - unfold locally_closed in *. constructor; assumption.
  - intros Hv; inversion Hv.
  - intros w Hstep; inversion Hstep; subst; auto.
  - apply ST_ChoiceLeft; assumption.
  - apply ST_ChoiceRight; assumption.
Qed.

Lemma sn_from_steps : forall z z1 z2,
  branch_pair z z1 z2 -> strongly_normalizing z1 -> strongly_normalizing z2 ->
  strongly_normalizing z.
Proof.
  intros z z1 z2 [_ [_ [Hsteps _]]] SN1 SN2. constructor; intros w Hw.
  destruct (Hsteps w Hw) as [E|E]; subst; assumption.
Qed.

Lemma reducible_arrow_elim : forall A B t u,
  reducible (Ty_Arrow A B) t -> reducible A u -> reducible B (tm_app t u).
Proof.
  Transparent reducible. intros A B t u H Hu.
  change (locally_closed t /\ strongly_normalizing t /\
    (forall v, reducible A v -> reducible B (tm_app t v))) in H.
  exact (proj2 (proj2 H) u Hu).
Qed.
Opaque reducible.

Lemma reducible_from_steps : forall T z z1 z2,
  branch_pair z z1 z2 -> reducible T z1 -> reducible T z2 -> reducible T z.
Proof.
  Transparent reducible.
  intros T; induction T as [|A IHA B IHB]; intros z z1 z2 BP R1 R2.
  - change (locally_closed z1 /\ strongly_normalizing z1) in R1.
    change (locally_closed z2 /\ strongly_normalizing z2) in R2.
    change (locally_closed z /\ strongly_normalizing z).
    destruct BP as [Hz [Hnv [Hsteps [Hleft Hright]]]]. split; [exact Hz|].
    eapply sn_from_steps.
    + exact (conj Hz (conj Hnv (conj Hsteps (conj Hleft Hright)))).
    + exact (proj2 R1).
    + exact (proj2 R2).
  - change (locally_closed z1 /\ strongly_normalizing z1 /\
      (forall u, reducible A u -> reducible B (tm_app z1 u))) in R1.
    change (locally_closed z2 /\ strongly_normalizing z2 /\
      (forall u, reducible A u -> reducible B (tm_app z2 u))) in R2.
    change (locally_closed z /\ strongly_normalizing z /\
      (forall u, reducible A u -> reducible B (tm_app z u))).
    destruct BP as [Hz [Hnv [Hsteps [Hleft Hright]]]].
    split; [exact Hz|]. split.
    + eapply sn_from_steps.
      * exact (conj Hz (conj Hnv (conj Hsteps (conj Hleft Hright)))).
      * exact (proj1 (proj2 R1)).
      * exact (proj1 (proj2 R2)).
    + intros u Hu. eapply IHB.
      * apply branch_pair_app.
        -- exact (conj Hz (conj Hnv (conj Hsteps (conj Hleft Hright)))).
        -- apply reducible_lc with (T:=A); exact Hu.
      * apply (proj2 (proj2 R1) u Hu).
      * apply (proj2 (proj2 R2) u Hu).
Qed.
Opaque reducible.

Lemma reducible_sn : forall T t, reducible T t -> strongly_normalizing t.
Proof.
  Transparent reducible. destruct T; intros t H.
  - change (locally_closed t /\ strongly_normalizing t) in H. exact (proj2 H).
  - change (locally_closed t /\ strongly_normalizing t /\
      (forall u, reducible T1 u -> reducible T2 (tm_app t u))) in H.
    exact (proj1 (proj2 H)).
Qed.
Opaque reducible.

Lemma sn_induction : forall (P : tm -> Prop),
  (forall t, (forall t', t --> t' -> P t') -> P t) ->
  forall t, strongly_normalizing t -> P t.
Proof.
  intros P HP t Hsn. induction Hsn as [t Hnext IH].
  apply HP. intros t' Hstep. apply IH; assumption.
Qed.

Lemma reducible_from_all_steps : forall T z,
  locally_closed z -> ~ value z ->
  (forall z', z --> z' -> reducible T z') -> reducible T z.
Proof.
  Transparent reducible.
  intros T; induction T as [|A IHA B IHB]; intros z Hz Hnv Hnext.
  - change (locally_closed z /\ strongly_normalizing z).
    split; [exact Hz|]. constructor; intros z' Hstep. apply reducible_sn with (T:=Ty_Bool). apply Hnext; assumption.
  - change (locally_closed z /\ strongly_normalizing z /\
      (forall u, reducible A u -> reducible B (tm_app z u))).
    split; [exact Hz|]. split.
    + constructor; intros z' Hstep. apply reducible_sn with (T:=Ty_Arrow A B). apply Hnext; assumption.
    + intros u Hu. eapply IHB.
      * unfold locally_closed in *. constructor; [exact Hz|apply reducible_lc with (T:=A); exact Hu].
      * intros Hv; inversion Hv.
      * intros w Hstep. inversion Hstep; subst.
        -- exfalso. apply Hnv. constructor. exact H1.
        -- apply reducible_arrow_elim with (A:=A).
           ++ apply Hnext; exact H1.
           ++ exact Hu.
        -- exfalso. apply Hnv. assumption.
Qed.
Opaque reducible.

Definition extend (rho : atom -> tm) (x : atom) (v : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then v else rho y.

Lemma realizes_extend : forall Gamma rho x A v,
  realizes Gamma rho -> reducible A v ->
  realizes (update Gamma x A) (extend rho x v).
Proof.
  intros Gamma rho x A v [Hrel Hclosed] Hv. split.
  - intros y T Hlookup. unfold update in Hlookup. unfold extend.
    destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E; subst. inversion Hlookup; subst. exact Hv.
    + apply Hrel with (x:=y); assumption.
  - intros y. unfold extend. destruct (Nat.eqb x y); [apply reducible_lc with (T:=A); exact Hv|apply Hclosed].
Qed.

Lemma reducible_abs_app : forall A B body u,
  locally_closed (tm_abs A body) ->
  (forall v, reducible A v -> reducible B (open body v)) ->
  reducible A u ->
  reducible B (tm_app (tm_abs A body) u).
Proof.
  intros A B body u Habs Hbody Hu.
  assert (Hind : forall w, reducible A w ->
      reducible B (tm_app (tm_abs A body) w)).
  { intros w HAw.
    refine (@sn_induction
      (fun w => reducible A w -> reducible B (tm_app (tm_abs A body) w))
      _ w (@reducible_sn A w HAw) HAw).
    intros w' IH HAw'. eapply reducible_from_all_steps.
    - unfold locally_closed in *. constructor.
      + exact Habs.
      + apply reducible_lc with (T:=A); exact HAw'.
    - intros Hv; inversion Hv.
    - intros q Hq. inversion Hq; subst.
      + apply Hbody; assumption.
      + inversion H1.
      + apply (IH t2' H3). eapply reducible_step; eassumption.
  }
  apply Hind; exact Hu.
Qed.

Lemma fundamental : forall Gamma t T,
  has_type Gamma t T -> forall rho, realizes Gamma rho ->
  reducible T (subst rho t).
Proof.
  intros Gamma t T Hty. induction Hty; intros rho Hreal.
  - destruct Hreal as [Hrel Hclosed]. eapply Hrel; eauto.
  - destruct Hreal as [Hrel Hclosed].
    assert (Hlc : locally_closed (tm_abs T1 (subst rho t1))).
    { assert (Horig : locally_closed (tm_abs T1 t1)).
      { destruct (fresh_atom L) as [x Hx]. unfold locally_closed. apply lc_abs.
        eapply lc_open_inv.
        exact (@typing_lc (update Gamma x T1) (open t1 (tm_fvar x)) T2 (H x Hx)). }
      unfold locally_closed. simpl. exact (@subst_lc rho 0 (tm_abs T1 t1) Hclosed Horig). }
    Transparent reducible.
    change (locally_closed (tm_abs T1 (subst rho t1)) /\
      strongly_normalizing (tm_abs T1 (subst rho t1)) /\
      (forall u, reducible T1 u -> reducible T2 (tm_app (tm_abs T1 (subst rho t1)) u))).
    Opaque reducible.
    split; [exact Hlc|]. split.
    + apply value_sn. constructor. exact Hlc.
    + assert (Hbody_sem : forall u, reducible T1 u ->
          reducible T2 (open (subst rho t1) u)).
      { intros u Hu.
      destruct (fresh_atom (L ++ fv t1)) as [x Hfresh].
      assert (HxL : ~ In x L) by (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
      assert (Hxfv : ~ In x (fv t1)) by (intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
      set (rho' := extend rho x u).
      assert (Hreal' : realizes (update Gamma x T1) rho').
      { unfold rho'. apply realizes_extend; [split; assumption|exact Hu]. }
      assert (Hbody : reducible T2 (subst rho' (open t1 (tm_fvar x)))).
      { match goal with
        | IH : forall y, ~ In y L -> forall r, realizes (update Gamma y T1) r ->
              reducible T2 (subst r (open t1 (tm_fvar y))) |- _ =>
            apply (IH x HxL rho' Hreal')
        end. }
      assert (Hagree : forall y, In y (fv t1) -> rho' y = rho y).
      { intros y Hy. unfold rho', extend. destruct (Nat.eqb x y) eqn:E.
        - apply Nat.eqb_eq in E; subst. exfalso; apply Hxfv; exact Hy.
        - reflexivity. }
      assert (Hclosed' : forall y, locally_closed (rho' y)).
      { intros y. unfold rho', extend. destruct (Nat.eqb x y); [apply reducible_lc with (T:=T1); exact Hu|apply Hclosed]. }
      rewrite (subst_open t1 (tm_fvar x) rho' Hclosed') in Hbody.
      replace (subst rho' t1) with (subst rho t1) in Hbody.
      2: { symmetry. apply subst_agree. exact Hagree. }
      unfold rho', extend in Hbody. cbn [subst] in Hbody.
      rewrite Nat.eqb_refl in Hbody.
      exact Hbody. }
      intros u Hu. eapply reducible_abs_app; [exact Hlc|exact Hbody_sem|exact Hu].
  - eapply reducible_arrow_elim; eauto.
  - Transparent reducible. change (locally_closed tm_true /\ strongly_normalizing tm_true).
    split; [unfold locally_closed; constructor|apply value_sn; constructor].
  - Transparent reducible. change (locally_closed tm_false /\ strongly_normalizing tm_false).
    split; [unfold locally_closed; constructor|apply value_sn; constructor].
  - eapply reducible_from_steps.
    + apply branch_pair_choice.
      * eapply reducible_lc. match goal with
        | IH : forall r, realizes Gamma r -> reducible T (subst r t1) |- _ => exact (IH rho Hreal)
        end.
      * eapply reducible_lc. match goal with
        | IH : forall r, realizes Gamma r -> reducible T (subst r t2) |- _ => exact (IH rho Hreal)
        end.
    + match goal with
      | IH : forall r, realizes Gamma r -> reducible T (subst r t1) |- _ => exact (IH rho Hreal)
      end.
    + match goal with
      | IH : forall r, realizes Gamma r -> reducible T (subst r t2) |- _ => exact (IH rho Hreal)
      end.
Qed.

Lemma fv_open_incl : forall k t u x,
  In x (fv t) -> In x (fv (open_rec k u t)).
Proof.
  intros k t; revert k; induction t; intros k u x Hin; simpl in *.
  - contradiction.
  - exact Hin.
  - apply in_app_iff in Hin. apply in_app_iff. destruct Hin as [H|H].
    + left; eapply IHt1; exact H.
    + right; eapply IHt2; exact H.
  - eapply IHt; exact Hin.
  - contradiction.
  - contradiction.
  - apply in_app_iff in Hin. apply in_app_iff. destruct Hin as [H|H].
    + left; eapply IHt1; exact H.
    + right; eapply IHt2; exact H.
Qed.

Lemma typing_fv : forall Gamma t T, has_type Gamma t T ->
  forall x, In x (fv t) -> exists U, Gamma x = Some U.
Proof.
  intros Gamma t T D; induction D; intros y Hy.
  - simpl in Hy. destruct Hy as [E|[]]. subst. eauto.
  - destruct (fresh_atom (app L (cons y nil))) as [x Hfresh].
    assert (HxL : ~ In x L) by (intro Hnot; apply Hfresh; apply in_or_app; left; exact Hnot).
    assert (Hxy : x <> y) by (intro Hneq; subst; apply Hfresh; apply in_or_app; right; simpl; auto).
    assert (Hyopen : In y (fv (open t1 (tm_fvar x)))).
    { unfold open. eapply fv_open_incl. exact Hy. }
    match goal with
    | IH : forall z, ~ In z L -> forall w, In w (fv (open t1 (tm_fvar z))) ->
          exists U, update Gamma z T1 w = Some U |- _ =>
        destruct (IH x HxL y Hyopen) as [U Hlookup]
    end.
    exists U. unfold update in Hlookup.
    destruct (Nat.eqb x y) eqn:E; [apply Nat.eqb_eq in E; contradiction|exact Hlookup].
  - simpl in Hy. apply in_app_iff in Hy. destruct Hy as [Hy|Hy].
    + eapply IHD1; eauto.
    + eapply IHD2; eauto.
  - simpl in Hy; contradiction.
  - simpl in Hy; contradiction.
  - simpl in Hy. apply in_app_iff in Hy. destruct Hy as [Hy|Hy]; [eapply IHD1|eapply IHD2]; eauto.
Qed.

Lemma empty_typed_fv_nil : forall t T,
  has_type empty t T -> fv t = nil.
Proof.
  intros t T Hty. destruct (fv t) as [|x xs] eqn:E; [reflexivity|].
  assert (Hin : In x (fv t)) by (rewrite E; simpl; auto).
  pose proof (@typing_fv empty t T Hty x Hin) as [U HU].
  discriminate.
Qed.

Lemma subst_id : forall t, subst (fun x => tm_fvar x) t = t.
Proof.
  induction t; simpl; try rewrite IHt; try rewrite IHt1; try rewrite IHt2; reflexivity.
Qed.

Theorem strong_normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  assert (Hreal : realizes empty (fun _ => tm_true)).
  { split.
    - intros x U Hx. discriminate.
    - intros x; unfold locally_closed; constructor. }
  pose proof (fundamental empty t T Hty (fun _ => tm_true) Hreal) as HR.
  assert (Hfv : fv t = nil) by (eapply empty_typed_fv_nil; exact Hty).
  assert (Hsub : subst (fun _ => tm_true) t = t).
  { pose proof (subst_agree t (fun _ => tm_true) (fun x => tm_fvar x)) as Hagree.
    assert (Hpoint : forall x, In x (fv t) -> tm_true = tm_fvar x).
    { intros x Hin. rewrite Hfv in Hin. contradiction. }
    specialize (Hagree Hpoint). rewrite subst_id in Hagree. exact Hagree. }
  rewrite Hsub in HR. exact (@reducible_sn T t HR).
Qed.

End STLCNormalizationNondeterminismHardTask.
