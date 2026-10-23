(** STLC CBV strong-normalization benchmark, Hard variant.
    Features: if-nondeterminism. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Relations.Relation_Definitions Lia.
Import ListNotations.

Module STLCNormalizationIfNondeterminismHardTask.

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

(* Reducibility candidates.  The extra locally-closed conjunct is useful
   because the CBV rules explicitly require it at their inactive positions. *)
Fixpoint red (T : ty) (t : tm) : Prop :=
  strongly_normalizing t /\
  locally_closed t /\
  match T with
  | Ty_Bool => True
  | Ty_Arrow A B => forall v, red A v -> red B (tm_app t v)
  end.

Lemma sn_of_red : forall T t, red T t -> strongly_normalizing t.
Proof. intros [|A B] t H; simpl in H; exact (proj1 H). Qed.

Lemma lc_of_red : forall T t, red T t -> locally_closed t.
Proof. intros [|A B] t H; simpl in H; exact (proj1 (proj2 H)). Qed.

Lemma red_bool : forall t, red Ty_Bool t ->
  strongly_normalizing t /\ locally_closed t.
Proof. intros t H; simpl in H; split;
  [exact (proj1 H)|exact (proj1 (proj2 H))]. Qed.

Lemma sn_step : forall t, strongly_normalizing t ->
  forall t', t --> t' -> strongly_normalizing t'.
Proof.
  intros t H. inversion H. eauto.
Qed.

Lemma value_no_step : forall v, value v ->
  forall v', ~ v --> v'.
Proof.
  intros v Hv v' Hs; destruct Hv; inversion Hs.
Qed.

Lemma abs_no_step : forall T t, locally_closed (tm_abs T t) ->
  forall t', ~ tm_abs T t --> t'.
Proof.
  intros T t Hlc t' Hs; inversion Hs.
Qed.

Lemma lc_mono : forall k k' t, k <= k' -> lc_at k t -> lc_at k' t.
Proof.
  intros k k' t Hkk' Hlc.
  revert k' Hkk'.
  induction Hlc; intros k' Hkk'.
  - constructor; lia.
  - constructor; assumption.
  - constructor; [apply IHHlc1; assumption|apply IHHlc2; assumption].
  - constructor. apply IHHlc. lia.
  - constructor.
  - constructor.
  - constructor; [apply IHHlc1; assumption|apply IHHlc2; assumption|
      apply IHHlc3; assumption].
  - constructor; [apply IHHlc1; assumption|apply IHHlc2; assumption].
Qed.

Lemma lc_open_rec : forall k t u,
  lc_at (S k) t -> lc_at k u -> lc_at k (open_rec k u t).
Proof.
  intros k t.
  revert k.
  induction t; intros k u Ht Hu; simpl in *; inversion Ht; subst.
  - destruct (Nat.eqb k n) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst. exact Hu.
    + constructor. apply Nat.eqb_neq in Heq. lia.
  - constructor.
  - constructor; [apply IHt1; assumption|apply IHt2; assumption].
  - constructor. apply IHt.
    + assumption.
    + apply (lc_mono k (S k) u); [lia|assumption].
  - constructor.
  - constructor.
  - constructor; [apply IHt1; assumption|apply IHt2; assumption|
      apply IHt3; assumption].
  - constructor; [apply IHt1; assumption|apply IHt2; assumption].
Qed.

Lemma lc_step : forall t t', locally_closed t -> t --> t' -> locally_closed t'.
Proof.
  intros t t' Hlc Hs.
  induction Hs; inversion Hlc; subst; simpl in *;
    eauto using lc_open_rec.
  all: try (unfold locally_closed; constructor).
  all: try solve [apply IHHs; assumption].
  all: try assumption.
  all: unfold locally_closed;
    match goal with
    | H : lc_at _ (tm_abs _ _) |- _ => inversion H; subst
    end;
    eapply lc_open_rec; eauto.
Qed.

Lemma red_down : forall T t t', red T t -> t --> t' -> red T t'.
Proof.
  induction T as [|A IHA B IHB]; intros t t' Hred Hstep.
  - simpl in Hred. destruct Hred as [Hsn [Hlc _]].
    split; [apply sn_step with (t := t); assumption|].
    split; [apply lc_step with (t := t); assumption|trivial].
  - simpl in Hred. destruct Hred as [Hsn [Hlc Har]].
    split; [apply sn_step with (t := t); assumption|].
    split; [apply lc_step with (t := t); assumption|].
    intros v Hv.
    apply IHB with (t := tm_app t v).
    + apply Har; exact Hv.
    + apply ST_App1.
      * exact Hstep.
      * exact (lc_of_red A v Hv).
Qed.

(* A locally closed non-value whose immediate reducts are reducible is
   reducible.  This is the neutral-term (CR3) part of the relation. *)
Lemma red_neutral : forall T t,
  locally_closed t -> (forall t', t --> t' -> red T t') ->
  ~ value t -> red T t.
Proof.
  induction T as [|A IHA B IHB]; intros t Hlc Hred Hnv.
  - split.
    + apply SN_intro. intros t' Hs. exact (sn_of_red _ _ (Hred t' Hs)).
    + split; [exact Hlc|exact I].
  - split.
    + apply SN_intro. intros t' Hs. exact (sn_of_red _ _ (Hred t' Hs)).
    + split.
      * exact Hlc.
      * intros v Hv.
        apply IHB.
        -- apply lc_app; [exact Hlc|exact (lc_of_red A v Hv)].
        -- intros q Hq.
           inversion Hq; subst.
           ++ exfalso. apply Hnv. constructor; assumption.
           ++ destruct (Hred _ H1) as [Hs' [Hl' Hp']].
              exact (Hp' v Hv).
           ++ exfalso. apply Hnv. assumption.
        -- intro Hvapp; inversion Hvapp.
Qed.

Lemma sn_ind : forall (P : tm -> Prop),
  (forall t, (forall t', t --> t' -> strongly_normalizing t' -> P t') -> P t) ->
  forall t, strongly_normalizing t -> P t.
Proof.
  intros P HP t Hsn.
  induction Hsn. apply HP. intros t' Hs Hsn'. eauto.
Qed.

Lemma red_beta_exp : forall A B body,
  locally_closed (tm_abs A body) ->
  (forall v, red A v -> red B (open body v)) ->
  forall v, red A v -> red B (tm_app (tm_abs A body) v).
Proof.
  intros A B body Hlc Hbody v.
  intro Hv.
  pose proof (sn_of_red A v Hv) as Hsn.
  revert Hv.
  induction Hsn as [v Hsteps IH].
  intro Hv.
  apply red_neutral.
  - apply lc_app; [exact Hlc|exact (lc_of_red A v Hv)].
  - intros q Hq; inversion Hq; subst.
    + apply Hbody; exact Hv.
    + exfalso. apply (abs_no_step A body Hlc t1'); exact H1.
    + apply IH with (t' := t2').
      * exact H3.
      * apply red_down with (t := v); assumption.
  - intro Hvapp; inversion Hvapp.
Qed.

Lemma red_abs : forall A B body,
  locally_closed (tm_abs A body) ->
  (forall v, red A v -> red B (open body v)) ->
  red (Ty_Arrow A B) (tm_abs A body).
Proof.
  intros A B body Hlc Hbody.
  split.
  - apply SN_intro. intros t' Hs. exfalso.
    apply (abs_no_step A body Hlc t'); exact Hs.
  - split.
    + exact Hlc.
    + intros v Hv.
      apply red_beta_exp with (A := A) (body := body); assumption.
Qed.

Lemma red_choice : forall T t1 t2,
  red T t1 -> red T t2 -> red T (tm_choice t1 t2).
Proof.
  intros T t1 t2 H1 H2.
  apply red_neutral.
  - apply lc_choice; [exact (lc_of_red T t1 H1)|exact (lc_of_red T t2 H2)].
  - intros t' Hs; inversion Hs; subst; assumption.
  - intro Hv; inversion Hv.
Qed.

Lemma red_if : forall T c t1 t2,
  red Ty_Bool c -> red T t1 -> red T t2 ->
  red T (tm_if c t1 t2).
Proof.
  intros T c t1 t2 Hc H1 H2.
  pose proof (sn_of_red Ty_Bool c Hc) as Hsn.
  revert Hc.
  induction Hsn as [c Hsteps IH].
  intros Hc.
  pose proof (lc_of_red Ty_Bool c Hc) as Hlc.
  apply red_neutral.
  - apply lc_if; [exact Hlc|exact (lc_of_red T t1 H1)|exact (lc_of_red T t2 H2)].
  - intros t' Hs; inversion Hs; subst.
    + exact H1.
    + exact H2.
    + apply IH.
      * assumption.
      * apply red_down with (t := c); assumption.
  - intro Hv; inversion Hv.
Qed.

Fixpoint tsubst (rho : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => rho x
  | tm_app t1 t2 => tm_app (tsubst rho t1) (tsubst rho t2)
  | tm_abs T t1 => tm_abs T (tsubst rho t1)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (tsubst rho t1) (tsubst rho t2) (tsubst rho t3)
  | tm_choice t1 t2 => tm_choice (tsubst rho t1) (tsubst rho t2)
  end.

Fixpoint fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_app t1 t2 => fv t1 ++ fv t2
  | tm_abs _ t1 => fv t1
  | tm_true => []
  | tm_false => []
  | tm_if t1 t2 t3 => fv t1 ++ fv t2 ++ fv t3
  | tm_choice t1 t2 => fv t1 ++ fv t2
  end.

Definition rho_update (rho : atom -> tm) (x : atom) (v : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then v else rho y.

Lemma open_rec_lc : forall k u t, lc_at k t -> open_rec k u t = t.
Proof.
  intros k u t. revert k u.
  induction t; intros k u Hlc; simpl in *; inversion Hlc; subst.
  - destruct (Nat.eqb k n) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - reflexivity.
  - f_equal; [apply IHt1; assumption|apply IHt2; assumption].
  - f_equal. apply IHt; assumption.
  - reflexivity.
  - reflexivity.
  - f_equal; [apply IHt1; assumption|apply IHt2; assumption|
      apply IHt3; assumption].
  - f_equal; [apply IHt1; assumption|apply IHt2; assumption].
Qed.

Lemma tsubst_open_rec : forall rho k u t,
  (forall x, locally_closed (rho x)) ->
  tsubst rho (open_rec k u t) = open_rec k (tsubst rho u) (tsubst rho t).
Proof.
  intros rho k u t Hrho. revert k.
  induction t; intros k; simpl;
    try reflexivity;
    try (destruct (Nat.eqb k n); reflexivity);
    try (rewrite (open_rec_lc k (tsubst rho u) (rho a));
      [reflexivity|apply lc_mono with (k := 0); [lia|apply Hrho]]);
    repeat f_equal; eauto.
Qed.

Lemma tsubst_open_fresh : forall rho x v t,
  (forall y, locally_closed (rho y)) ->
  locally_closed v ->
  ~ In x (fv t) ->
  tsubst (rho_update rho x v) (open t (tm_fvar x)) =
  open (tsubst rho t) v.
Proof.
  intros rho x v t Hrho Hlv Hfresh.
  assert (Hru : forall y, locally_closed (rho_update rho x v y)).
  { intro y. unfold rho_update. destruct (Nat.eqb x y) eqn:E;
      [exact Hlv|exact (Hrho y)]. }
  unfold open.
  rewrite (tsubst_open_rec (rho_update rho x v) 0 (tm_fvar x) t Hru).
  assert (Heq : tsubst (rho_update rho x v) t = tsubst rho t).
  { induction t; simpl in *.
    - reflexivity.
    - destruct (Nat.eqb x a) eqn:E.
      + exfalso; apply Hfresh; simpl; apply Nat.eqb_eq in E; subst; auto.
      + unfold rho_update; rewrite E; reflexivity.
    - assert (Hf1 : ~ In x (fv t1)).
      { intro H. apply Hfresh. apply in_or_app; left; exact H. }
      assert (Hf2 : ~ In x (fv t2)).
      { intro H. apply Hfresh. apply in_or_app; right; exact H. }
      rewrite (IHt1 Hf1), (IHt2 Hf2); reflexivity.
    - rewrite (IHt Hfresh); reflexivity.
    - reflexivity.
    - reflexivity.
    - assert (Hf1 : ~ In x (fv t1)).
      { intro H. apply Hfresh. apply in_or_app; left; exact H. }
      assert (Hf2 : ~ In x (fv t2)).
      { intro H. apply Hfresh. apply in_or_app; right; apply in_or_app; left; exact H. }
      assert (Hf3 : ~ In x (fv t3)).
      { intro H. apply Hfresh. apply in_or_app; right; apply in_or_app; right; exact H. }
      rewrite (IHt1 Hf1), (IHt2 Hf2), (IHt3 Hf3); reflexivity.
    - assert (Hf1 : ~ In x (fv t1)).
      { intro H. apply Hfresh. apply in_or_app; left; exact H. }
      assert (Hf2 : ~ In x (fv t2)).
      { intro H. apply Hfresh. apply in_or_app; right; exact H. }
      rewrite (IHt1 Hf1), (IHt2 Hf2); reflexivity.
  }
  rewrite Heq.
  change (open_rec 0 (if Nat.eqb x x then v else rho x) (tsubst rho t) =
    open_rec 0 v (tsubst rho t)).
  rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma tsubst_lc_at : forall k t rho,
  lc_at k t -> (forall x, lc_at k (rho x)) ->
  lc_at k (tsubst rho t).
Proof.
  intros k t rho Hlc Hrho.
  revert k Hlc Hrho.
  induction t; intros k Hlc Hrho; simpl in *; inversion Hlc; subst.
  - constructor; assumption.
  - apply Hrho.
  - constructor; [apply IHt1; assumption|apply IHt2; assumption].
  - constructor. apply IHt.
    + assumption.
    + intros x. apply lc_mono with (k := k); [lia|apply Hrho].
  - constructor.
  - constructor.
  - constructor; [apply IHt1; assumption|apply IHt2; assumption|
      apply IHt3; assumption].
  - constructor; [apply IHt1; assumption|apply IHt2; assumption].
Qed.

Fixpoint list_max (l : list atom) : atom :=
  match l with
  | [] => 0
  | a :: l' => Nat.max a (list_max l')
  end.

Lemma in_list_max : forall x l, In x l -> x <= list_max l.
Proof.
  intros x l. induction l as [|a l IH]; simpl; intros H.
  - contradiction.
  - destruct H as [->|H].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; exact H|apply Nat.le_max_r].
Qed.

Lemma fresh_exists : forall l : list atom, exists x, ~ In x l.
Proof.
  intro l. exists (S (list_max l)). intro H.
  pose proof (in_list_max _ _ H). lia.
Qed.

Lemma lc_open_inv : forall k t u,
  lc_at k (open_rec k u t) -> lc_at (S k) t.
Proof.
  intros k t u. revert k u.
  induction t; intros k u H; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + constructor. apply Nat.eqb_eq in E. lia.
    + inversion H. constructor. apply Nat.eqb_neq in E. lia.
  - inversion H. constructor.
  - inversion H; subst. apply lc_app; [apply (IHt1 k u); assumption|apply (IHt2 k u); assumption].
  - inversion H; subst. apply lc_abs. apply (IHt (S k) u); assumption.
  - constructor.
  - constructor.
  - inversion H; subst. apply lc_if;
      [apply (IHt1 k u)|apply (IHt2 k u)|apply (IHt3 k u)]; assumption.
  - inversion H; subst. apply lc_choice; [apply (IHt1 k u)|apply (IHt2 k u)]; assumption.
Qed.

Lemma typing_lc : forall Gamma t T, <{ Gamma |-- t \in T }> -> locally_closed t.
Proof.
  intros Gamma t T H.
  induction H.
  - constructor.
  - destruct (fresh_exists L) as [x Hx].
    apply lc_abs.
    apply lc_open_inv with (k := 0) (u := tm_fvar x).
    match goal with
    | H0 : forall y, ~ In y L -> locally_closed (open t1 (tm_fvar y)) |- _ =>
        exact (H0 x Hx)
    end.
  - constructor; assumption.
  - constructor.
  - constructor.
  - constructor; assumption.
  - constructor; assumption.
Qed.

Lemma tsubst_id : forall t, tsubst (fun x => tm_fvar x) t = t.
Proof. induction t; simpl; f_equal; eauto. Qed.

Lemma fundamental : forall Gamma t T,
  <{ Gamma |-- t \in T }> ->
  forall rho,
    (forall x, locally_closed (rho x)) ->
    (forall x A, Gamma x = Some A -> red A (rho x)) ->
    red T (tsubst rho t).
Proof.
  intros Gamma t T H.
  induction H; intros rho Hrho Henv; simpl.
  - apply Henv; exact H.
  - destruct (fresh_exists (L ++ fv t1)) as [x Hx].
    assert (HxL : ~ In x L).
    { intro Hin. apply Hx. apply in_or_app; left; exact Hin. }
    assert (HxF : ~ In x (fv t1)).
    { intro Hin. apply Hx. apply in_or_app; right; exact Hin. }
    assert (Hbodylc : lc_at 1 t1).
    { apply lc_open_inv with (k := 0) (u := tm_fvar x).
      exact (typing_lc (update Gamma x T1) (open t1 (tm_fvar x)) T2 (H x HxL)). }
    apply red_abs.
    + apply lc_abs. apply tsubst_lc_at with (k := 1) (rho := rho).
      * exact Hbodylc.
      * intros y. apply lc_mono with (k := 0); [lia|apply Hrho].
    + intros v Hv.
      assert (Hrho' : forall y, locally_closed (rho_update rho x v y)).
      { intro y. unfold rho_update. destruct (Nat.eqb x y) eqn:E;
          [exact (lc_of_red T1 v Hv)|exact (Hrho y)]. }
      assert (Henv' : forall y U,
        (update Gamma x T1) y = Some U -> red U (rho_update rho x v y)).
      { intros y U Hy. unfold update in Hy.
        destruct (Nat.eqb x y) eqn:E.
        - inversion Hy; subst. unfold rho_update. rewrite E. exact Hv.
        - unfold rho_update. rewrite E. apply Henv. exact Hy. }
      assert (Hsem : red T2
        (tsubst (rho_update rho x v) (open t1 (tm_fvar x)))).
      { eauto. }
      rewrite (tsubst_open_fresh rho x v t1 Hrho (lc_of_red T1 v Hv) HxF) in Hsem.
      exact Hsem.
  - match goal with
    | |- red T2 _ =>
        assert (Hfun : red (Ty_Arrow T1 T2) (tsubst rho t1)) by eauto;
        assert (Harg : red T1 (tsubst rho t2)) by eauto;
        simpl in Hfun;
        destruct Hfun as [Hsn [Hlc Hfunprop]];
        exact (Hfunprop _ Harg)
    end.
  - split.
    + apply SN_intro. intros t' Hs. inversion Hs.
    + split; [constructor|trivial].
  - split.
    + apply SN_intro. intros t' Hs. inversion Hs.
    + split; [constructor|trivial].
  - eapply red_if; eauto.
  - eapply red_choice; eauto.
Qed.

Lemma empty_no_binding : forall x A, empty x = Some A -> False.
Proof. intros x A H; unfold empty in H; discriminate. Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Ht.
  pose proof (fundamental empty t T Ht (fun x => tm_fvar x)
    (fun x => lc_fvar 0 x)
    (fun x A H => False_rect _ (empty_no_binding x A H))) as Hred.
  rewrite (tsubst_id t) in Hred.
  exact (sn_of_red T t Hred).
Qed.

End STLCNormalizationIfNondeterminismHardTask.
