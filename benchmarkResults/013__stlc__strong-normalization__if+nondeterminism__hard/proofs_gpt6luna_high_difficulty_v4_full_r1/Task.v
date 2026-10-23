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

(* A reducibility candidate at each type.  The arrow clause quantifies over
   reducible arguments and returns a candidate at the codomain; this is the
   part that makes the interpretation compositional in the presence of
   branching reductions. *)
Fixpoint reducible (T : ty) (t : tm) : Prop :=
  match T with
  | Ty_Bool => locally_closed t /\ strongly_normalizing t
  | Ty_Arrow A B =>
      locally_closed t /\ strongly_normalizing t /\
      forall u, reducible A u -> reducible B (tm_app t u)
  end.

Fixpoint env_subst (rho : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar n => tm_bvar n
  | tm_fvar x => rho x
  | tm_app t1 t2 => tm_app (env_subst rho t1) (env_subst rho t2)
  | tm_abs T t1 => tm_abs T (env_subst rho t1)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (env_subst rho t1) (env_subst rho t2) (env_subst rho t3)
  | tm_choice t1 t2 => tm_choice (env_subst rho t1) (env_subst rho t2)
  end.

Lemma open_rec_closed : forall t d k u,
  d <= k -> lc_at d t -> open_rec k u t = t.
Proof.
  induction t; intros d k u Hdk Hlc; inversion Hlc; subst; simpl.
  - assert (E : Nat.eqb k n = false) by (apply Nat.eqb_neq; lia).
    rewrite E; reflexivity.
  - reflexivity.
  - f_equal; eauto.
  - f_equal. eapply IHt with (d := S d) (k := S k); [lia|exact H1].
  - reflexivity.
  - reflexivity.
  - f_equal; eauto.
  - f_equal; eauto.
Qed.

Lemma env_subst_open_rec : forall rho k t u,
  (forall x, locally_closed (rho x)) ->
  env_subst rho (open_rec k u t) =
  open_rec k (env_subst rho u) (env_subst rho t).
Proof.
  intros rho k t; revert k; induction t; intros k u Hrho; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry; apply open_rec_closed with (d := 0); [lia|apply Hrho].
  - rewrite IHt1, IHt2; auto.
  - rewrite IHt; auto.
  - reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2, IHt3; auto.
  - rewrite IHt1, IHt2; auto.
Qed.

Fixpoint max_atom (xs : list atom) : nat :=
  match xs with [] => 0 | x :: xs' => Nat.max x (max_atom xs') end.

Lemma in_le_max_atom : forall x xs, In x xs -> x <= max_atom xs.
Proof.
  intros x xs; induction xs as [|a xs IH]; simpl; intros Hin; [contradiction|].
  destruct Hin as [->|Hin].
  - apply Nat.le_max_l.
  - eapply Nat.le_trans; [eapply IH; exact Hin|apply Nat.le_max_r].
Qed.

Lemma fresh_notin : forall xs, ~ In (S (max_atom xs)) xs.
Proof.
  intros xs Hin. pose proof (in_le_max_atom _ _ Hin). lia.
Qed.

Lemma lc_mono : forall k j t, k <= j -> lc_at k t -> lc_at j t.
Proof.
  intros k j t Hkj Hlc; revert j Hkj.
  induction Hlc; intros j Hkj.
  - apply lc_bvar; lia.
  - constructor.
  - econstructor; eauto.
  - apply lc_abs. apply IHHlc. lia.
  - constructor.
  - constructor.
  - econstructor; eauto.
  - econstructor; eauto.
Qed.

Lemma env_subst_lc : forall k t,
  lc_at k t -> forall rho, (forall x, locally_closed (rho x)) ->
  lc_at k (env_subst rho t).
Proof.
  intros k t; revert k.
  induction t; intros k Hlc rho Hrho; inversion Hlc; subst; simpl.
  - econstructor; eassumption.
  - eapply lc_mono with (k := 0); [lia|exact (Hrho a)].
  - econstructor; [eapply IHt1|eapply IHt2]; eauto.
  - econstructor. eapply IHt; eauto.
  - constructor.
  - constructor.
  - econstructor; [eapply IHt1|eapply IHt2|eapply IHt3]; eauto.
  - econstructor; [eapply IHt1|eapply IHt2]; eauto.
Qed.

Fixpoint fvars (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_app t1 t2 => fvars t1 ++ fvars t2
  | tm_abs _ t1 => fvars t1
  | tm_true | tm_false => []
  | tm_if t1 t2 t3 => fvars t1 ++ fvars t2 ++ fvars t3
  | tm_choice t1 t2 => fvars t1 ++ fvars t2
  end.

Lemma env_subst_ext : forall t rho sigma,
  (forall x, In x (fvars t) -> rho x = sigma x) ->
  env_subst rho t = env_subst sigma t.
Proof.
  induction t; intros rho sigma H; simpl.
  - reflexivity.
  - rewrite H; [reflexivity|simpl; auto].
  - assert (H1 : forall x, In x (fvars t1) -> rho x = sigma x).
    { intros x Hin; apply H; apply in_or_app; left; exact Hin. }
    assert (H2 : forall x, In x (fvars t2) -> rho x = sigma x).
    { intros x Hin; apply H; apply in_or_app; right; exact Hin. }
    rewrite (IHt1 rho sigma H1), (IHt2 rho sigma H2); reflexivity.
  - apply f_equal. apply IHt. exact H.
  - reflexivity.
  - reflexivity.
  - assert (H1 : forall x, In x (fvars t1) -> rho x = sigma x).
    { intros x Hin; apply H; apply in_or_app; left; exact Hin. }
    assert (H2 : forall x, In x (fvars t2) -> rho x = sigma x).
    { intros x Hin; apply H; apply in_or_app; right; apply in_or_app; left; exact Hin. }
    assert (H3 : forall x, In x (fvars t3) -> rho x = sigma x).
    { intros x Hin; apply H; apply in_or_app; right; apply in_or_app; right; exact Hin. }
    rewrite (IHt1 rho sigma H1), (IHt2 rho sigma H2), (IHt3 rho sigma H3); reflexivity.
  - assert (H1 : forall x, In x (fvars t1) -> rho x = sigma x).
    { intros x Hin; apply H; apply in_or_app; left; exact Hin. }
    assert (H2 : forall x, In x (fvars t2) -> rho x = sigma x).
    { intros x Hin; apply H; apply in_or_app; right; exact Hin. }
    rewrite (IHt1 rho sigma H1), (IHt2 rho sigma H2); reflexivity.
Qed.

Lemma lc_open_fvar_inv_rec : forall k t x,
  lc_at k (open_rec k (tm_fvar x) t) -> lc_at (S k) t.
Proof.
  intros k t; revert k; induction t; intros k x Hlc; simpl in Hlc.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst. apply lc_bvar; lia.
    + inversion Hlc; subst. apply lc_bvar. lia.
  - inversion Hlc; constructor.
  - inversion Hlc; subst; constructor; eauto.
  - inversion Hlc; subst; constructor. eapply IHt; eauto.
  - inversion Hlc; constructor.
  - inversion Hlc; constructor.
  - inversion Hlc; subst; constructor; eauto.
  - inversion Hlc; subst; constructor; eauto.
Qed.

Lemma has_type_lc : forall Gamma t T, has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T Hty; induction Hty.
  - unfold locally_closed; constructor.
  - apply lc_abs. apply lc_open_fvar_inv_rec with (x := S (max_atom L)).
    apply H0. apply fresh_notin.
  - unfold locally_closed in *; econstructor; eauto.
  - unfold locally_closed; constructor.
  - unfold locally_closed; constructor.
  - unfold locally_closed in *; econstructor; eauto.
  - unfold locally_closed in *; econstructor; eauto.
Qed.

Lemma sn_down : forall t t', t --> t' ->
  strongly_normalizing t -> strongly_normalizing t'.
Proof.
  intros t t' Hst Hsn. inversion Hsn; subst. eauto.
Qed.

Lemma lc_weaken : forall k t, lc_at k t -> lc_at (S k) t.
Proof. intros k t H; induction H; econstructor; eauto; lia. Qed.

Lemma lc_open_rec : forall k t u,
  lc_at (S k) t -> lc_at k u -> lc_at k (open_rec k u t).
Proof.
  intros k t; revert k; induction t; intros k u Ht Hu; inversion Ht; subst; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst; exact Hu.
    + apply lc_bvar. apply Nat.eqb_neq in E. lia.
  - constructor.
  - econstructor; eauto.
  - econstructor. eapply IHt. eassumption. eapply lc_weaken; eauto.
  - constructor.
  - constructor.
  - econstructor; eauto.
  - econstructor; eauto.
Qed.

Lemma lc_open : forall T t u,
  locally_closed (tm_abs T t) -> locally_closed u -> locally_closed (open t u).
Proof. intros T t u Ht Hu; inversion Ht; subst; unfold open; eapply lc_open_rec; eauto. Qed.

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v Hv; inversion Hv; subst; [assumption|unfold locally_closed; constructor|unfold locally_closed; constructor].
Qed.

Lemma lc_step : forall t t', t --> t' -> locally_closed t -> locally_closed t'.
Proof.
  intros t t' H; induction H; intros Hlc; inversion Hlc; subst.
  - eapply lc_open; eauto using value_lc.
  - apply lc_app; [apply IHstep; exact H4|exact H5].
  - apply lc_app; [exact H4|apply IHstep; exact H5].
  - assumption.
  - assumption.
  - apply lc_if; [apply IHstep; exact H6|exact H7|exact H8].
  - assumption.
  - assumption.
Qed.

Lemma reducible_lc : forall T t, reducible T t -> locally_closed t.
Proof.
  intros T t H; destruct T; simpl in H.
  - exact (proj1 H).
  - exact (proj1 H).
Qed.

Lemma red_step : forall T t t', reducible T t -> t --> t' -> reducible T t'.
Proof.
  induction T; simpl; intros t t' Hr Hst.
  - split.
    + exact (lc_step t t' Hst (proj1 Hr)).
    + exact (sn_down t t' Hst (proj2 Hr)).
  - split.
    + exact (lc_step t t' Hst (proj1 Hr)).
    + split.
      * exact (sn_down t t' Hst (proj1 (proj2 Hr))).
      * intros u Hu.
        assert (Happu : reducible T2 (tm_app t u)) by
          (apply (proj2 (proj2 Hr)); exact Hu).
        eapply IHT2 with (t := tm_app t u).
        -- exact Happu.
        -- apply ST_App1; [exact Hst|exact (reducible_lc _ _ Hu)].
Qed.

Lemma reducible_sn : forall T t, reducible T t -> strongly_normalizing t.
Proof.
  intros T t H; destruct T; simpl in H.
  - exact (proj2 H).
  - exact (proj1 (proj2 H)).
Qed.

Inductive nonvalue : tm -> Prop :=
| nv_bvar : forall n, nonvalue (tm_bvar n)
| nv_fvar : forall x, nonvalue (tm_fvar x)
| nv_app : forall t u, nonvalue (tm_app t u)
| nv_if : forall t a b, nonvalue (tm_if t a b)
| nv_choice : forall a b, nonvalue (tm_choice a b).

Lemma nonvalue_abs : forall T t, ~ nonvalue (tm_abs T t).
Proof. intros T t H; inversion H. Qed.

(* Saturation at non-values is what lets the relation account for choice:
   every branch of a choice is tested, while applications headed by a choice
   are saturated through their evaluation steps. *)
Lemma reducible_expand : forall T t,
  nonvalue t -> locally_closed t -> strongly_normalizing t ->
  (forall t', t --> t' -> reducible T t') -> reducible T t.
Proof.
  induction T as [|A IHA B IHB]; intros t Hnv Hlc Hsn Hred; simpl.
  - split; assumption.
  - split; [exact Hlc|]. split; [exact Hsn|].
    intros u Hu.
    induction (reducible_sn A u Hu) as [u Hsteps IH].
    assert (HuLC : locally_closed u) by (eapply reducible_lc; eauto).
    assert (Happs : strongly_normalizing (tm_app t u)).
    { econstructor; intros q Hq.
      inversion Hq; subst.
      - exfalso; eapply nonvalue_abs; eauto.
      - apply reducible_sn with (T := B).
        apply (proj2 (proj2 (Hred t1' H1)) u Hu).
      - apply reducible_sn with (T := B).
        apply (IH t2' H3 (red_step A u t2' Hu H3)).
    }
    eapply IHB with (t := tm_app t u).
    + constructor.
    + unfold locally_closed; constructor; assumption.
    + exact Happs.
    + intros q Hq. inversion Hq; subst.
      * exfalso; inversion Hnv.
      * exact ((proj2 (proj2 (Hred t1' H1))) u Hu).
      * apply IH; [assumption|apply red_step with (t := u); assumption].
Qed.

Lemma sn_choice : forall a b, strongly_normalizing a ->
  strongly_normalizing b -> strongly_normalizing (tm_choice a b).
Proof.
  intros a b Ha Hb. econstructor; intros q Hq; inversion Hq; subst; assumption.
Qed.

Lemma reducible_choice : forall T a b,
  reducible T a -> reducible T b -> reducible T (tm_choice a b).
Proof.
  induction T as [|A IHA B IHB]; intros a b Ha Hb; simpl in *.
  - split.
    + unfold locally_closed; constructor; [exact (proj1 Ha)|exact (proj1 Hb)].
    + apply sn_choice; [exact (proj2 Ha)|exact (proj2 Hb)].
  - split.
    + unfold locally_closed; constructor; [exact (proj1 Ha)|exact (proj1 Hb)].
    + split.
      * apply sn_choice; [exact (proj1 (proj2 Ha))|exact (proj1 (proj2 Hb))].
      * intros u Hu.
        induction (reducible_sn A u Hu) as [u Hsteps IH].
        assert (HuLC : locally_closed u) by (eapply reducible_lc; eauto).
        assert (HappSN : strongly_normalizing (tm_app (tm_choice a b) u)).
        { econstructor; intros q Hq; inversion Hq; subst.
          - inversion H1; subst.
            + apply reducible_sn with (T := B).
              exact ((proj2 (proj2 Ha)) u Hu).
            + apply reducible_sn with (T := B).
              exact ((proj2 (proj2 Hb)) u Hu).
          - apply reducible_sn with (T := B).
            apply IH; [assumption|apply red_step with (t := u); assumption].
        }
        eapply reducible_expand with (t := tm_app (tm_choice a b) u).
        { constructor. }
        { unfold locally_closed; constructor.
          - unfold locally_closed; constructor; [exact (proj1 Ha)|exact (proj1 Hb)].
          - exact HuLC. }
        { exact HappSN. }
        { intros q Hq; inversion Hq; subst.
          - inversion H1; subst.
            + exact ((proj2 (proj2 Ha)) u Hu).
            + exact ((proj2 (proj2 Hb)) u Hu).
          - apply IH; [assumption|apply red_step with (t := u); assumption]. }
Qed.

Lemma reducible_abs : forall A B body,
  locally_closed (tm_abs A body) ->
  (forall u, reducible A u -> reducible B (open body u)) ->
  reducible (Ty_Arrow A B) (tm_abs A body).
Proof.
  intros A B body Hlc Hbody; simpl.
  split; [exact Hlc|]. split.
  - econstructor; intros q Hq; inversion Hq.
  - intros u Hu.
    induction (reducible_sn A u Hu) as [u Hsteps IH].
    assert (HuLC : locally_closed u) by (eapply reducible_lc; eauto).
    assert (HappSN : strongly_normalizing (tm_app (tm_abs A body) u)).
    { econstructor; intros q Hq; inversion Hq; subst.
      - exact (reducible_sn B (open body u) (Hbody u Hu)).
      - inversion H1.
      - apply reducible_sn with (T := B).
        apply IH; [assumption|apply red_step with (t := u); assumption]. }
    eapply reducible_expand with (t := tm_app (tm_abs A body) u).
    { constructor. }
    { unfold locally_closed; constructor; [exact Hlc|exact HuLC]. }
    { exact HappSN. }
    { intros q Hq; inversion Hq; subst.
      - exact (Hbody u Hu).
      - inversion H1.
      - apply IH; [assumption|apply red_step with (t := u); assumption]. }
Qed.

Lemma sn_if : forall g a b,
  strongly_normalizing g -> strongly_normalizing a -> strongly_normalizing b ->
  strongly_normalizing (tm_if g a b).
Proof.
  intros g a b Hg; induction Hg as [g Hsteps IH]; intros Ha Hb.
  econstructor; intros q Hq; inversion Hq; subst.
  - exact Ha.
  - exact Hb.
  - apply IH; assumption.
Qed.

Lemma reducible_if : forall T g a b,
  reducible Ty_Bool g -> reducible T a -> reducible T b ->
  reducible T (tm_if g a b).
Proof.
  intros T g a b [HgLC HgSN] Ha Hb.
  induction HgSN as [g Hsteps IH].
  eapply reducible_expand with (t := tm_if g a b).
  - constructor.
  - unfold locally_closed; constructor;
      [exact HgLC|exact (reducible_lc T a Ha)|exact (reducible_lc T b Hb)].
  - apply sn_if; [econstructor; exact Hsteps|apply reducible_sn in Ha; exact Ha|apply reducible_sn in Hb; exact Hb].
  - intros q Hq; inversion Hq; subst.
    + exact Ha.
    + exact Hb.
    + apply IH with (t' := t1'); [exact H2|exact (lc_step g t1' H2 HgLC)].
Qed.

Definition env_update (rho : atom -> tm) (x : atom) (v : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then v else rho y.

Definition env_ok (Gamma : context) (rho : atom -> tm) : Prop :=
  (forall x, locally_closed (rho x)) /\
  (forall x T, Gamma x = Some T -> reducible T (rho x)).

Lemma env_ok_update : forall Gamma rho x A v,
  env_ok Gamma rho -> reducible A v ->
  env_ok (update Gamma x A) (env_update rho x v).
Proof.
  intros Gamma rho x A v [Hlc Hok] Hv; split.
  - intros y; unfold env_update; destruct (Nat.eqb x y); [exact (reducible_lc _ _ Hv)|apply Hlc].
  - intros y T Hy; unfold update, env_update in *.
    destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E; subst y. simpl in Hy; inversion Hy; subst. exact Hv.
    + apply Hok with (x := y); assumption.
Qed.

Theorem fundamental : forall Gamma t T,
  has_type Gamma t T -> forall rho, env_ok Gamma rho ->
  reducible T (env_subst rho t).
Proof.
  intros Gamma t T Hty; induction Hty; intros rho Hok; simpl.
  - apply (proj2 Hok) with (x := x); assumption.
  - pose proof (has_type_lc _ _ _ (T_Abs L Gamma T1 T2 t1 H)) as HlcTy.
    unfold locally_closed in HlcTy; inversion HlcTy; subst.
    assert (HlamLC : locally_closed (tm_abs T1 (env_subst rho t1))).
    { unfold locally_closed; apply lc_abs.
      eapply env_subst_lc; [exact H3|exact (proj1 Hok)]. }
    apply reducible_abs; [exact HlamLC|].
    intros u Hu.
    set (x := S (max_atom (L ++ fvars t1))).
    assert (Hx : ~ In x (L ++ fvars t1)).
    { unfold x; apply fresh_notin. }
    assert (HxL : ~ In x L).
    { intro Hin; apply Hx; apply in_or_app; left; exact Hin. }
    assert (HxF : ~ In x (fvars t1)).
    { intro Hin; apply Hx; apply in_or_app; right; exact Hin. }
    set (rho' := env_update rho x u).
    assert (Hok' : env_ok (update Gamma x T1) rho').
    { subst rho'; eapply env_ok_update; eauto. }
    specialize (H0 x HxL rho' Hok').
    assert (Hext : env_subst rho' t1 = env_subst rho t1).
    { apply env_subst_ext; intros y Hy; subst rho'; unfold env_update.
      destruct (Nat.eqb x y) eqn:E; [|reflexivity].
      apply Nat.eqb_eq in E; subst y; exfalso; apply HxF; exact Hy. }
    assert (Hopen : env_subst rho' (open t1 (tm_fvar x)) =
      open (env_subst rho' t1) u).
    { unfold open; rewrite env_subst_open_rec; [|apply (proj1 Hok')].
      unfold rho', env_update; simpl; rewrite Nat.eqb_refl; reflexivity. }
    rewrite Hopen, Hext in H0. exact H0.
  - exact ((proj2 (proj2 (IHHty1 rho Hok))) (env_subst rho t2) (IHHty2 rho Hok)).
  - split; [unfold locally_closed; constructor|].
    econstructor; intros q Hq; inversion Hq.
  - split; [unfold locally_closed; constructor|].
    econstructor; intros q Hq; inversion Hq.
  - apply reducible_if; [apply IHHty1|apply IHHty2|apply IHHty3]; exact Hok.
  - apply reducible_choice; [apply IHHty1|apply IHHty2]; exact Hok.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  pose (idrho := fun x : atom => tm_fvar x).
  assert (Hok : env_ok empty idrho).
  { split.
    - intros x; unfold locally_closed; constructor.
    - intros x U Hx; discriminate. }
  pose proof (fundamental empty t T Hty idrho Hok) as Hr.
  assert (Hid : env_subst idrho t = t).
  { clear Hty Hr Hok. induction t; simpl; try reflexivity;
    rewrite ?IHt1, ?IHt2, ?IHt3; f_equal; auto. }
  rewrite Hid in Hr. apply reducible_sn with (T := T); exact Hr.
Qed.

End STLCNormalizationIfNondeterminismHardTask.
