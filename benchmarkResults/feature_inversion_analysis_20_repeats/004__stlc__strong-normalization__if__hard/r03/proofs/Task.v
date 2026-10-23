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

(** ** Auxiliary development for the strong normalization proof.

    We prove strong normalization for the full-beta reduction relation
    [fstep], which contains the call-by-value [step] relation.  Full-beta
    reduction is the standard relation for which the Girard/Tait
    reducibility argument goes through without value restrictions. *)

Inductive fstep : tm -> tm -> Prop :=
  | F_AppAbs : forall T t u,
      fstep (tm_app (tm_abs T t) u) (open t u)
  | F_App1 : forall t1 t1' t2,
      fstep t1 t1' ->
      fstep (tm_app t1 t2) (tm_app t1' t2)
  | F_App2 : forall t1 t2 t2',
      fstep t2 t2' ->
      fstep (tm_app t1 t2) (tm_app t1 t2')
  | F_IfTrue : forall t1 t2,
      fstep (tm_if tm_true t1 t2) t1
  | F_IfFalse : forall t1 t2,
      fstep (tm_if tm_false t1 t2) t2
  | F_If : forall t1 t1' t2 t3,
      fstep t1 t1' ->
      fstep (tm_if t1 t2 t3) (tm_if t1' t2 t3).

Inductive sn_f : tm -> Prop :=
  | sn_f_intro : forall t,
      (forall t', fstep t t' -> sn_f t') ->
      sn_f t.

Lemma step_fstep : forall t t', step t t' -> fstep t t'.
Proof.
  intros t t' H. induction H.
  - apply F_AppAbs.
  - apply F_App1; assumption.
  - apply F_App2; assumption.
  - apply F_IfTrue.
  - apply F_IfFalse.
  - apply F_If; assumption.
Qed.

Lemma sn_f_sn : forall t, sn_f t -> strongly_normalizing t.
Proof.
  intros t H. induction H as [s Hs IH].
  apply SN_intro. intros s' Hstep.
  apply IH. apply step_fstep. exact Hstep.
Qed.

(** ** Free variables and substitution. *)

Fixpoint fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ => nil
  | tm_fvar x => x :: nil
  | tm_app t1 t2 => fv t1 ++ fv t2
  | tm_abs _ t1 => fv t1
  | tm_true => nil
  | tm_false => nil
  | tm_if t1 t2 t3 => fv t1 ++ fv t2 ++ fv t3
  end.

Fixpoint subst (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_app t1 t2 => tm_app (subst sigma t1) (subst sigma t2)
  | tm_abs T t1 => tm_abs T (subst sigma t1)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 =>
      tm_if (subst sigma t1) (subst sigma t2) (subst sigma t3)
  end.

Definition extend (sigma : atom -> tm) (x : atom) (u : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then u else sigma y.

Lemma subst_extend_same : forall sigma x u,
  subst (extend sigma x u) (tm_fvar x) = u.
Proof.
  intros. simpl. unfold extend. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma notin_app_l : forall (x : atom) (L1 L2 : list atom),
  ~ In x (L1 ++ L2) -> ~ In x L1.
Proof.
  intros x L1 L2 H Hin. apply H. apply in_or_app. auto.
Qed.

Lemma notin_app_r : forall (x : atom) (L1 L2 : list atom),
  ~ In x (L1 ++ L2) -> ~ In x L2.
Proof.
  intros x L1 L2 H Hin. apply H. apply in_or_app. auto.
Qed.

Lemma subst_extend_neq : forall t sigma x u,
  ~ In x (fv t) -> subst (extend sigma x u) t = subst sigma t.
Proof.
  induction t as [n | a | t1 IH1 t2 IH2 | T t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
    intros sigma x u H; simpl; auto.
  - (* tm_fvar *) unfold extend.
    destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E. subst a.
      exfalso. apply H. simpl. auto.
    + reflexivity.
  - (* tm_app *) simpl in H.
    assert (H1 : ~ In x (fv t1)) by (apply notin_app_l with (L2 := fv t2); exact H).
    assert (H2 : ~ In x (fv t2)) by (apply notin_app_r with (L1 := fv t1); exact H).
    rewrite (IH1 sigma x u H1), (IH2 sigma x u H2). reflexivity.
  - (* tm_abs *) simpl in H.
    rewrite (IH1 sigma x u H). reflexivity.
  - (* tm_if *) simpl in H.
    assert (H1 : ~ In x (fv t1)) by (apply notin_app_l with (L2 := fv t2 ++ fv t3); exact H).
    assert (H2 : ~ In x (fv t2)) by (apply notin_app_l with (L2 := fv t3);
      apply notin_app_r with (L1 := fv t1); exact H).
    assert (H3 : ~ In x (fv t3)) by (apply notin_app_r with (L1 := fv t2);
      apply notin_app_r with (L1 := fv t1); exact H).
    rewrite (IH1 sigma x u H1), (IH2 sigma x u H2), (IH3 sigma x u H3). reflexivity.
Qed.

(** A supply of fresh atoms. *)

Fixpoint sum_list (L : list atom) : nat :=
  match L with
  | nil => 0
  | x :: xs => x + sum_list xs
  end.

Definition fresh (L : list atom) : atom := S (sum_list L).

Lemma fresh_gt : forall L x, In x L -> x < fresh L.
Proof.
  induction L as [| y ys IH]; intros x Hin.
  - inversion Hin.
  - simpl in Hin. unfold fresh in IH. unfold fresh. simpl.
    destruct Hin as [-> | Hin].
    + rewrite Nat.lt_succ_r. apply Nat.le_add_r.
    + pose proof (IH x Hin) as Hlt.
      assert (Hsum : sum_list ys <= y + sum_list ys) by apply Nat.le_add_l.
      lia.
Qed.

Lemma fresh_notin : forall L x, fresh L <= x -> ~ In x L.
Proof.
  intros L x Hle Hin. pose proof (fresh_gt L x Hin). lia.
Qed.

(** ** Inversion lemmas for full-beta reduction. *)

Lemma fstep_app_inv : forall t1 t2 s',
  fstep (tm_app t1 t2) s' ->
  (exists T body, t1 = tm_abs T body /\ s' = open body t2) \/
  (exists t1', fstep t1 t1' /\ s' = tm_app t1' t2) \/
  (exists t2', fstep t2 t2' /\ s' = tm_app t1 t2').
Proof.
  intros t1 t2 s' H.
  remember (tm_app t1 t2) as a eqn:E.
  revert t1 t2 E.
  induction H as [T t u | a1 a1' a2 Hst | a1 a2 a2' Hst | b1 b2 | b1 b2 | a1 a1' a2 a3 Hst];
    intros t1 t2 E; try discriminate E.
  - injection E as E1 E2. subst t1. subst t2.
    left. exists T, t. split; reflexivity.
  - injection E as E1 E2. subst t1. subst t2.
    right. left. exists a1'. split; [assumption | reflexivity].
  - injection E as E1 E2. subst t1. subst t2.
    right. right. exists a2'. split; [assumption | reflexivity].
Qed.

Lemma fstep_if_inv : forall t1 t2 t3 s',
  fstep (tm_if t1 t2 t3) s' ->
  (t1 = tm_true /\ s' = t2) \/ (t1 = tm_false /\ s' = t3) \/
  (exists t1', fstep t1 t1' /\ s' = tm_if t1' t2 t3).
Proof.
  intros t1 t2 t3 s' H.
  remember (tm_if t1 t2 t3) as a eqn:E.
  revert t1 t2 t3 E.
  induction H as [T t u | a1 a1' a2 Hst | a1 a2 a2' Hst | b1 b2 | b1 b2 | a1 a1' a2 a3 Hst];
    intros t1 t2 t3 E; try discriminate E.
  - injection E as E1 E2 E3. subst t1. subst t2. subst t3.
    left. split; reflexivity.
  - injection E as E1 E2 E3. subst t1. subst t2. subst t3.
    right. left. split; reflexivity.
  - injection E as E1 E2 E3. subst t1. subst t2. subst t3.
    right. right. exists a1'. split; [assumption | reflexivity].
Qed.

Lemma fstep_abs_inv : forall T t s', ~ fstep (tm_abs T t) s'.
Proof.
  intros T t s' H.
  remember (tm_abs T t) as a eqn:E.
  revert T t E.
  induction H as [T0 t0 u | a1 a1' a2 Hst | a1 a2 a2' Hst | b1 b2 | b1 b2 | a1 a1' a2 a3 Hst];
    intros T1 t1 E; discriminate E.
Qed.

Lemma fstep_bvar_inv : forall k s', ~ fstep (tm_bvar k) s'.
Proof.
  intros k s' H.
  remember (tm_bvar k) as a eqn:E.
  revert k E.
  induction H as [T0 t0 u | a1 a1' a2 Hst | a1 a2 a2' Hst | b1 b2 | b1 b2 | a1 a1' a2 a3 Hst];
    intros k E; discriminate E.
Qed.

Lemma fstep_true_inv : forall s', ~ fstep tm_true s'.
Proof.
  intros s' H.
  remember tm_true as a eqn:E.
  induction H as [T0 t0 u | a1 a1' a2 Hst | a1 a2 a2' Hst | b1 b2 | b1 b2 | a1 a1' a2 a3 Hst];
    try discriminate E.
Qed.

Lemma fstep_false_inv : forall s', ~ fstep tm_false s'.
Proof.
  intros s' H.
  remember tm_false as a eqn:E.
  induction H as [T0 t0 u | a1 a1' a2 Hst | a1 a2 a2' Hst | b1 b2 | b1 b2 | a1 a1' a2 a3 Hst];
    try discriminate E.
Qed.

Lemma fstep_fvar_inv : forall x s', ~ fstep (tm_fvar x) s'.
Proof.
  intros x s' H.
  remember (tm_fvar x) as a eqn:E.
  revert x E.
  induction H as [T0 t0 u | a1 a1' a2 Hst | a1 a2 a2' Hst | b1 b2 | b1 b2 | a1 a1' a2 a3 Hst];
    intros x E; discriminate E.
Qed.

(** ** Locally-nameless level lemmas. *)

Lemma lc_at_mono : forall k1 t, lc_at k1 t -> forall k2, k1 <= k2 -> lc_at k2 t.
Proof.
  intros k1 t H. induction H as [k i Hi | k x | k a b H1 IH1 H2 IH2 |
                                  k T b H1 IH1 | k | k | k a b c H1 IH1 H2 IH2 H3 IH3];
    intros k2 Hle.
  - apply lc_bvar. lia.
  - apply lc_fvar.
  - apply lc_app; [apply IH1 | apply IH2]; exact Hle.
  - apply lc_abs. apply IH1. lia.
  - apply lc_true.
  - apply lc_false.
  - apply lc_if; [apply IH1 | apply IH2 | apply IH3]; exact Hle.
Qed.

Lemma lc_at_weaken : forall k t, lc_at k t -> lc_at (S k) t.
Proof. intros. apply lc_at_mono with (k1 := k); [exact H | lia]. Qed.

Lemma lc_at_bvar_inv : forall k i, lc_at k (tm_bvar i) -> i < k.
Proof. intros k i H. inversion H. assumption. Qed.

Lemma lc_at_app_inv : forall k t1 t2,
  lc_at k (tm_app t1 t2) -> lc_at k t1 /\ lc_at k t2.
Proof. intros k t1 t2 H. inversion H. auto. Qed.

Lemma lc_at_abs_inv : forall k T t, lc_at k (tm_abs T t) -> lc_at (S k) t.
Proof. intros k T t H. inversion H. assumption. Qed.

Lemma lc_at_if_inv : forall k t1 t2 t3,
  lc_at k (tm_if t1 t2 t3) -> lc_at k t1 /\ lc_at k t2 /\ lc_at k t3.
Proof. intros k t1 t2 t3 H. inversion H. auto. Qed.

Lemma open_rec_lc_gen : forall t k, lc_at k t ->
  forall j y, k <= j -> open_rec j y t = t.
Proof.
  induction t as [n | a | t1 IH1 t2 IH2 | T t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
    intros k Hlc j y Hkj; simpl; auto.
  - pose proof (lc_at_bvar_inv k n Hlc).
    destruct (Nat.eqb j n) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + reflexivity.
  - apply lc_at_app_inv in Hlc. destruct Hlc as [H1 H2].
    rewrite (IH1 k H1 j y Hkj). rewrite (IH2 k H2 j y Hkj). reflexivity.
  - apply lc_at_abs_inv in Hlc.
    rewrite (IH1 (S k) Hlc (S j) y); [reflexivity | lia].
  - apply lc_at_if_inv in Hlc. destruct Hlc as [H1 [H2 H3]].
    rewrite (IH1 k H1 j y Hkj). rewrite (IH2 k H2 j y Hkj).
    rewrite (IH3 k H3 j y Hkj). reflexivity.
Qed.

Lemma lc_open_inv : forall t k u, lc_at k (open_rec k u t) -> lc_at (S k) t.
Proof.
  induction t as [n | a | t1 IH1 t2 IH2 | T t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
    intros k u H; simpl in H; auto using lc_fvar, lc_true, lc_false.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. apply lc_bvar. lia.
    + apply lc_bvar. apply lc_at_bvar_inv in H. lia.
  - apply lc_at_app_inv in H. destruct H as [H1 H2].
    apply lc_app.
    + apply IH1 with (u := u). exact H1.
    + apply IH2 with (u := u). exact H2.
  - apply lc_at_abs_inv in H.
    apply lc_abs. apply IH1 with (k := S k) (u := u). exact H.
  - apply lc_at_if_inv in H. destruct H as [H1 [H2 H3]].
    apply lc_if.
    + apply IH1 with (u := u). exact H1.
    + apply IH2 with (u := u). exact H2.
    + apply IH3 with (u := u). exact H3.
Qed.

Lemma lc_open_rec : forall t k u,
  lc_at (S k) t -> lc_at k u -> lc_at k (open_rec k u t).
Proof.
  induction t as [n | a | t1 IH1 t2 IH2 | T t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
    intros k u Ht Hu; simpl; auto using lc_fvar, lc_true, lc_false.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. exact Hu.
    + apply lc_bvar. apply lc_at_bvar_inv in Ht.
      apply Nat.eqb_neq in E. lia.
  - apply lc_at_app_inv in Ht. destruct Ht as [H1 H2].
    apply lc_app.
    + apply IH1 with (u := u); assumption.
    + apply IH2 with (u := u); assumption.
  - apply lc_at_abs_inv in Ht.
    apply lc_abs. apply IH1 with (k := S k) (u := u).
    + exact Ht.
    + apply lc_at_weaken. exact Hu.
  - apply lc_at_if_inv in Ht. destruct Ht as [H1 [H2 H3]].
    apply lc_if.
    + apply IH1 with (u := u); assumption.
    + apply IH2 with (u := u); assumption.
    + apply IH3 with (u := u); assumption.
Qed.

Lemma subst_lc : forall t k sigma,
  lc_at k t -> (forall a, lc_at 0 (sigma a)) -> lc_at k (subst sigma t).
Proof.
  induction t as [n | a | t1 IH1 t2 IH2 | T t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
    intros k sigma Ht Hsig; simpl; auto using lc_fvar, lc_true, lc_false.
  - (* fvar *) apply lc_at_mono with (k1 := 0); [apply Hsig | lia].
  - (* app *) apply lc_at_app_inv in Ht. destruct Ht as [H1 H2]. apply lc_app.
    + apply IH1 with (sigma := sigma); assumption.
    + apply IH2 with (sigma := sigma); assumption.
  - (* abs *) apply lc_at_abs_inv in Ht. apply lc_abs.
    apply IH1 with (sigma := sigma); assumption.
  - (* if *) apply lc_at_if_inv in Ht. destruct Ht as [H1 [H2 H3]]. apply lc_if.
    + apply IH1 with (sigma := sigma); assumption.
    + apply IH2 with (sigma := sigma); assumption.
    + apply IH3 with (sigma := sigma); assumption.
Qed.

Lemma subst_open_rec_lc : forall t k u sigma,
  (forall a, lc_at 0 (sigma a)) ->
  subst sigma (open_rec k u t) =
  open_rec k (subst sigma u) (subst sigma t).
Proof.
  induction t as [n | a | t1 IH1 t2 IH2 | T t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
    intros k u sigma Hsig; simpl; auto.
  - (* bvar *) destruct (Nat.eqb k n); reflexivity.
  - (* fvar *) symmetry. apply open_rec_lc_gen with (k := 0); [apply Hsig | lia].
  - (* app *) rewrite (IH1 k u sigma Hsig), (IH2 k u sigma Hsig). reflexivity.
  - (* abs *) rewrite (IH1 (S k) u sigma Hsig). reflexivity.
  - (* if *) rewrite (IH1 k u sigma Hsig), (IH2 k u sigma Hsig), (IH3 k u sigma Hsig).
    reflexivity.
Qed.

Lemma fstep_lc : forall t t', lc_at 0 t -> fstep t t' -> lc_at 0 t'.
Proof.
  intros t t' Hlc Hstep. revert Hlc.
  induction Hstep as [T body u | a1 a1' a2 Hst1 IH1 | a1 a2 a2' Hst2 IH2 |
                       b1 b2 | b1 b2 | a1 a1' a2 a3 Hst1 IH1];
    intros Hlc.
  - apply lc_at_app_inv in Hlc. destruct Hlc as [Habs Hu].
    apply lc_at_abs_inv in Habs.
    exact (lc_open_rec body 0 u Habs Hu).
  - apply lc_at_app_inv in Hlc. destruct Hlc as [H1 H2].
    apply lc_app. + apply IH1. exact H1. + exact H2.
  - apply lc_at_app_inv in Hlc. destruct Hlc as [H1 H2].
    apply lc_app. + exact H1. + apply IH2. exact H2.
  - apply lc_at_if_inv in Hlc. destruct Hlc as [_ [H2 _]]. exact H2.
  - apply lc_at_if_inv in Hlc. destruct Hlc as [_ [_ H3]]. exact H3.
  - apply lc_at_if_inv in Hlc. destruct Hlc as [H1 [H2 H3]].
    apply lc_if. + apply IH1. exact H1. + exact H2. + exact H3.
Qed.

Lemma typing_lc : forall Gamma t T, <{ Gamma |-- t \in T }> -> lc_at 0 t.
Proof.
  intros Gamma t T Hty. induction Hty as
    [Gamma x T0 Hx
    | L Gamma T1 T2 t1 Hprem IHprem
    | Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
    | Gamma
    | Gamma
    | Gamma t1 t2 t3 T0 H1 IH1 H2 IH2 H3 IH3].
  - apply lc_fvar.
  - apply lc_abs.
    pose (x := fresh (L ++ fv t1)).
    assert (HxL : ~ In x L).
    { intro Hin.
      assert (Hin' : In x (L ++ fv t1)) by (apply in_or_app; left; exact Hin).
      pose proof (fresh_gt (L ++ fv t1) x Hin'). lia. }
    specialize (IHprem x HxL).
    unfold open in IHprem.
    exact (lc_open_inv t1 0 (tm_fvar x) IHprem).
  - apply lc_app; assumption.
  - apply lc_true.
  - apply lc_false.
  - apply lc_if; assumption.
Qed.

(** ** The type-indexed reducibility relation. *)

Definition neutral (t : tm) : Prop :=
  match t with
  | tm_abs _ _ => False
  | _ => True
  end.

Fixpoint CR (T : ty) : tm -> Prop :=
  match T with
  | Ty_Bool => fun t => sn_f t
  | Ty_Arrow T1 T2 => fun t => forall u, lc_at 0 u -> CR T1 u -> CR T2 (tm_app t u)
  end.

Definition CR_ok (T : ty) : Prop :=
  (forall t, CR T t -> sn_f t) /\
  (forall t t', CR T t -> fstep t t' -> CR T t') /\
  (forall t, neutral t -> (forall t', fstep t t' -> CR T t') -> CR T t) /\
  (forall x, CR T (tm_fvar x)).

Lemma sn_f_app_l_aux : forall s, sn_f s ->
  forall t u, s = tm_app t u -> sn_f t.
Proof.
  intros s H. induction H as [s Hs IH].
  intros t u Heq. subst s.
  apply sn_f_intro. intros t' Hstep.
  exact (IH (tm_app t' u) (F_App1 t t' u Hstep) t' u eq_refl).
Qed.

Lemma sn_f_app_l : forall t u, sn_f (tm_app t u) -> sn_f t.
Proof.
  intros t u H. exact (sn_f_app_l_aux (tm_app t u) H t u eq_refl).
Qed.

Lemma CR_ok_all : forall T, CR_ok T.
Proof.
  induction T as [| T1 IH1 T2 IH2].
  - unfold CR_ok. simpl. split.
    + intros t H; exact H.
    + split.
      * intros t t' H Hstep. destruct H as [s Hs]. apply Hs. exact Hstep.
      * split.
        -- intros t Hn Hred. apply sn_f_intro. exact Hred.
        -- intros x. apply sn_f_intro. intros t' Hstep.
           exfalso. exact (fstep_fvar_inv x t' Hstep).
  - destruct IH1 as [IH1_sn [IH1_step [IH1_cand IH1_fvar]]].
    destruct IH2 as [IH2_sn [IH2_step [IH2_cand IH2_fvar]]].
    unfold CR_ok. simpl. split.
    + intros t HCR. apply sn_f_app_l with (u := tm_fvar 0).
      apply IH2_sn. apply HCR. apply lc_fvar. apply IH1_fvar.
    + split.
      * intros t t' HCR Hstep u Hlcu HCRu.
        apply IH2_step with (t := tm_app t u).
        -- apply HCR. exact Hlcu. exact HCRu.
        -- apply F_App1. exact Hstep.
      * split.
        -- intros t Hn Hred u Hlcu HCRu.
           assert (Haux : forall u, sn_f u -> lc_at 0 u -> CR T1 u -> CR T2 (tm_app t u)).
           { intros u0 HSN. induction HSN as [s Hs IH].
             intros Hlc HCRs.
             apply IH2_cand.
             ++ simpl. exact I.
             ++ intros s' Hstep.
                destruct (fstep_app_inv t s s' Hstep) as
                  [[T0 [body [Heq1 Heq2]]] | [[t1' [Hst Heq]] | [s2 [Hst Heq]]]].
                ** subst t. unfold neutral in Hn. simpl in Hn. destruct Hn.
                ** subst s'. apply (Hred t1' Hst s Hlc HCRs).
                ** subst s'. apply IH.
                   --- exact Hst.
                   --- apply fstep_lc with (t := s); assumption.
                   --- apply IH1_step with (t := s); assumption.
           }
           apply Haux.
           ++ apply IH1_sn. exact HCRu.
           ++ exact Hlcu.
           ++ exact HCRu.
        -- intros x u Hlcu HCRu.
           assert (Haux : forall u, sn_f u -> lc_at 0 u -> CR T1 u -> CR T2 (tm_app (tm_fvar x) u)).
           { intros u0 HSN. induction HSN as [s Hs IH].
             intros Hlc HCRs.
             apply IH2_cand.
             ++ simpl. exact I.
             ++ intros s' Hstep.
                destruct (fstep_app_inv (tm_fvar x) s s' Hstep) as
                  [[T0 [body [Heq1 Heq2]]] | [[t1' [Hst Heq]] | [s2 [Hst Heq]]]].
                ** discriminate Heq1.
                ** subst s'. exfalso. exact (fstep_fvar_inv x t1' Hst).
                ** subst s'. apply IH.
                   --- exact Hst.
                   --- apply fstep_lc with (t := s); assumption.
                   --- apply IH1_step with (t := s); assumption.
           }
           apply Haux.
           ++ apply IH1_sn. exact HCRu.
           ++ exact Hlcu.
           ++ exact HCRu.
Qed.

Lemma CR_sn : forall T t, CR T t -> sn_f t.
Proof. intros T. destruct (CR_ok_all T) as [H _]. exact H. Qed.

Lemma CR_step : forall T t t', CR T t -> fstep t t' -> CR T t'.
Proof. intros T. destruct (CR_ok_all T) as [_ [H _]]. exact H. Qed.

Lemma CR_cand : forall T t, neutral t ->
  (forall t', fstep t t' -> CR T t') -> CR T t.
Proof. intros T. destruct (CR_ok_all T) as [_ [_ [H _]]]. exact H. Qed.

Lemma CR_fvar : forall T x, CR T (tm_fvar x).
Proof. intros T. destruct (CR_ok_all T) as [_ [_ [_ H]]]. exact H. Qed.

Lemma CR_app_abs : forall u, sn_f u -> forall T1 T2 body,
  (forall w, lc_at 0 w -> CR T1 w -> CR T2 (open body w)) ->
  lc_at 0 u -> CR T1 u -> CR T2 (tm_app (tm_abs T1 body) u).
Proof.
  intros u HSN. induction HSN as [s Hs IH].
  intros T1 T2 body Hbody Hlc HCRu.
  apply CR_cand.
  - simpl. exact I.
  - intros s' Hstep.
    destruct (fstep_app_inv (tm_abs T1 body) s s' Hstep) as
      [[T0 [body0 [Heq1 Heq2]]] | [[t1' [Hst Heq]] | [s2 [Hst Heq]]]].
    + injection Heq1 as E1 E2. subst T0. subst body0. subst s'.
      apply Hbody; assumption.
    + subst s'. exfalso. exact (fstep_abs_inv T1 body t1' Hst).
    + subst s'. apply IH.
      * exact Hst.
      * exact Hbody.
      * apply fstep_lc with (t := s); assumption.
      * apply CR_step with (t := s); assumption.
Qed.

Lemma CR_if : forall T t1 t2 t3,
  sn_f t1 -> CR T t2 -> CR T t3 -> CR T (tm_if t1 t2 t3).
Proof.
  intros T t1 t2 t3 HSN. revert T t2 t3.
  induction HSN as [s Hs IH].
  intros T t2 t3 H2 H3.
  apply CR_cand.
  - simpl. exact I.
  - intros s' Hstep.
    destruct (fstep_if_inv s t2 t3 s' Hstep) as
      [[E1 E2] | [[E1 E2] | [s0 [Hst Heq]]]].
    + subst s. subst s'. exact H2.
    + subst s. subst s'. exact H3.
    + subst s'. apply IH; assumption.
Qed.

Definition env_ok (Gamma : context) (sigma : atom -> tm) : Prop :=
  (forall a, lc_at 0 (sigma a)) /\
  (forall x T, Gamma x = Some T -> CR T (sigma x)).

Lemma subst_id : forall t, subst (fun x => tm_fvar x) t = t.
Proof.
  induction t as [n | a | t1 IH1 t2 IH2 | T t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
    simpl; auto.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH1. reflexivity.
  - rewrite IH1, IH2, IH3. reflexivity.
Qed.

Lemma fundamental : forall Gamma t T,
  <{ Gamma |-- t \in T }> ->
  forall sigma, env_ok Gamma sigma -> CR T (subst sigma t).
Proof.
  intros Gamma t T Hty. induction Hty as
    [Gamma x T0 Hx
    | L Gamma T1 T2 t1 Hprem IHprem
    | Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
    | Gamma
    | Gamma
    | Gamma t1 t2 t3 T0 H1 IH1 H2 IH2 H3 IH3].
  - (* T_Var *) intros sigma Henv. destruct Henv as [Hlc Hcr].
    simpl. apply Hcr. exact Hx.
  - (* T_Abs *) intros sigma Henv. destruct Henv as [Hlc Hcr].
    simpl. intros u Hlcu HCRu.
    pose (x := fresh (L ++ fv t1)).
    assert (HxL : ~ In x L).
    { intro Hin.
      assert (Hin' : In x (L ++ fv t1)) by (apply in_or_app; left; exact Hin).
      pose proof (fresh_gt (L ++ fv t1) x Hin'). lia. }
    assert (Hxfv : ~ In x (fv t1)).
    { intro Hin.
      assert (Hin' : In x (L ++ fv t1)) by (apply in_or_app; right; exact Hin).
      pose proof (fresh_gt (L ++ fv t1) x Hin'). lia. }
    assert (Hbody : forall w, lc_at 0 w -> CR T1 w -> CR T2 (open (subst sigma t1) w)).
    { intros w Hlcw HCRw.
      assert (Henv : env_ok (update Gamma x T1) (extend sigma x w)).
      { split.
        - intros a. unfold extend. destruct (Nat.eqb x a) eqn:E.
          + exact Hlcw.
          + apply Hlc.
        - intros y T' Hy. unfold update in Hy. destruct (Nat.eqb x y) eqn:E.
          + injection Hy as Hy'. subst T'.
            unfold extend. rewrite E. exact HCRw.
          + unfold extend. rewrite E.
            apply Hcr. exact Hy. }
      destruct Henv as [Henv_lc Henv_cr].
      specialize (IHprem x HxL (extend sigma x w) (conj Henv_lc Henv_cr)).
      unfold open in IHprem.
      rewrite (subst_open_rec_lc t1 0 (tm_fvar x) (extend sigma x w) Henv_lc) in IHprem.
      rewrite subst_extend_same in IHprem.
      rewrite (subst_extend_neq t1 sigma x w Hxfv) in IHprem.
      exact IHprem. }
    apply (CR_app_abs u (CR_sn T1 u HCRu) T1 T2 (subst sigma t1) Hbody Hlcu HCRu).
  - (* T_App *) intros sigma Henv. destruct Henv as [Hlc Hcr]. simpl.
    apply (IH1 sigma (conj Hlc Hcr)).
    + apply subst_lc with (k := 0).
      * apply typing_lc with (Gamma := Gamma) (T := T1). exact H2.
      * exact Hlc.
    + apply IH2. exact (conj Hlc Hcr).
  - (* T_True *) intros sigma Henv. simpl.
    apply sn_f_intro. intros t' Hstep. exfalso. exact (fstep_true_inv t' Hstep).
  - (* T_False *) intros sigma Henv. simpl.
    apply sn_f_intro. intros t' Hstep. exfalso. exact (fstep_false_inv t' Hstep).
  - (* T_If *) intros sigma Henv. destruct Henv as [Hlc Hcr]. simpl.
    apply CR_if.
    + exact (IH1 sigma (conj Hlc Hcr)).
    + apply IH2. exact (conj Hlc Hcr).
    + apply IH3. exact (conj Hlc Hcr).
Qed.


Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  assert (Henv : env_ok empty (fun x => tm_fvar x)).
  { split.
    - intros a. apply lc_fvar.
    - intros x T' Hx. unfold empty in Hx. discriminate Hx. }
  assert (HCR : CR T t).
  { pose proof (fundamental empty t T Hty (fun x => tm_fvar x) Henv) as H.
    rewrite subst_id in H. exact H. }
  apply sn_f_sn. apply CR_sn with (T := T). exact HCR.
Qed.

End STLCCBVNormalizationTask.
