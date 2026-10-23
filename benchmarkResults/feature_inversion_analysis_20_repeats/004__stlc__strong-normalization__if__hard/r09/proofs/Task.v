(** STLC call-by-value strong-normalization benchmark task. *)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Relations.Relation_Definitions.

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

(** * Strong normalization for STLC call-by-value *)

(* ---------- Locally closed terms ---------- *)

Lemma lc_at_bvar_inv : forall k n, lc_at k (tm_bvar n) -> n < k.
Proof. intros k n H; inversion H; subst; assumption. Qed.

Lemma lc_at_app_inv : forall k t1 t2,
  lc_at k (tm_app t1 t2) -> lc_at k t1 /\ lc_at k t2.
Proof. intros k t1 t2 H; inversion H; subst; split; assumption. Qed.

Lemma lc_at_abs_inv : forall k T t1,
  lc_at k (tm_abs T t1) -> lc_at (S k) t1.
Proof. intros k T t1 H; inversion H; subst; assumption. Qed.

Lemma lc_at_if_inv : forall k t1 t2 t3,
  lc_at k (tm_if t1 t2 t3) -> lc_at k t1 /\ lc_at k t2 /\ lc_at k t3.
Proof. intros k t1 t2 t3 H; inversion H; subst; auto. Qed.

Lemma lc_at_mono : forall k k' t, lc_at k t -> k <= k' -> lc_at k' t.
Proof.
  intros k k' t H. revert k'.
  induction H as [k0 i Hi | k0 x | k0 t1 t2 H1 IH1 H2 IH2
    | k0 T t1 H1 IH1 | k0 | k0 | k0 t1 t2 t3 H1 IH1 H2 IH2 H3 IH3];
    intros k' Hle.
  - apply lc_bvar. eapply Nat.lt_le_trans; eassumption.
  - apply lc_fvar.
  - apply lc_app; [apply IH1 | apply IH2]; exact Hle.
  - apply lc_abs. apply IH1. apply le_n_S in Hle. exact Hle.
  - apply lc_true.
  - apply lc_false.
  - apply lc_if; [apply IH1 | apply IH2 | apply IH3]; exact Hle.
Qed.

Lemma open_rec_lc : forall k u t, lc_at k t -> open_rec k u t = t.
Proof.
  intros k u t. revert k.
  induction t as [n | x | t1 IH1 t2 IH2 | T t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
    intros k Ht; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n.
      apply lc_at_bvar_inv in Ht. exfalso. exact (Nat.lt_irrefl _ Ht).
    + reflexivity.
  - reflexivity.
  - apply lc_at_app_inv in Ht. destruct Ht as [H1 H2].
    rewrite (IH1 k H1), (IH2 k H2). reflexivity.
  - apply lc_at_abs_inv in Ht.
    rewrite (IH1 (S k) Ht). reflexivity.
  - reflexivity.
  - reflexivity.
  - apply lc_at_if_inv in Ht. destruct Ht as [H1 [H2 H3]].
    rewrite (IH1 k H1), (IH2 k H2), (IH3 k H3). reflexivity.
Qed.

Lemma lc_at_open_rec_S : forall k u t,
  lc_at (S k) t -> lc_at k u -> lc_at k (open_rec k u t).
Proof.
  intros k u t. revert k.
  induction t as [n | x | t1 IH1 t2 IH2 | T t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
    intros k Ht Hu; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + exact Hu.
    + apply lc_bvar.
      apply lc_at_bvar_inv in Ht.
      pose proof (proj1 (Nat.lt_succ_r n k) Ht) as Hle.
      apply Nat.le_neq; split; [exact Hle |].
      intros Heq. apply Nat.eqb_neq in E. apply E. symmetry. exact Heq.
  - apply lc_fvar.
  - apply lc_at_app_inv in Ht. destruct Ht as [H1 H2].
    apply lc_app.
    + apply IH1; [exact H1 | exact Hu].
    + apply IH2; [exact H2 | exact Hu].
  - apply lc_at_abs_inv in Ht.
    apply lc_abs.
    apply IH1; [exact Ht |].
    apply lc_at_mono with (k := k); [exact Hu | apply Nat.le_succ_diag_r].
  - apply lc_true.
  - apply lc_false.
  - apply lc_at_if_inv in Ht. destruct Ht as [H1 [H2 H3]].
    apply lc_if.
    + apply IH1; [exact H1 | exact Hu].
    + apply IH2; [exact H2 | exact Hu].
    + apply IH3; [exact H3 | exact Hu].
Qed.

Lemma lc_at_open_inv : forall k t u,
  lc_at k (open_rec k u t) -> lc_at k u -> lc_at (S k) t.
Proof.
  intros k t u. revert k.
  induction t as [n | x | t1 IH1 t2 IH2 | T t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
    intros k Hopen Hu; simpl in Hopen.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n.
      apply lc_bvar. apply Nat.lt_succ_diag_r.
    + apply lc_bvar.
      apply lc_at_bvar_inv in Hopen.
      eapply Nat.lt_trans; [exact Hopen | apply Nat.lt_succ_diag_r].
  - apply lc_fvar.
  - apply lc_at_app_inv in Hopen. destruct Hopen as [H1 H2].
    apply lc_app.
    + apply IH1 with (k := k); assumption.
    + apply IH2 with (k := k); assumption.
  - apply lc_at_abs_inv in Hopen.
    apply lc_abs.
    apply IH1 with (k := S k).
    exact Hopen.
    apply lc_at_mono with (k := k); [exact Hu | apply Nat.le_succ_diag_r].
  - apply lc_true.
  - apply lc_false.
  - apply lc_at_if_inv in Hopen. destruct Hopen as [H1 [H2 H3]].
    apply lc_if.
    + apply IH1 with (k := k); assumption.
    + apply IH2 with (k := k); assumption.
    + apply IH3 with (k := k); assumption.
Qed.

(* ---------- Free variables and substitution on free variables ---------- *)

Fixpoint fvs (t : tm) : list atom :=
  match t with
  | tm_bvar _ => nil
  | tm_fvar x => x :: nil
  | tm_app t1 t2 => fvs t1 ++ fvs t2
  | tm_abs _ t1 => fvs t1
  | tm_true => nil
  | tm_false => nil
  | tm_if t1 t2 t3 => fvs t1 ++ fvs t2 ++ fvs t3
  end.

Lemma in_app_l : forall (x : atom) l1 l2, In x l1 -> In x (l1 ++ l2).
Proof. intros; apply in_or_app; auto. Qed.

Lemma in_app_r : forall (x : atom) l1 l2, In x l2 -> In x (l1 ++ l2).
Proof. intros; apply in_or_app; auto. Qed.

Fixpoint subst_all (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_app t1 t2 => tm_app (subst_all sigma t1) (subst_all sigma t2)
  | tm_abs T t1 => tm_abs T (subst_all sigma t1)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 =>
      tm_if (subst_all sigma t1) (subst_all sigma t2) (subst_all sigma t3)
  end.

Lemma subst_all_open_rec_fvs : forall sigma k u t,
  (forall x, In x (fvs t) -> locally_closed (sigma x)) ->
  subst_all sigma (open_rec k u t) =
  open_rec k (subst_all sigma u) (subst_all sigma t).
Proof.
  intros sigma k u t. revert k.
  induction t as [n | x | t1 IH1 t2 IH2 | T t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
    intros k Hcl; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - assert (Hfx : lc_at k (sigma x)).
    { apply lc_at_mono with (k := 0); [| apply Nat.le_0_l].
      apply Hcl. simpl. left. reflexivity. }
    rewrite open_rec_lc with (u := subst_all sigma u) (t := sigma x);
      [reflexivity | exact Hfx].
  - assert (E1 : subst_all sigma (open_rec k u t1) =
                open_rec k (subst_all sigma u) (subst_all sigma t1)).
    { apply IH1. intros y Hy. apply Hcl. simpl.
      apply in_app_l. exact Hy. }
    assert (E2 : subst_all sigma (open_rec k u t2) =
                open_rec k (subst_all sigma u) (subst_all sigma t2)).
    { apply IH2. intros y Hy. apply Hcl. simpl.
      apply in_app_r. exact Hy. }
    rewrite E1, E2. reflexivity.
  - rewrite IH1; [reflexivity |].
    intros y Hy. apply Hcl. simpl. exact Hy.
  - reflexivity.
  - reflexivity.
  - assert (E1 : subst_all sigma (open_rec k u t1) =
                open_rec k (subst_all sigma u) (subst_all sigma t1)).
    { apply IH1. intros y Hy. apply Hcl. simpl.
      apply in_app_l. exact Hy. }
    assert (E2 : subst_all sigma (open_rec k u t2) =
                open_rec k (subst_all sigma u) (subst_all sigma t2)).
    { apply IH2. intros y Hy. apply Hcl. simpl.
      apply in_app_r. apply in_app_l. exact Hy. }
    assert (E3 : subst_all sigma (open_rec k u t3) =
                open_rec k (subst_all sigma u) (subst_all sigma t3)).
    { apply IH3. intros y Hy. apply Hcl. simpl.
      apply in_app_r. apply in_app_r. exact Hy. }
    rewrite E1, E2, E3. reflexivity.
Qed.

Lemma subst_all_ext : forall t sigma tau,
  (forall x, In x (fvs t) -> sigma x = tau x) ->
  subst_all sigma t = subst_all tau t.
Proof.
  induction t as [n | x | t1 IH1 t2 IH2 | T t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
    intros sigma tau Hagree; simpl.
  - reflexivity.
  - apply Hagree. simpl. left. reflexivity.
  - assert (E1 : subst_all sigma t1 = subst_all tau t1).
    { apply IH1. intros y Hy. apply Hagree. simpl.
      apply in_app_l. exact Hy. }
    assert (E2 : subst_all sigma t2 = subst_all tau t2).
    { apply IH2. intros y Hy. apply Hagree. simpl.
      apply in_app_r. exact Hy. }
    rewrite E1, E2. reflexivity.
  - assert (E1 : subst_all sigma t1 = subst_all tau t1).
    { apply IH1. intros y Hy. apply Hagree. simpl. exact Hy. }
    rewrite E1. reflexivity.
  - reflexivity.
  - reflexivity.
  - assert (E1 : subst_all sigma t1 = subst_all tau t1).
    { apply IH1. intros y Hy. apply Hagree. simpl.
      apply in_app_l. exact Hy. }
    assert (E2 : subst_all sigma t2 = subst_all tau t2).
    { apply IH2. intros y Hy. apply Hagree. simpl.
      apply in_app_r. apply in_app_l. exact Hy. }
    assert (E3 : subst_all sigma t3 = subst_all tau t3).
    { apply IH3. intros y Hy. apply Hagree. simpl.
      apply in_app_r. apply in_app_r. exact Hy. }
    rewrite E1, E2, E3. reflexivity.
Qed.

Definition update_subst (sigma : atom -> tm) (x : atom) (v : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then v else sigma y.

Lemma update_subst_same : forall sigma x v, update_subst sigma x v x = v.
Proof. intros. unfold update_subst. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma update_subst_neq : forall sigma x v y, x <> y ->
  update_subst sigma x v y = sigma y.
Proof.
  intros sigma x v y Hne. unfold update_subst.
  apply Nat.eqb_neq in Hne. rewrite Hne. reflexivity.
Qed.

Lemma subst_all_update_out : forall sigma x v t,
  ~ In x (fvs t) ->
  subst_all (update_subst sigma x v) t = subst_all sigma t.
Proof.
  intros sigma x v t Hx. apply subst_all_ext.
  intros y Hy. apply update_subst_neq.
  intros Heq. subst y. apply Hx. exact Hy.
Qed.

Lemma subst_open_fresh : forall sigma x v t,
  ~ In x (fvs t) ->
  (forall y, In y (fvs t) -> locally_closed (sigma y)) ->
  locally_closed v ->
  subst_all (update_subst sigma x v) (open t (tm_fvar x)) =
  open (subst_all sigma t) v.
Proof.
  intros sigma x v t Hx Hcl Hv.
  change (subst_all (update_subst sigma x v) (open_rec 0 (tm_fvar x) t) =
          open_rec 0 v (subst_all sigma t)).
  rewrite subst_all_open_rec_fvs with (u := tm_fvar x).
  - change (open_rec 0 (update_subst sigma x v x)
              (subst_all (update_subst sigma x v) t) =
            open_rec 0 v (subst_all sigma t)).
    assert (Hout : subst_all (update_subst sigma x v) t = subst_all sigma t)
      by (apply subst_all_update_out; exact Hx).
    rewrite update_subst_same, Hout. reflexivity.
  - intros y Hy. unfold update_subst. destruct (Nat.eqb x y) eqn:E.
    + exact Hv.
    + apply Hcl. exact Hy.
Qed.

Lemma subst_all_id : forall t, subst_all (fun x => tm_fvar x) t = t.
Proof.
  induction t as [n | x | t1 IH1 t2 IH2 | T t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
    simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH1. reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IH1, IH2, IH3. reflexivity.
Qed.

(* ---------- Fresh atoms ---------- *)

Fixpoint max_list (l : list atom) : atom :=
  match l with
  | nil => 0
  | x :: xs => Nat.max x (max_list xs)
  end.

Definition fresh (l : list atom) : atom := S (max_list l).

Lemma max_list_spec : forall l x, In x l -> x <= max_list l.
Proof.
  induction l as [| a l IH]; intros x Hin.
  - inversion Hin.
  - simpl. destruct Hin as [Heq | Hin].
    + subst a. apply Nat.le_max_l.
    + apply Nat.le_trans with (max_list l).
      * apply IH; exact Hin.
      * apply Nat.le_max_r.
Qed.

Lemma fresh_fresh : forall l, ~ In (fresh l) l.
Proof.
  intros l Hin. unfold fresh in Hin.
  apply max_list_spec in Hin.
  assert (Hlt : max_list l < S (max_list l)) by apply Nat.lt_succ_diag_r.
  pose proof (Nat.lt_le_trans _ _ _ Hlt Hin) as Hc.
  exact (Nat.lt_irrefl _ Hc).
Qed.


(* ---------- Values do not step ---------- *)

Lemma abs_no_step : forall T t s, step (tm_abs T t) s -> False.
Proof. intros; inversion H. Qed.

Lemma true_no_step : forall s, step tm_true s -> False.
Proof. intros; inversion H. Qed.

Lemma false_no_step : forall s, step tm_false s -> False.
Proof. intros; inversion H. Qed.

Lemma value_no_step : forall v, value v -> forall s, step v s -> False.
Proof.
  intros v Hv. destruct Hv as [T t Hlc | | ]; intros s Hs; inversion Hs.
Qed.

Lemma app_not_value : forall t1 t2, value (tm_app t1 t2) -> False.
Proof. intros; inversion H. Qed.

Lemma if_not_value : forall t1 t2 t3, value (tm_if t1 t2 t3) -> False.
Proof. intros; inversion H. Qed.

(* ---------- Strong normalization facts ---------- *)

Lemma SN_step : forall t s, strongly_normalizing t -> step t s -> strongly_normalizing s.
Proof.
  intros t s H. revert s.
  induction H as [t0 Hsn IH].
  intros s Hs. apply Hsn. exact Hs.
Qed.

Lemma SN_multi : forall t s, strongly_normalizing t -> multi step t s -> strongly_normalizing s.
Proof.
  intros t s H Hm. revert H.
  induction Hm as [x | x y z Hs Hm IH]; intros H.
  - exact H.
  - apply IH. apply SN_step with (t := x); assumption.
Qed.

Lemma SN_abs : forall T t, strongly_normalizing (tm_abs T t).
Proof. intros. apply SN_intro. intros s Hs. inversion Hs. Qed.

Lemma SN_true : strongly_normalizing tm_true.
Proof. apply SN_intro. intros s Hs. inversion Hs. Qed.

Lemma SN_false : strongly_normalizing tm_false.
Proof. apply SN_intro. intros s Hs. inversion Hs. Qed.

(* ---------- Values reduce only to themselves ---------- *)

Lemma multi_cases : forall t s, multi step t s ->
  s = t \/ exists u, step t u /\ multi step u s.
Proof.
  intros t s Hm. induction Hm as [x | x y z Hs Hm IH].
  - left. reflexivity.
  - right. exists y. split; assumption.
Qed.

Lemma multi_abs_eq : forall T t s, multi step (tm_abs T t) s -> s = tm_abs T t.
Proof.
  intros T t s Hm. destruct (multi_cases (tm_abs T t) s Hm) as [Heq | [u [Hs _]]].
  - exact Heq.
  - exfalso. apply abs_no_step in Hs. exact Hs.
Qed.

Lemma multi_true_eq : forall s, multi step tm_true s -> s = tm_true.
Proof.
  intros s Hm. destruct (multi_cases tm_true s Hm) as [Heq | [u [Hs _]]].
  - exact Heq.
  - exfalso. apply true_no_step in Hs. exact Hs.
Qed.

Lemma multi_false_eq : forall s, multi step tm_false s -> s = tm_false.
Proof.
  intros s Hm. destruct (multi_cases tm_false s Hm) as [Heq | [u [Hs _]]].
  - exact Heq.
  - exfalso. apply false_no_step in Hs. exact Hs.
Qed.

(* ---------- Locally closed terms are preserved by steps ---------- *)

Lemma step_lc : forall t s, step t s -> locally_closed t -> locally_closed s.
Proof.
  intros t s H.
  induction H as [T t0 v _ Hval
    | t1 t1' t2 Hstep IH Hlc2
    | v1 t2 t2' Hval Hstep IH
    | t1 t2 Hlc1 Hlc2
    | t1 t2 Hlc1 Hlc2
    | t1 t1' t2 t3 Hstep IH Hlc2 Hlc3];
    intros Hlc.
  - apply lc_at_app_inv in Hlc. destruct Hlc as [Hla Hlv].
    apply lc_at_abs_inv in Hla.
    change (lc_at 0 (open_rec 0 v t0)).
    apply lc_at_open_rec_S; [exact Hla | exact Hlv].
  - apply lc_at_app_inv in Hlc. destruct Hlc as [Hl1 Hl2].
    apply lc_app.
    + apply IH. exact Hl1.
    + exact Hl2.
  - apply lc_at_app_inv in Hlc. destruct Hlc as [Hl1 Hl2].
    apply lc_app.
    + exact Hl1.
    + apply IH. exact Hl2.
  - apply lc_at_if_inv in Hlc. destruct Hlc as [Hl1 [Hl2 Hl3]].
    exact Hl2.
  - apply lc_at_if_inv in Hlc. destruct Hlc as [Hl1 [Hl2 Hl3]].
    exact Hl3.
  - apply lc_at_if_inv in Hlc. destruct Hlc as [Hl1 [Hl2 Hl3]].
    apply lc_if.
    + apply IH. exact Hl1.
    + exact Hl2.
    + exact Hl3.
Qed.

(* ---------- The logical relation ---------- *)

Fixpoint LR (T : ty) (t : tm) : Prop :=
  locally_closed t /\
  strongly_normalizing t /\
  (forall s, multi step t s -> value s ->
     match T with
     | Ty_Bool => s = tm_true \/ s = tm_false
     | Ty_Arrow A B => forall w, LR A w -> LR B (tm_app s w)
     end).

Definition value_cond (T : ty) (s : tm) : Prop :=
  match T with
  | Ty_Bool => s = tm_true \/ s = tm_false
  | Ty_Arrow A B => forall w, LR A w -> LR B (tm_app s w)
  end.

Lemma LR_unfold : forall T t,
  LR T t <-> locally_closed t /\ strongly_normalizing t /\
    (forall s, multi step t s -> value s -> value_cond T s).
Proof. intros T t. destruct T; simpl; reflexivity. Qed.

Lemma LR_lc : forall T t, LR T t -> locally_closed t.
Proof. intros T t H. apply LR_unfold in H. tauto. Qed.

Lemma LR_sn : forall T t, LR T t -> strongly_normalizing t.
Proof. intros T t H. apply LR_unfold in H. tauto. Qed.

Lemma LR_cond : forall T t s, LR T t -> multi step t s -> value s -> value_cond T s.
Proof.
  intros T t s H Hm Hv. apply LR_unfold in H.
  destruct H as [_ [_ Hcond]]. apply Hcond; assumption.
Qed.

Lemma LR_value : forall T t, LR T t -> value t -> value_cond T t.
Proof. intros T t H Hv. apply LR_cond with (t := t); auto using multi_refl. Qed.

Lemma LR_intro : forall T t, locally_closed t -> strongly_normalizing t ->
  (forall s, multi step t s -> value s -> value_cond T s) -> LR T t.
Proof.
  intros T t H1 H2 H3. apply LR_unfold.
  split; [exact H1 | split; [exact H2 | exact H3]].
Qed.

Lemma value_cond_arrow : forall A B s,
  value_cond (Ty_Arrow A B) s <-> (forall w, LR A w -> LR B (tm_app s w)).
Proof. intros. simpl. reflexivity. Qed.

Lemma value_cond_bool : forall s,
  value_cond Ty_Bool s <-> (s = tm_true \/ s = tm_false).
Proof. intros. simpl. reflexivity. Qed.

Lemma LR_step : forall T t s, LR T t -> step t s -> LR T s.
Proof.
  intros T t s H Hst.
  apply LR_unfold in H. apply LR_unfold.
  destruct H as [Hlc [Hsn Hcond]]. split.
  - apply step_lc with (t := t); assumption.
  - split.
    + apply SN_step with (t := t); assumption.
    + intros s' Hm Hv. apply Hcond.
      * apply multi_step with (y := s); assumption.
      * exact Hv.
Qed.

Lemma LR_multi : forall T t s, LR T t -> multi step t s -> LR T s.
Proof.
  intros T t s H Hm. revert H.
  induction Hm as [x | x y z Hs Hm IH]; intros H.
  - exact H.
  - apply IH. apply LR_step with (t := x); assumption.
Qed.


(* ---------- Inversion lemmas for the application and if steps ---------- *)

Lemma step_app_inv : forall t1 t2 s,
  step (tm_app t1 t2) s ->
  (exists A body v, t1 = tm_abs A body /\ t2 = v /\ value v /\ s = open body v) \/
  (exists t1', step t1 t1' /\ s = tm_app t1' t2) \/
  (exists t2', value t1 /\ step t2 t2' /\ s = tm_app t1 t2').
Proof.
  intros t1 t2 s H. inversion H; subst; eauto 10.
Qed.

Lemma step_app_abs_inv : forall A body t2 s,
  step (tm_app (tm_abs A body) t2) s ->
  (value t2 /\ s = open body t2) \/
  (value (tm_abs A body) /\
   exists t2', step t2 t2' /\ s = tm_app (tm_abs A body) t2').
Proof.
  intros A body t2 s H. inversion H; subst.
  - left. split; [assumption | reflexivity].
  - exfalso. eapply abs_no_step. eassumption.
  - right. split; [assumption | eauto].
Qed.

Lemma step_if_inv : forall t1 t2 t3 s,
  step (tm_if t1 t2 t3) s ->
  (t1 = tm_true /\ s = t2) \/
  (t1 = tm_false /\ s = t3) \/
  (exists t1', step t1 t1' /\ s = tm_if t1' t2 t3).
Proof.
  intros t1 t2 t3 s H. inversion H; subst; eauto 10.
Qed.

Lemma LR_value_arrow : forall A B t,
  LR (Ty_Arrow A B) t -> value t -> forall w, LR A w -> LR B (tm_app t w).
Proof.
  intros A B t H Hv.
  apply (proj1 (value_cond_arrow A B t)). apply LR_value; assumption.
Qed.

(* ---------- Application closure of the logical relation ---------- *)

Lemma LR_app_abs : forall A B body,
  locally_closed (tm_abs A body) ->
  (forall w, LR A w -> LR B (open body w)) ->
  forall t2, LR A t2 -> LR B (tm_app (tm_abs A body) t2).
Proof.
  intros A B body Hlcabs Hbody t2 HLRA.
  assert (Hsn : strongly_normalizing t2) by (apply LR_sn with (T := A); exact HLRA).
  revert HLRA.
  induction Hsn as [t2 HsnAll IH].
  intros HLRA.
  apply LR_intro.
  - (* locally closed *)
    apply lc_app; [exact Hlcabs | apply LR_lc with (T := A); exact HLRA].
  - (* strongly normalizing *)
    apply SN_intro. intros s Hs.
    destruct (step_app_abs_inv A body t2 s Hs) as [[Hval Heq] | [Hval [t2' [Hstep Heq]]]].
    + subst s. apply LR_sn with (T := B). apply Hbody. exact HLRA.
    + subst s. apply LR_sn with (T := B). apply IH; [exact Hstep |].
      apply LR_step with (T := A) (t := t2); assumption.
  - (* value condition *)
    intros s Hm Hv.
    destruct (multi_cases (tm_app (tm_abs A body) t2) s Hm) as [Heq | [u [Hs Hm']]].
    + subst s. exfalso. apply app_not_value in Hv. exact Hv.
    + destruct (step_app_abs_inv A body t2 u Hs) as [[Hval Heq] | [Hval [t2' [Hstep Heq]]]].
      * subst u. apply LR_value with (t := s).
        -- apply LR_multi with (t := open body t2).
           ++ apply Hbody. exact HLRA.
           ++ exact Hm'.
        -- exact Hv.
      * subst u. apply LR_value with (t := s).
        -- apply LR_multi with (t := tm_app (tm_abs A body) t2').
           ++ apply IH; [exact Hstep | apply LR_step with (T := A) (t := t2); assumption].
           ++ exact Hm'.
        -- exact Hv.
Qed.

Lemma LR_app : forall A B t1 t2,
  LR (Ty_Arrow A B) t1 -> LR A t2 -> LR B (tm_app t1 t2).
Proof.
  intros A B t1 t2 H1 H2.
  assert (Hsn : strongly_normalizing t1) by (apply LR_sn with (T := Ty_Arrow A B); exact H1).
  revert H1 H2.
  induction Hsn as [t1 HsnAll IH].
  intros H1 H2.
  apply LR_intro.
  - (* locally closed *)
    apply lc_app; [apply LR_lc with (T := Ty_Arrow A B); exact H1 | apply LR_lc with (T := A); exact H2].
  - (* strongly normalizing *)
    apply SN_intro. intros s Hs.
    destruct (step_app_inv t1 t2 s Hs) as
      [[A0 [body [v [Eq1 [Eq2 [Hval Eqs]]]]]] |
       [[t1' [Hstep Eqs]] |
        [t2' [Hval [Hstep Eqs]]]]].
    + subst t1. subst t2. subst s.
      assert (HLB : LR B (tm_app (tm_abs A0 body) v)).
      { apply LR_value_arrow with (A := A) (t := tm_abs A0 body).
        - exact H1.
        - apply v_abs. apply LR_lc with (T := Ty_Arrow A B). exact H1.
        - exact H2. }
      apply SN_step with (t := tm_app (tm_abs A0 body) v).
      * apply LR_sn with (T := B). exact HLB.
      * exact Hs.
    + subst s.
      assert (HLB : LR B (tm_app t1' t2)).
      { apply IH; [exact Hstep | apply LR_step with (T := Ty_Arrow A B) (t := t1); [exact H1 | exact Hstep] | exact H2]. }
      apply LR_sn with (T := B). exact HLB.
    + subst s.
      assert (HLB : LR B (tm_app t1 t2')).
      { apply LR_value_arrow with (A := A) (t := t1).
        - exact H1.
        - exact Hval.
        - apply LR_step with (T := A) (t := t2); [exact H2 | exact Hstep]. }
      apply LR_sn with (T := B). exact HLB.
  - (* value condition *)
    intros s Hm Hv.
    destruct (multi_cases (tm_app t1 t2) s Hm) as [Heq | [u [Hs Hm']]].
    + subst s. exfalso. apply app_not_value in Hv. exact Hv.
    + destruct (step_app_inv t1 t2 u Hs) as
        [[A0 [body [v [Eq1 [Eq2 [Hval Eqs]]]]]] |
         [[t1' [Hstep Eqs]] |
          [t2' [Hval [Hstep Eqs]]]]].
      * subst t1. subst t2. subst u.
        assert (HLB : LR B (tm_app (tm_abs A0 body) v)).
        { apply LR_value_arrow with (A := A) (t := tm_abs A0 body).
          - exact H1.
          - apply v_abs. apply LR_lc with (T := Ty_Arrow A B). exact H1.
        - exact H2. }
        apply LR_value with (t := s).
        -- apply LR_multi with (t := open body v).
           ++ apply LR_step with (T := B) (t := tm_app (tm_abs A0 body) v);
                [exact HLB | exact Hs].
           ++ exact Hm'.
        -- exact Hv.
      * subst u.
        assert (HLB : LR B (tm_app t1' t2)).
        { apply IH; [exact Hstep | apply LR_step with (T := Ty_Arrow A B) (t := t1); [exact H1 | exact Hstep] | exact H2]. }
        apply LR_value with (t := s).
        -- apply LR_multi with (t := tm_app t1' t2); [exact HLB | exact Hm'].
        -- exact Hv.
      * subst u.
        assert (HLB : LR B (tm_app t1 t2')).
        { apply LR_value_arrow with (A := A) (t := t1).
          - exact H1.
          - exact Hval.
          - apply LR_step with (T := A) (t := t2); [exact H2 | exact Hstep]. }
        apply LR_value with (t := s).
        -- apply LR_multi with (t := tm_app t1 t2'); [exact HLB | exact Hm'].
        -- exact Hv.
Qed.

Lemma LR_if : forall t1 T t2 t3,
  LR Ty_Bool t1 -> LR T t2 -> LR T t3 -> LR T (tm_if t1 t2 t3).
Proof.
  intros t1 T t2 t3 H1 H2 H3.
  assert (Hsn : strongly_normalizing t1) by (apply LR_sn with (T := Ty_Bool); exact H1).
  revert T t2 t3 H1 H2 H3.
  induction Hsn as [t1 HsnAll IH].
  intros T t2 t3 H1 H2 H3.
  apply LR_intro.
  - (* locally closed *)
    apply lc_if; [apply LR_lc with (T := Ty_Bool); exact H1 | apply LR_lc with (T := T); exact H2 | apply LR_lc with (T := T); exact H3].
  - (* strongly normalizing *)
    apply SN_intro. intros s Hs.
    destruct (step_if_inv t1 t2 t3 s Hs) as [[Eqt Eqs] | [[Eqt Eqs] | [t1' [Hstep Eqs]]]].
    + subst t1. subst s. apply LR_sn with (T := T). exact H2.
    + subst t1. subst s. apply LR_sn with (T := T). exact H3.
    + subst s. apply LR_sn with (T := T).
      apply IH; [exact Hstep | apply LR_step with (T := Ty_Bool) (t := t1); assumption | exact H2 | exact H3].
  - (* value condition *)
    intros s Hm Hv.
    destruct (multi_cases (tm_if t1 t2 t3) s Hm) as [Heq | [u [Hs Hm']]].
    + subst s. exfalso. apply if_not_value in Hv. exact Hv.
    + destruct (step_if_inv t1 t2 t3 u Hs) as [[Eqt Eqs] | [[Eqt Eqs] | [t1' [Hstep Eqs]]]].
      * subst t1. subst u.
        apply LR_value with (t := s).
        -- apply LR_multi with (t := t2); assumption.
        -- exact Hv.
      * subst t1. subst u.
        apply LR_value with (t := s).
        -- apply LR_multi with (t := t3); assumption.
        -- exact Hv.
      * subst u.
        apply LR_value with (t := s).
        -- apply LR_multi with (t := tm_if t1' t2 t3).
           ++ apply IH; [exact Hstep | apply LR_step with (T := Ty_Bool) (t := t1); assumption | exact H2 | exact H3].
           ++ exact Hm'.
        -- exact Hv.
Qed.

(* ---------- Context update lemmas ---------- *)

Lemma update_eq : forall Gamma x T, update Gamma x T x = Some T.
Proof. intros. unfold update. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma update_neq : forall Gamma x y T, x <> y -> update Gamma x T y = Gamma y.
Proof.
  intros Gamma x y T Hne. unfold update.
  apply Nat.eqb_neq in Hne. rewrite Hne. reflexivity.
Qed.

(* ---------- Substitution preserves local closure ---------- *)

Lemma subst_all_lc_at_fvs : forall sigma k t,
  lc_at k t ->
  (forall x, In x (fvs t) -> locally_closed (sigma x)) ->
  lc_at k (subst_all sigma t).
Proof.
  intros sigma k t. revert k.
  induction t as [n | x | t1 IH1 t2 IH2 | T t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
    intros k Hlc Hcl; simpl.
  - apply lc_bvar. apply lc_at_bvar_inv in Hlc. exact Hlc.
  - apply lc_at_mono with (k := 0); [| apply Nat.le_0_l].
    apply Hcl. simpl. left. reflexivity.
  - apply lc_at_app_inv in Hlc. destruct Hlc as [H1 H2].
    apply lc_app.
    + apply IH1; [exact H1 |].
      intros y Hy. apply Hcl. simpl. apply in_app_l. exact Hy.
    + apply IH2; [exact H2 |].
      intros y Hy. apply Hcl. simpl. apply in_app_r. exact Hy.
  - apply lc_at_abs_inv in Hlc. apply lc_abs.
    apply IH1; [exact Hlc |].
    intros y Hy. apply Hcl. simpl. exact Hy.
  - apply lc_true.
  - apply lc_false.
  - apply lc_at_if_inv in Hlc. destruct Hlc as [H1 [H2 H3]].
    apply lc_if.
    + apply IH1; [exact H1 |].
      intros y Hy. apply Hcl. simpl. apply in_app_l. exact Hy.
    + apply IH2; [exact H2 |].
      intros y Hy. apply Hcl. simpl. apply in_app_r. apply in_app_l. exact Hy.
    + apply IH3; [exact H3 |].
      intros y Hy. apply Hcl. simpl. apply in_app_r. apply in_app_r. exact Hy.
Qed.

(* ---------- Opening preserves free variables ---------- *)

Lemma in_fvs_open_rec : forall k y u t,
  In y (fvs t) -> In y (fvs (open_rec k u t)).
Proof.
  intros k y u t. revert k.
  induction t as [n | x | t1 IH1 t2 IH2 | T t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
    intros k Hy; simpl in *.
  - inversion Hy.
  - exact Hy.
  - apply in_or_app. destruct (in_app_or _ _ _ Hy) as [H1 | H2].
    + left. apply IH1 with (k := k). exact H1.
    + right. apply IH2 with (k := k). exact H2.
  - apply IH1 with (k := S k). exact Hy.
  - inversion Hy.
  - inversion Hy.
  - apply in_or_app. destruct (in_app_or _ _ _ Hy) as [Hy' | H3].
    + left. apply IH1 with (k := k). exact Hy'.
    + right. apply in_or_app. destruct (in_app_or _ _ _ H3) as [H2 | H3'].
      * left. apply IH2 with (k := k). exact H2.
      * right. apply IH3 with (k := k). exact H3'.
Qed.

(* ---------- Typing: local closure and free variables ---------- *)

Lemma has_type_lc : forall Gamma t T, has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T H.
  induction H as [Gamma x T Hx
    | L Gamma T1 T2 t1 Hprem IH
    | Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
    | Gamma
    | Gamma
    | Gamma t1 t2 t3 T H1 IH1 H2 IH2 H3 IH3].
  - apply lc_fvar.
  - set (x := fresh (L ++ fvs t1)).
    assert (Hxin : ~ In x (L ++ fvs t1)) by (unfold x; apply fresh_fresh).
    assert (HxL : ~ In x L)
      by (intro Hin; apply Hxin; apply in_or_app; left; exact Hin).
    apply lc_abs.
    apply lc_at_open_inv with (u := tm_fvar x).
    + apply IH. exact HxL.
    + apply lc_fvar.
  - apply lc_app; assumption.
  - apply lc_true.
  - apply lc_false.
  - apply lc_if; assumption.
Qed.

Lemma has_type_fvs : forall Gamma t T, has_type Gamma t T ->
  forall x, In x (fvs t) -> exists S, Gamma x = Some S.
Proof.
  intros Gamma t T H.
  induction H as [Gamma x T Hx
    | L Gamma T1 T2 t1 Hprem IH
    | Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
    | Gamma
    | Gamma
    | Gamma t1 t2 t3 T H1 IH1 H2 IH2 H3 IH3].
  - intros y Hy. simpl in Hy. destruct Hy as [Heq | Hnil].
    + subst y. exists T. exact Hx.
    + inversion Hnil.
  - intros y Hy.
    set (x := fresh (L ++ fvs t1)).
    assert (Hxin : ~ In x (L ++ fvs t1)) by (unfold x; apply fresh_fresh).
    assert (HxL : ~ In x L)
      by (intro Hin; apply Hxin; apply in_or_app; left; exact Hin).
    assert (Hxf : ~ In x (fvs t1))
      by (intro Hin; apply Hxin; apply in_or_app; right; exact Hin).
    assert (Hyopen : In y (fvs (open t1 (tm_fvar x)))).
    { apply in_fvs_open_rec with (k := 0). exact Hy. }
    destruct (IH x HxL y Hyopen) as [S HS].
    exists S.
    unfold update in HS.
    destruct (Nat.eqb x y) eqn:E.
    + inversion HS. subst S.
      exfalso. apply Hxf. apply Nat.eqb_eq in E. subst y. exact Hy.
    + exact HS.
  - intros y Hy. simpl in Hy.
    destruct (in_app_or _ _ _ Hy) as [Hy1 | Hy2].
    + apply IH1. exact Hy1.
    + apply IH2. exact Hy2.
  - intros y Hy. simpl in Hy. inversion Hy.
  - intros y Hy. simpl in Hy. inversion Hy.
  - intros y Hy. simpl in Hy.
    destruct (in_app_or _ _ _ Hy) as [Hy1 | Hy3].
    + apply IH1. exact Hy1.
    + destruct (in_app_or _ _ _ Hy3) as [Hy2 | Hy4].
      * apply IH2. exact Hy2.
      * apply IH3. exact Hy4.
Qed.

(* ---------- The fundamental theorem ---------- *)

Definition valuation (sigma : atom -> tm) (Gamma : context) : Prop :=
  forall x S, Gamma x = Some S -> LR S (sigma x).

Lemma fundamental : forall Gamma t T, has_type Gamma t T ->
  forall sigma, valuation sigma Gamma -> LR T (subst_all sigma t).
Proof.
  intros Gamma t T H.
  induction H as [Gamma x T Hx
    | L Gamma T1 T2 t1 Hprem IH
    | Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
    | Gamma
    | Gamma
    | Gamma t1 t2 t3 T H1 IH1 H2 IH2 H3 IH3].
  - (* T_Var *)
    intros sigma Hval. simpl. apply Hval. exact Hx.
  - (* T_Abs *)
    intros sigma Hval.
    pose proof (T_Abs L Gamma T1 T2 t1 Hprem) as Hjudg.
    assert (Hlcabs : locally_closed (tm_abs T1 t1))
      by (apply has_type_lc with (Gamma := Gamma) (T := Ty_Arrow T1 T2); exact Hjudg).
    assert (Hlcbody : lc_at 1 t1) by (apply lc_at_abs_inv with (T := T1); exact Hlcabs).
    assert (Hslc : forall y, In y (fvs t1) -> locally_closed (sigma y)).
    { intros y Hy.
      destruct (has_type_fvs Gamma (tm_abs T1 t1) (Ty_Arrow T1 T2) Hjudg y Hy)
        as [S HS].
      apply LR_lc with (T := S). apply Hval. exact HS. }
    assert (Hlcsubst : locally_closed (tm_abs T1 (subst_all sigma t1))).
    { apply lc_abs. change (lc_at 1 (subst_all sigma t1)).
      apply subst_all_lc_at_fvs with (sigma := sigma);
        [exact Hlcbody | exact Hslc]. }
    change (LR (Ty_Arrow T1 T2) (tm_abs T1 (subst_all sigma t1))).
    apply LR_intro.
    + exact Hlcsubst.
    + apply SN_abs.
    + intros s Hm Hv.
      assert (E := multi_abs_eq T1 (subst_all sigma t1) s Hm). subst s.
      apply (proj2 (value_cond_arrow T1 T2 (tm_abs T1 (subst_all sigma t1)))).
      intros w Hw.
      apply LR_app_abs with (A := T1) (B := T2) (body := subst_all sigma t1).
      * exact Hlcsubst.
      * intros v HvLR.
        set (x := fresh (L ++ fvs t1)).
        assert (Hxin : ~ In x (L ++ fvs t1)) by (unfold x; apply fresh_fresh).
        assert (HxL : ~ In x L)
          by (intro Hin; apply Hxin; apply in_or_app; left; exact Hin).
        assert (Hxf : ~ In x (fvs t1))
          by (intro Hin; apply Hxin; apply in_or_app; right; exact Hin).
        assert (Hval' : valuation (update_subst sigma x v) (update Gamma x T1)).
        { intros y S Hy.
          unfold update in Hy. unfold update_subst.
          destruct (Nat.eqb x y) eqn:E.
          - inversion Hy. subst S. exact HvLR.
          - apply Hval. exact Hy. }
        pose proof (IH x HxL (update_subst sigma x v) Hval') as Hsub.
        rewrite (subst_open_fresh sigma x v t1 Hxf Hslc (LR_lc T1 v HvLR)) in Hsub.
        exact Hsub.
      * exact Hw.
  - (* T_App *)
    intros sigma Hval. simpl.
    apply LR_app with (A := T1) (B := T2).
    + apply IH1. exact Hval.
    + apply IH2. exact Hval.
  - (* T_True *)
    intros sigma Hval. change (LR Ty_Bool tm_true).
    apply LR_intro.
    + apply lc_true.
    + apply SN_true.
    + intros s Hm Hv.
      assert (E := multi_true_eq s Hm). subst s.
      simpl. left. reflexivity.
  - (* T_False *)
    intros sigma Hval. change (LR Ty_Bool tm_false).
    apply LR_intro.
    + apply lc_false.
    + apply SN_false.
    + intros s Hm Hv.
      assert (E := multi_false_eq s Hm). subst s.
      simpl. right. reflexivity.
  - (* T_If *)
    intros sigma Hval. simpl.
    apply LR_if.
    + apply IH1. exact Hval.
    + apply IH2. exact Hval.
    + apply IH3. exact Hval.
Qed.

(* ---------- Target theorem ---------- *)

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T H.
  assert (Hval : valuation (fun x => tm_fvar x) empty).
  { intros x S Hx. unfold empty in Hx. discriminate. }
  pose proof (fundamental empty t T H (fun x => tm_fvar x) Hval) as HLR.
  rewrite subst_all_id in HLR.
  apply LR_sn with (T := T). exact HLR.
Qed.
End STLCCBVNormalizationTask.
