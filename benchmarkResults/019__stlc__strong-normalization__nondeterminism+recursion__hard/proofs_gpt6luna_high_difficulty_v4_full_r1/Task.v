(** STLC CBV strong-normalization benchmark, Hard variant.
    Features: nondeterminism-recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Relations.Relation_Definitions Lia Program.Equality.
Import ListNotations.

Module STLCNormalizationNondeterminismRecursionHardTask.

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

  | tm_natrec : tm -> tm -> tm -> tm
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
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (open_rec k u t1)
  | tm_natrec n b s =>
      tm_natrec (open_rec k u n) (open_rec k u b) (open_rec k u s)
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
  | lc_zero : forall k, lc_at k tm_zero
  | lc_succ : forall k t, lc_at k t -> lc_at k (tm_succ t)
  | lc_rec : forall k n b s,
      lc_at k n -> lc_at k b -> lc_at k s ->
      lc_at k (tm_natrec n b s)
    | lc_choice : forall k t1 t2,
      lc_at k t1 -> lc_at k t2 -> lc_at k (tm_choice t1 t2).

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
  | T_Choice : forall Gamma t1 t2 T,
      <{ Gamma |-- $(t1) \in T }> ->
      <{ Gamma |-- $(t2) \in T }> ->
      <{ Gamma |-- choice $(t1) or $(t2) \in T }>
where "<{ Gamma '|--' t '\in' T }>" := (has_type Gamma t T)
  : stlc_scope.

Hint Constructors has_type : core.

(* Simultaneous substitution for free variables. *)
Fixpoint subst (rho : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => rho x
  | tm_app t1 t2 => tm_app (subst rho t1) (subst rho t2)
  | tm_abs T t1 => tm_abs T (subst rho t1)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (subst rho t1)
  | tm_natrec n b s => tm_natrec (subst rho n) (subst rho b) (subst rho s)
  | tm_choice t1 t2 => tm_choice (subst rho t1) (subst rho t2)
  end.

Fixpoint fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_app t1 t2 => fv t1 ++ fv t2
  | tm_abs _ t1 => fv t1
  | tm_true | tm_false | tm_zero => []
  | tm_succ t1 => fv t1
  | tm_natrec n b s => fv n ++ fv b ++ fv s
  | tm_choice t1 t2 => fv t1 ++ fv t2
  end.

Lemma subst_ext_fv : forall t rho sigma,
  (forall x, In x (fv t) -> rho x = sigma x) -> subst rho t = subst sigma t.
Proof.
  induction t; intros rho sigma Heq; simpl in *; try reflexivity.
  - apply Heq; simpl; auto.
  - f_equal; [apply IHt1|apply IHt2]; intros x Hin; apply Heq; apply in_or_app; auto.
  - f_equal; apply IHt; exact Heq.
  - f_equal; apply IHt; exact Heq.
  - f_equal; [apply IHt1|apply IHt2|apply IHt3]; intros x Hin; apply Heq.
    + apply in_or_app; left; exact Hin.
    + apply in_or_app; right; apply in_or_app; left; exact Hin.
    + apply in_or_app; right; apply in_or_app; right; exact Hin.
  - f_equal; [apply IHt1|apply IHt2]; intros x Hin; apply Heq; apply in_or_app; auto.
Qed.

Lemma fv_open_preserve : forall t k u x,
  In x (fv t) -> In x (fv (open_rec k u t)).
Proof.
  induction t; intros k u x Hin; simpl in *; try contradiction; try exact Hin.
  - apply in_app_or in Hin as [H|H]; apply in_or_app; [left; eapply IHt1|right; eapply IHt2]; eauto.
  - eapply IHt; eauto.
  - eapply IHt; eauto.
  - apply in_app_or in Hin as [H|Hin].
    + apply in_or_app; left; eapply IHt1; eauto.
    + apply in_app_or in Hin as [H|H].
      * apply in_or_app; right; apply in_or_app; left; eapply IHt2; eauto.
      * apply in_or_app; right; apply in_or_app; right; eapply IHt3; eauto.
  - apply in_app_or in Hin as [H|H]; apply in_or_app; [left; eapply IHt1|right; eapply IHt2]; eauto.
Qed.

Lemma max_list : forall (xs : list atom) (x : atom), In x xs -> x <= fold_right Nat.max 0 xs.
Proof.
  induction xs; simpl; intros x Hin; [contradiction|].
  destruct Hin as [->|Hin]; [apply Nat.le_max_l|].
  eapply Nat.le_trans; [apply IHxs; exact Hin|apply Nat.le_max_r].
Qed.

Lemma fresh_list : forall (xs : list atom), exists x : atom, ~ In x xs.
Proof.
  intros xs; exists (S (fold_right Nat.max 0 xs)); intros Hin.
  pose proof (max_list xs _ Hin); lia.
Qed.

Lemma update_eq : forall Gamma x T, update Gamma x T x = Some T.
Proof. intros; unfold update; rewrite Nat.eqb_refl; reflexivity. Qed.

Lemma update_neq : forall Gamma x y T, x <> y -> update Gamma x T y = Gamma y.
Proof. intros; unfold update; apply Nat.eqb_neq in H; rewrite H; reflexivity. Qed.

Lemma typing_fv : forall Gamma t T,
  <{ Gamma |-- t \in T }> -> forall x, In x (fv t) -> exists U, Gamma x = Some U.
Proof.
  intros Gamma t T H; induction H; intros y Hy; simpl in *.
  - destruct Hy as [<-|[]]. exists T; exact H.
  - destruct (fresh_list (L ++ fv t1)) as [z Hz].
    assert (HzL : ~ In z L) by (intro Hin; apply Hz; apply in_or_app; left; exact Hin).
    assert (Hzy : z <> y).
    { intro E; subst. apply Hz; apply in_or_app; right; exact Hy. }
    assert (Hyopen : In y (fv (open t1 (tm_fvar z)))).
    { unfold open; eapply fv_open_preserve; exact Hy. }
    destruct (H0 z HzL y Hyopen) as [U HU].
    exists U. rewrite update_neq in HU by exact Hzy. exact HU.
  - apply in_app_or in Hy as [Hy|Hy]; [eapply IHhas_type1|eapply IHhas_type2]; eauto.
  - contradiction.
  - contradiction.
  - contradiction.
  - eapply IHhas_type; eauto.
  - apply in_app_or in Hy as [Hy|Hy].
    + eapply IHhas_type1; eauto.
    + apply in_app_or in Hy as [Hy|Hy].
      * eapply IHhas_type2; eauto.
      * eapply IHhas_type3; eauto.
  - apply in_app_or in Hy as [Hy|Hy]; [eapply IHhas_type1|eapply IHhas_type2]; eauto.
Qed.

Lemma open_rec_lc : forall d k t u,
  lc_at d t -> open_rec (d + k) u t = t.
Proof.
  intros d k t u H; revert k; induction H; intros kk; simpl.
  - destruct (Nat.eqb (k + kk) i) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - f_equal; eauto.
  - replace (S (k + kk)) with (S k + kk) by lia. f_equal; eauto.
  - f_equal; eauto.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
Qed.

Lemma subst_open_rec : forall rho k t u,
  (forall x, lc_at 0 (rho x)) ->
  subst rho (open_rec k u t) = open_rec k (subst rho u) (subst rho t).
Proof.
  intros rho k t; revert k; induction t; intros k u Hr; simpl; try rewrite IHt by exact Hr; try rewrite IHt1 by exact Hr; try rewrite IHt2 by exact Hr; try rewrite IHt3 by exact Hr; try reflexivity.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry; apply open_rec_lc with (d:=0) (k:=k) (u:=subst rho u); apply Hr.
Qed.

Lemma subst_open : forall rho t u,
  (forall x, lc_at 0 (rho x)) ->
  subst rho (open t u) = open (subst rho t) (subst rho u).
Proof. intros; apply subst_open_rec; assumption. Qed.

Lemma lc_mono : forall k j t, k <= j -> lc_at k t -> lc_at j t.
Proof.
  intros k j t Hkj H; revert j Hkj; induction H; intros j Hkj; eauto using lc_at; try (constructor; lia).
  - constructor; apply IHlc_at; lia.
Qed.

Lemma subst_lc : forall k t rho,
  lc_at k t -> (forall x, lc_at 0 (rho x)) -> lc_at k (subst rho t).
Proof.
  intros k t rho H; induction H; intros Hr; simpl; eauto using lc_at.
  apply lc_mono with (k:=0); [lia|apply Hr].
Qed.

Lemma lc_open_inv : forall k t u,
  lc_at k u -> lc_at k (open_rec k u t) -> lc_at (S k) t.
Proof.
  intros k t; revert k; induction t; intros k u Hu Hopen; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst; constructor; lia.
    + inversion Hopen; subst; constructor; lia.
  - inversion Hopen; constructor.
  - inversion Hopen; subst; apply lc_app.
    + exact (IHt1 k u Hu H2).
    + exact (IHt2 k u Hu H3).
  - inversion Hopen; subst; apply lc_abs.
    apply IHt with (k:=S k) (u:=u).
    + apply (lc_mono k (S k) u); [lia|exact Hu].
    + assumption.
  - constructor.
  - constructor.
  - constructor.
  - inversion Hopen; subst; apply lc_succ; exact (IHt k u Hu H1).
  - inversion Hopen; subst; apply lc_rec.
    + exact (IHt1 k u Hu H3).
    + exact (IHt2 k u Hu H4).
    + exact (IHt3 k u Hu H5).
  - inversion Hopen; subst; apply lc_choice.
    + exact (IHt1 k u Hu H2).
    + exact (IHt2 k u Hu H3).
Qed.

Lemma typing_lc : forall Gamma t T,
  <{ Gamma |-- t \in T }> -> locally_closed t.
Proof.
  intros Gamma t T H; induction H; unfold locally_closed; simpl; eauto using lc_at.
  - destruct (fresh_list L) as [x Hx].
    apply lc_abs. eapply lc_open_inv with (k:=0) (u:=tm_fvar x).
    + constructor.
    + apply H0; exact Hx.
Qed.

Lemma lc_open : forall d t u,
  lc_at (S d) t -> lc_at d u -> lc_at d (open_rec d u t).
Proof.
  intros d t; revert d; induction t; intros d u Ht Hu; simpl in *.
  - inversion Ht; subst. destruct (Nat.eqb d n) eqn:E.
    + apply Nat.eqb_eq in E; subst; exact Hu.
    + apply Nat.eqb_neq in E; constructor; lia.
  - inversion Ht; constructor.
  - inversion Ht; subst; constructor; [eapply IHt1|eapply IHt2]; eauto.
  - inversion Ht; subst; apply lc_abs.
    apply IHt with (d:=S d) (u:=u).
    + assumption.
    + apply (lc_mono d (S d) u); [lia|exact Hu].
  - constructor.
  - constructor.
  - constructor.
  - inversion Ht; subst; apply lc_succ; eapply IHt; eauto.
  - inversion Ht; subst; apply lc_rec; [eapply IHt1|eapply IHt2|eapply IHt3]; eauto.
  - inversion Ht; subst; apply lc_choice; [eapply IHt1|eapply IHt2]; eauto.
Qed.

Lemma numeric_value_lc : forall n, numeric_value n -> locally_closed n.
Proof. intros n H; induction H; unfold locally_closed in *; eauto using lc_at. Qed.

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v Hv; induction Hv.
  - assumption.
  - unfold locally_closed; constructor.
  - unfold locally_closed; constructor.
  - apply numeric_value_lc; assumption.
Qed.

Lemma step_lc : forall t t', locally_closed t -> t --> t' -> locally_closed t'.
Proof.
  intros t t' Hlc Hs; induction Hs; unfold locally_closed in *.
  - inversion Hlc; subst. inversion H; subst. apply lc_open; [assumption|apply value_lc; assumption].
  - inversion Hlc; subst; apply lc_app; [apply IHHs; assumption|assumption].
  - inversion Hlc; subst; apply lc_app; [apply value_lc; assumption|apply IHHs; assumption].
  - inversion Hlc; subst; apply lc_succ; apply IHHs; assumption.
  - inversion Hlc; subst; apply lc_rec; [apply IHHs; assumption|assumption|assumption].
  - inversion Hlc; subst; apply lc_rec; [assumption|apply IHHs; assumption|assumption].
  - inversion Hlc; subst; apply lc_rec; [assumption|assumption|apply IHHs; assumption].
  - inversion Hlc; subst; assumption.
  - inversion Hlc; subst; apply lc_app; [apply lc_app; [apply value_lc; assumption|apply numeric_value_lc; assumption]|apply lc_rec; [apply numeric_value_lc; assumption|apply value_lc; assumption|apply value_lc; assumption]].
  - inversion Hlc; subst; assumption.
  - inversion Hlc; subst; assumption.
Qed.


Inductive strongly_normalizing : tm -> Prop :=

  | SN_intro : forall t,
      (forall t', t --> t' -> strongly_normalizing t') ->
      strongly_normalizing t.

Fixpoint reducible (T : ty) (t : tm) : Prop :=
  locally_closed t /\ strongly_normalizing t /\
  (forall q, t -->* q -> value q \/ exists q', q --> q') /\
  match T with
  | Ty_Bool => forall v, t -->* v -> value v -> v = tm_true \/ v = tm_false
  | Ty_Nat => forall v, t -->* v -> value v -> numeric_value v
  | Ty_Arrow A B => forall u, reducible A u -> reducible B (tm_app t u)
  end.

Lemma SN_step : forall t t', strongly_normalizing t -> t --> t' -> strongly_normalizing t'.
Proof. intros t t' H; inversion H; eauto. Qed.

Lemma SN_from_steps : forall t,
  (forall t', t --> t' -> strongly_normalizing t') -> strongly_normalizing t.
Proof. intros; constructor; assumption. Qed.

Lemma multi_transitive : forall t u v, t -->* u -> u -->* v -> t -->* v.
Proof.
  intros t u v H; revert v; induction H; intros v Hv.
  - exact Hv.
  - eapply multi_step; [eassumption|apply IHmulti; exact Hv].
Qed.

Lemma numeric_no_step : forall n n', numeric_value n -> ~ (n --> n').
Proof.
  intros n n' H; revert n'; induction H; intros n' Hs; inversion Hs; subst; eauto.
  eapply IHnumeric_value; eassumption.
Qed.

Lemma value_no_step : forall v v', value v -> ~ (v --> v').
Proof.
  intros v v' Hv Hs; dependent destruction Hv; inversion Hs; subst;
    try (match goal with Hn : numeric_value _ |- _ => inversion Hn end);
    try (match goal with Hn : numeric_value ?n, Hstep : ?n --> ?m |- _ => exact (numeric_no_step _ _ Hn Hstep) end);
    eauto using numeric_no_step.
Qed.

Lemma reducible_lc : forall T t, reducible T t -> locally_closed t.
Proof. intros T t H; destruct T; simpl in H; tauto. Qed.

Lemma reducible_progress : forall T t q,
  reducible T t -> t -->* q -> value q \/ exists q', q --> q'.
Proof.
  intros T t q H Hm; destruct T; simpl in H;
    destruct H as [_ [_ [Hp _]]]; eapply Hp; exact Hm.
Qed.

Lemma reducible_rel : forall T t,
  reducible T t ->
  match T with
  | Ty_Bool => forall v, t -->* v -> value v -> v = tm_true \/ v = tm_false
  | Ty_Nat => forall v, t -->* v -> value v -> numeric_value v
  | Ty_Arrow A B => forall u, reducible A u -> reducible B (tm_app t u)
  end.
Proof. intros T t H; destruct T; simpl in H; destruct H as [_ [_ [_ Hr]]]; exact Hr. Qed.

Lemma reducible_step : forall T t t', reducible T t -> t --> t' -> reducible T t'.
Proof.
  induction T; intros t t' [Hlc [Hsn [Hprog Hrel]]] Hs; simpl in *.
  - split; [eapply step_lc; eauto|]. split; [eapply SN_step; eauto|]. split.
    + intros q Hmulti. apply Hprog with (q:=q). eapply multi_step; eauto.
    +
    intros v Hmulti Hv. eapply Hrel; [eapply multi_step; eauto|exact Hv].
  - split; [eapply step_lc; eauto|]. split; [eapply SN_step; eauto|]. split.
    + intros q Hmulti. apply Hprog with (q:=q). eapply multi_step; eauto.
    +
    intros v Hmulti Hv. eapply Hrel; [eapply multi_step; eauto|exact Hv].
  - split; [eapply step_lc; eauto|]. split; [eapply SN_step; eauto|]. split.
    + intros q Hmulti. apply Hprog with (q:=q). eapply multi_step; eauto.
    +
    intros u Hu. specialize (Hrel u Hu).
    eapply IHT2; [exact Hrel|].
    apply ST_App1; [exact Hs|apply reducible_lc with (T:=T1); exact Hu].
Qed.

Lemma reducible_multi : forall T t u, reducible T t -> t -->* u -> reducible T u.
Proof.
  intros T t u Hr Hm; induction Hm; [exact Hr|].
  apply IHHm. eapply reducible_step; eauto.
Qed.

Lemma reducible_sn : forall T t, reducible T t -> strongly_normalizing t.
Proof. intros T t H; destruct T; simpl in H; tauto. Qed.

Lemma reducible_expand : forall T t,
  locally_closed t -> ~ value t -> (exists t', t --> t') ->
  (forall t', t --> t' -> reducible T t') -> reducible T t.
Proof.
  induction T; intros t Hlc Hnv Hhasstep Hsteps; simpl.
  - split; [exact Hlc|]. split.
    + apply SN_from_steps. intros t' Hs. apply reducible_sn with (T:=Ty_Bool); apply Hsteps; exact Hs.
    + split.
      * intros q Hm. inversion Hm; subst.
        -- right; exact Hhasstep.
        -- destruct (Hsteps y H) as [_ [_ [Hp _]]]. eapply Hp; eauto.
      * intros v Hm Hv. inversion Hm; subst.
        -- contradiction.
        -- destruct (Hsteps y H) as [_ [_ [_ Hshape]]]. eapply Hshape; eauto.
  - split; [exact Hlc|]. split.
    + apply SN_from_steps. intros t' Hs. apply reducible_sn with (T:=Ty_Nat); apply Hsteps; exact Hs.
    + split.
      * intros q Hm. inversion Hm; subst.
        -- right; exact Hhasstep.
        -- destruct (Hsteps y H) as [_ [_ [Hp _]]]. eapply Hp; eauto.
      * intros v Hm Hv. inversion Hm; subst.
        -- contradiction.
        -- destruct (Hsteps y H) as [_ [_ [_ Hshape]]]. eapply Hshape; eauto.
  - split; [exact Hlc|]. split.
    + apply SN_from_steps. intros t' Hs. apply reducible_sn with (T:=Ty_Arrow T1 T2); apply Hsteps; exact Hs.
    + split.
      * intros q Hm. inversion Hm; subst.
        -- right; exact Hhasstep.
        -- destruct (Hsteps y H) as [_ [_ [Hp _]]]. eapply Hp; eauto.
      * intros u Hu.
        eapply IHT2.
        -- apply lc_app; [exact Hlc|apply reducible_lc with (T:=T1); exact Hu].
        -- intros Hv; dependent destruction Hv; match goal with Hn : numeric_value _ |- _ => inversion Hn end.
        -- destruct Hhasstep as [t' Ht']; exists (tm_app t' u); apply ST_App1; [exact Ht'|apply reducible_lc with (T:=T1); exact Hu].
        -- intros q Hq. inversion Hq; subst.
           ++ exfalso; apply Hnv; constructor; assumption.
           ++ destruct (Hsteps t1' H1) as [_ [_ [_ Hsem]]]. apply Hsem; exact Hu.
           ++ exfalso; apply Hnv; assumption.
Qed.

Lemma app_not_value : forall t u, ~ value (tm_app t u).
Proof.
  intros t u Hv; dependent destruction Hv;
    match goal with Hn : numeric_value _ |- _ => inversion Hn end.
Qed.

Lemma SN_induction : forall (P : tm -> Prop) t,
  strongly_normalizing t ->
  (forall t, (forall t', t --> t' -> P t') -> P t) -> P t.
Proof.
  intros P t H; induction H; intros Hrec; apply Hrec; intros t' Hs; eauto.
Qed.

Lemma reducible_abs_app : forall A B T body u,
  locally_closed (tm_abs T body) ->
  (forall v, reducible A v -> reducible B (open body v)) ->
  reducible A u -> reducible B (tm_app (tm_abs T body) u).
Proof.
  intros A B T body u Habs Hbody Hu.
  eapply (SN_induction (fun a => reducible A a -> reducible B (tm_app (tm_abs T body) a)) u).
  - apply reducible_sn with (T:=A); exact Hu.
  - intros a IH Ha.
    apply reducible_expand.
    + apply lc_app; [exact Habs|apply reducible_lc with (T:=A); exact Ha].
    + apply app_not_value.
    + destruct (reducible_progress A a a Ha (multi_refl step a)) as [Hv|[a' Hstep]].
      * exists (open body a); apply ST_AppAbs; [exact Habs|exact Hv].
      * exists (tm_app (tm_abs T body) a'); apply ST_App2; [constructor; exact Habs|exact Hstep].
    + intros q Hq. inversion Hq; subst.
      * apply Hbody; exact Ha.
      * exfalso. eapply value_no_step; [constructor; exact Habs|eassumption].
      * apply IH; [assumption|]. eapply reducible_step; eauto.
  - exact Hu.
Qed.

Lemma multi_from_value : forall v u, value v -> v -->* u -> u = v.
Proof.
  intros v u Hv Hm; induction Hm.
  - reflexivity.
  - exfalso; eapply value_no_step; eauto.
Qed.

Lemma reducible_numeric : forall n, numeric_value n -> reducible Ty_Nat n.
Proof.
  intros n Hn; unfold locally_closed; split.
  - apply numeric_value_lc; exact Hn.
  - split.
    + constructor; intros t' Hs; exfalso; eapply numeric_no_step; eauto.
    + split.
      * intros q Hm. rewrite (multi_from_value n q (v_nat n Hn) Hm); left; constructor; exact Hn.
      * intros v Hm Hv. rewrite (multi_from_value n v (v_nat n Hn) Hm); exact Hn.
Qed.

Lemma reducible_true : reducible Ty_Bool tm_true.
Proof.
  unfold locally_closed; split; [constructor|]. split.
  - constructor; intros t' Hs; inversion Hs.
  - split.
    + intros q Hm. rewrite (multi_from_value tm_true q v_true Hm); left; constructor.
    + intros v Hm Hv. rewrite (multi_from_value tm_true v v_true Hm); auto.
Qed.

Lemma reducible_false : reducible Ty_Bool tm_false.
Proof.
  unfold locally_closed; split; [constructor|]. split.
  - constructor; intros t' Hs; inversion Hs.
  - split.
    + intros q Hm. rewrite (multi_from_value tm_false q v_false Hm); left; constructor.
    + intros v Hm Hv. rewrite (multi_from_value tm_false v v_false Hm); auto.
Qed.

Lemma reducible_zero : reducible Ty_Nat tm_zero.
Proof. apply reducible_numeric; constructor. Qed.

Lemma SN_succ : forall n, strongly_normalizing n -> strongly_normalizing (tm_succ n).
Proof.
  intros n H; induction H; constructor; intros t' Hs; inversion Hs; subst; eauto.
Qed.

Lemma multi_succ_inv : forall n v,
  tm_succ n -->* v -> exists n', v = tm_succ n' /\ n -->* n'.
Proof.
  intros n v H. remember (tm_succ n) as start eqn:E in H.
  revert n E; induction H; intros n E.
  - inversion E; subst; exists n; split; [reflexivity|constructor].
  - inversion E; subst. inversion H; subst.
    destruct (IHmulti t' eq_refl) as [n' [E' Hm]].
    exists n'; split; [exact E'|eapply multi_step; [exact H3|exact Hm]].
Qed.

Lemma reducible_succ : forall n, reducible Ty_Nat n -> reducible Ty_Nat (tm_succ n).
Proof.
  intros n [Hlc [Hsn [Hprog Hshape]]]. split.
  - unfold locally_closed in *; constructor; exact Hlc.
  - split.
    + apply SN_succ; exact Hsn.
    + split.
      * intros q Hm. destruct (multi_succ_inv n q Hm) as [n' [-> Hn]].
        destruct (Hprog n' Hn) as [Hv|[n'' Hstep]].
        -- left. apply v_nat. apply nv_succ. eapply Hshape; eauto.
        -- right. exists (tm_succ n''); apply ST_Succ; exact Hstep.
      * intros v Hm Hv. destruct (multi_succ_inv n v Hm) as [n' [-> Hn]].
        dependent destruction Hv. inversion H; subst; apply nv_succ.
        eapply Hshape; [exact Hn|constructor; exact H1].
Qed.

Lemma reducible_choice : forall T t1 t2,
  reducible T t1 -> reducible T t2 -> reducible T (tm_choice t1 t2).
Proof.
  intros T t1 t2 H1 H2. apply reducible_expand.
  - apply lc_choice; [apply reducible_lc in H1|apply reducible_lc in H2]; assumption.
  - intros Hv; dependent destruction Hv; match goal with Hn : numeric_value _ |- _ => inversion Hn end.
  - exists t1. apply ST_ChoiceLeft; apply reducible_lc with (T:=T); assumption.
  - intros t' Hs; inversion Hs; subst; assumption.
Qed.

Lemma reducible_natrec_numeric : forall T n,
  numeric_value n -> forall b s,
  reducible T b -> reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  reducible T (tm_natrec n b s).
Proof.
  intros T n Hn; induction Hn as [|n Hpred IHn]; intros b s Hb Hs.
  - apply (SN_induction
      (fun b0 => reducible T b0 -> forall s0, reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s0 -> reducible T (tm_natrec tm_zero b0 s0))
      b (reducible_sn T b Hb)).
    intros b0 IHb Hb0 s0 Hs0.
    apply (SN_induction
      (fun s1 => reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s1 -> reducible T (tm_natrec tm_zero b0 s1))
      s0 (reducible_sn _ _ Hs0)).
    intros s1 IHs Hs1. apply reducible_expand.
    + apply lc_rec; [constructor|apply reducible_lc with (T:=T); exact Hb0|apply reducible_lc with (T:=Ty_Arrow Ty_Nat (Ty_Arrow T T)); exact Hs1].
    + intros Hv; dependent destruction Hv; match goal with Hnv : numeric_value _ |- _ => inversion Hnv end.
    + destruct (reducible_progress T b0 b0 Hb0 (multi_refl step b0)) as [Vb|[b' Hbstep]].
      * destruct (reducible_progress _ s1 s1 Hs1 (multi_refl step s1)) as [Vs|[s' Hsstep]].
        -- exists b0; apply ST_RecZero; assumption.
        -- exists (tm_natrec tm_zero b0 s'); apply ST_RecStep; [constructor|exact Vb|exact Hsstep].
      * exists (tm_natrec tm_zero b' s1); apply ST_RecBase; [constructor|exact Hbstep|apply reducible_lc with (T:=Ty_Arrow Ty_Nat (Ty_Arrow T T)); exact Hs1].
    + intros q Hq; inversion Hq; subst.
      * exfalso; exact (numeric_no_step tm_zero n' nv_zero H2).
      * exact (IHb b' H4 (reducible_step T b0 b' Hb0 H4) s1 Hs1).
      * exact (IHs s' H5 (reducible_step (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s1 s' Hs1 H5)).
      * exact Hb0.
    + exact Hs0.
    + exact Hb.
    + exact Hs.
  - apply (SN_induction
      (fun b0 => reducible T b0 -> forall s0, reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s0 -> reducible T (tm_natrec (tm_succ n) b0 s0))
      b (reducible_sn T b Hb)).
    intros b0 IHb Hb0 s0 Hs0.
    apply (SN_induction
      (fun s1 => reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s1 -> reducible T (tm_natrec (tm_succ n) b0 s1))
      s0 (reducible_sn _ _ Hs0)).
    intros s1 IHs Hs1. apply reducible_expand.
    + apply lc_rec; [apply numeric_value_lc; constructor; assumption|apply reducible_lc with (T:=T); exact Hb0|apply reducible_lc with (T:=Ty_Arrow Ty_Nat (Ty_Arrow T T)); exact Hs1].
    + intros Hv; dependent destruction Hv; match goal with Hnv : numeric_value _ |- _ => inversion Hnv end.
    + destruct (reducible_progress T b0 b0 Hb0 (multi_refl step b0)) as [Vb|[b' Hbstep]].
      * destruct (reducible_progress _ s1 s1 Hs1 (multi_refl step s1)) as [Vs|[s' Hsstep]].
        -- exists (tm_app (tm_app s1 n) (tm_natrec n b0 s1)); apply ST_RecSucc; [exact Hpred|exact Vb|exact Vs].
        -- exists (tm_natrec (tm_succ n) b0 s'); apply ST_RecStep; [constructor; exact Hpred|exact Vb|exact Hsstep].
      * exists (tm_natrec (tm_succ n) b' s1); apply ST_RecBase; [constructor; exact Hpred|exact Hbstep|apply reducible_lc with (T:=Ty_Arrow Ty_Nat (Ty_Arrow T T)); exact Hs1].
    + intros q Hq; inversion Hq; subst.
      * exfalso; exact (numeric_no_step (tm_succ n) n' (nv_succ n Hpred) H2).
      * apply (IHb b'); [assumption|eapply reducible_step; eauto|exact Hs1].
      * apply IHs; [assumption|eapply reducible_step; eauto].
      * pose proof Hs1 as Hs1copy. destruct Hs1copy as [_ [_ [_ Hsem]]].
        pose proof (Hsem n (reducible_numeric n H2)) as Hsn.
        destruct Hsn as [_ [_ [_ Hsem2]]].
        apply Hsem2. exact (IHn b0 s1 Hb0 Hs1).
    + exact Hs0.
    + exact Hb.
    + exact Hs.
Qed.

Lemma reducible_natrec : forall T n b s,
  reducible Ty_Nat n -> reducible T b ->
  reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  reducible T (tm_natrec n b s).
Proof.
  intros T n b s Hn.
  eapply (SN_induction
    (fun n0 => reducible Ty_Nat n0 -> forall b0 s0,
       reducible T b0 -> reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s0 ->
       reducible T (tm_natrec n0 b0 s0)) n).
  - apply reducible_sn with (T:=Ty_Nat); exact Hn.
  - intros n0 IHn Hn0 b0 s0 Hb0 Hs0.
    destruct (reducible_progress Ty_Nat n0 n0 Hn0 (multi_refl step n0)) as [Vn|[n' Hstep]].
    + pose proof (reducible_rel Ty_Nat n0 Hn0 n0 (multi_refl step n0) Vn) as Hnum.
      eapply reducible_natrec_numeric; [exact Hnum|exact Hb0|exact Hs0].
    + assert (Hnv : ~ value n0) by (intros Hv; eapply value_no_step; eauto).
      apply reducible_expand.
      * apply lc_rec; [apply reducible_lc with (T:=Ty_Nat); exact Hn0|apply reducible_lc with (T:=T); exact Hb0|apply reducible_lc with (T:=Ty_Arrow Ty_Nat (Ty_Arrow T T)); exact Hs0].
      * intros Hv; dependent destruction Hv; match goal with Hnum : numeric_value _ |- _ => inversion Hnum end.
      * exists (tm_natrec n' b0 s0); apply ST_RecArg; [exact Hstep|apply reducible_lc with (T:=T); exact Hb0|apply reducible_lc with (T:=Ty_Arrow Ty_Nat (Ty_Arrow T T)); exact Hs0].
      * intros q Hq; inversion Hq; subst.
        -- exact (IHn n'0 H2 (reducible_step Ty_Nat n0 n'0 Hn0 H2) b0 s0 Hb0 Hs0).
        -- exfalso; apply Hnv; exact (v_nat n0 H2).
        -- exfalso; apply Hnv; exact (v_nat n0 H2).
        -- exfalso; apply Hnv; exact (v_nat tm_zero nv_zero).
        -- exfalso; apply Hnv; exact (v_nat (tm_succ n1) (nv_succ n1 H2)).
  - exact Hn.
Qed.

Definition extend_subst (rho : atom -> tm) (x : atom) (u : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then u else rho y.

Lemma subst_extend_open : forall rho x u t,
  (forall y, locally_closed (rho y)) ->
  locally_closed u ->
  ~ In x (fv t) ->
  subst (extend_subst rho x u) (open t (tm_fvar x)) = open (subst rho t) u.
Proof.
  intros rho x u t Hlc Hu Hfresh. rewrite subst_open.
  2:{ intros y; unfold extend_subst; destruct (Nat.eqb x y); [exact Hu|apply Hlc]. }
  f_equal.
  - apply subst_ext_fv; intros y Hy; unfold extend_subst.
    destruct (Nat.eqb x y) eqn:E; [apply Nat.eqb_eq in E; subst; contradiction|reflexivity].
  - unfold extend_subst; simpl. destruct (Nat.eqb x x) eqn:E; [reflexivity|apply Nat.eqb_neq in E; contradiction].
Qed.

Theorem fundamental : forall Gamma t T,
  <{ Gamma |-- t \in T }> -> forall rho,
  (forall x, locally_closed (rho x)) ->
  (forall x U, Gamma x = Some U -> reducible U (rho x)) ->
  reducible T (subst rho t).
Proof.
  intros Gamma t T Hty; induction Hty; intros rho Hrho Henv; simpl.
  - apply Henv with (x:=x); exact H.
  - destruct (fresh_list (L ++ fv t1)) as [z Hz].
    assert (HzL : ~ In z L) by (intro Hin; apply Hz; apply in_or_app; left; exact Hin).
    assert (Hzfv : ~ In z (fv t1)) by (intro Hin; apply Hz; apply in_or_app; right; exact Hin).
    assert (Habs_lc : locally_closed (tm_abs T1 (subst rho t1))).
    { unfold locally_closed. apply lc_abs.
      assert (Htlc : lc_at 1 t1).
      { apply lc_open_inv with (k:=0) (u:=tm_fvar z); [constructor|].
        apply typing_lc with (Gamma:=update Gamma z T1) (T:=T2); apply H; exact HzL. }
      eapply subst_lc; [exact Htlc|exact Hrho]. }
    split; [exact Habs_lc|]. split.
    + constructor; intros q Hq; inversion Hq.
    + split.
      * intros q Hm. rewrite (multi_from_value (tm_abs T1 (subst rho t1)) q (v_abs T1 (subst rho t1) Habs_lc) Hm). left; constructor; exact Habs_lc.
      * intros u Hu.
      eapply reducible_abs_app; [exact Habs_lc| |exact Hu].
      intros v Hv.
      assert (Hrho' : forall y, locally_closed (extend_subst rho z v y)).
      { intros y; unfold extend_subst; destruct (Nat.eqb z y) eqn:E.
        - apply Nat.eqb_eq in E; subst y; exact (reducible_lc T1 v Hv).
        - apply Hrho. }
      assert (Henv' : forall y U, update Gamma z T1 y = Some U -> reducible U (extend_subst rho z v y)).
      { intros y U Hy. unfold extend_subst.
        destruct (Nat.eqb z y) eqn:E.
        - apply Nat.eqb_eq in E; subst. rewrite update_eq in Hy. inversion Hy; subst; exact Hv.
        - apply Nat.eqb_neq in E. rewrite update_neq in Hy by congruence. eapply Henv; exact Hy. }
      specialize (H0 z HzL (extend_subst rho z v) Hrho' Henv').
      rewrite (subst_extend_open rho z v t1 Hrho (reducible_lc T1 v Hv) Hzfv) in H0.
      exact H0.
  -
    (* application *)
    specialize (IHHty1 rho Hrho Henv).
    specialize (IHHty2 rho Hrho Henv).
    simpl in IHHty1. destruct IHHty1 as [_ [_ [_ Happ]]].
    exact (Happ (subst rho t2) IHHty2).
  - apply reducible_true.
  - apply reducible_false.
  - apply reducible_zero.
  - exact (reducible_succ (subst rho n) (IHHty rho Hrho Henv)).
  - exact (reducible_natrec T (subst rho n) (subst rho b) (subst rho s)
      (IHHty1 rho Hrho Henv) (IHHty2 rho Hrho Henv) (IHHty3 rho Hrho Henv)).
  - apply reducible_choice; [apply IHHty1|apply IHHty2]; assumption.
Qed.

Lemma subst_identity : forall t, subst (fun x => tm_fvar x) t = t.
Proof. induction t; simpl; f_equal; eauto. Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  assert (Henv : forall x U, empty x = Some U -> reducible U tm_true).
  { intros x U Hlookup; unfold empty in Hlookup; discriminate. }
  pose proof (fundamental empty t T Hty (fun _ => tm_true)
    (fun _ => lc_true 0) Henv) as Hred.
  assert (Hfv : forall x, In x (fv t) -> False).
  { intros x Hx. destruct (typing_fv empty t T Hty x Hx) as [U HU].
    unfold empty in HU; discriminate. }
  assert (Hsub : subst (fun _ => tm_true) t = subst (fun x => tm_fvar x) t).
  { apply subst_ext_fv; intros x Hx; exfalso; eapply Hfv; eauto. }
  rewrite Hsub, subst_identity in Hred.
  apply reducible_sn with (T:=T); exact Hred.
Qed.

End STLCNormalizationNondeterminismRecursionHardTask.
