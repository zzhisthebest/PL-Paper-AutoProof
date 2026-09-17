(** STLC CBV strong-normalization benchmark, Hard variant.
    Features: nondeterminism-recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Relations.Relation_Definitions Lia Program.Equality Classical_Prop.
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

Inductive strongly_normalizing : tm -> Prop :=

  | SN_intro : forall t,
      (forall t', t --> t' -> strongly_normalizing t') ->
      strongly_normalizing t.

(* Some elementary locally-nameless infrastructure. *)

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

Lemma lc_weaken : forall k t, lc_at k t -> forall k', k <= k' -> lc_at k' t.
Proof.
  intros k t H; induction H; intros k' Hk.
  - constructor. lia.
  - constructor.
  - constructor; eauto.
  - constructor. apply IHlc_at. lia.
  - constructor.
  - constructor.
  - constructor.
  - constructor. apply IHlc_at. assumption.
  - constructor; eauto.
  - constructor; eauto.
Qed.

Lemma open_rec_lc : forall k t, lc_at k t -> forall j u, k <= j ->
    open_rec j u t = t.
Proof.
  intros k t H; induction H; intros j u Hj; simpl.
  - destruct (Nat.eqb j i) eqn:E; [apply Nat.eqb_eq in E; lia | reflexivity].
  - reflexivity.
  - rewrite IHlc_at1, IHlc_at2; auto.
  - rewrite IHlc_at; auto. lia.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHlc_at; auto.
  - rewrite IHlc_at1, IHlc_at2, IHlc_at3; auto.
  - rewrite IHlc_at1, IHlc_at2; auto.
Qed.

Lemma subst_open_rec : forall rho k u t,
    (forall x, locally_closed (rho x)) ->
    subst rho (open_rec k u t) = open_rec k (subst rho u) (subst rho t).
Proof.
  intros rho k u t Hlc.
  revert k u.
  induction t; intros k u; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - rewrite (open_rec_lc 0 (rho a) (Hlc a) k (subst rho u) (Nat.le_0_l k)). reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
  - rewrite IHt; reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHt; reflexivity.
  - rewrite IHt1, IHt2, IHt3; reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
Qed.

Lemma subst_irrelevant : forall rho rho' t (x : atom),
    (forall y, In y (fv t) -> rho y = rho' y) ->
    subst rho t = subst rho' t.
Proof.
  intros rho rho' t x H.
  induction t; simpl in *; try reflexivity.
  - specialize (H a). exact (H (or_introl eq_refl)).
  - rewrite (IHt1 (fun y Hy => H y (@in_or_app atom (fv t1) (fv t2) y (or_introl Hy)))).
    rewrite (IHt2 (fun y Hy => H y (@in_or_app atom (fv t1) (fv t2) y (or_intror Hy)))). reflexivity.
  - rewrite (IHt (fun y Hy => H y Hy)). reflexivity.
  - rewrite (IHt (fun y Hy => H y Hy)). reflexivity.
  - rewrite (IHt1 (fun y Hy => H y (@in_or_app atom (fv t1) (fv t2 ++ fv t3) y (or_introl Hy)))).
    rewrite (IHt2 (fun y Hy => H y (@in_or_app atom (fv t1) (fv t2 ++ fv t3) y
      (or_intror (@in_or_app atom (fv t2) (fv t3) y (or_introl Hy)))))).
    rewrite (IHt3 (fun y Hy => H y (@in_or_app atom (fv t1) (fv t2 ++ fv t3) y
      (or_intror (@in_or_app atom (fv t2) (fv t3) y (or_intror Hy)))))). reflexivity.
  - rewrite (IHt1 (fun y Hy => H y (@in_or_app atom (fv t1) (fv t2) y (or_introl Hy)))).
    rewrite (IHt2 (fun y Hy => H y (@in_or_app atom (fv t1) (fv t2) y (or_intror Hy)))). reflexivity.
Qed.

Lemma subst_open : forall rho x v t,
    (forall y, locally_closed (rho y)) -> locally_closed v ->
    ~ In x (fv t) ->
    subst (fun y => if Nat.eqb x y then v else rho y) (open t (tm_fvar x)) =
    open (subst rho t) v.
Proof.
  intros rho x v t Hrho Hv Hfresh; unfold open.
  rewrite subst_open_rec; auto.
  assert (Heq : subst (fun y => if Nat.eqb x y then v else rho y) t =
      subst rho t).
  { apply (subst_irrelevant (fun y => if Nat.eqb x y then v else rho y) rho t x).
    intros y Hy. simpl. destruct (Nat.eqb x y) eqn:E.
    - apply Nat.eqb_eq in E; subst y. exfalso; apply Hfresh; exact Hy.
    - reflexivity. }
  rewrite Heq. simpl. rewrite Nat.eqb_refl. reflexivity.
  intros x0. destruct (Nat.eqb x x0); auto.
Qed.

Fixpoint list_max (l : list nat) : nat :=
  match l with [] => 0 | x :: l' => Nat.max x (list_max l') end.

Lemma list_max_bound : forall l z, In z l -> z <= list_max l.
Proof.
  induction l as [|x l IH].
  - simpl; intros z H; contradiction.
  - simpl; intros z H. destruct H as [E|H].
    + subst; apply Nat.le_max_l.
    + apply Nat.le_trans with (m := list_max l); [apply IH; exact H | apply Nat.le_max_r].
Qed.

Lemma fresh_not_in : forall l : list atom, ~ In (S (list_max l)) l.
Proof.
  induction l as [|x l IH]; simpl; auto.
  intro H; destruct H as [H|H].
  - assert (x <= Nat.max x (list_max l)) by apply Nat.le_max_l. lia.
  - pose proof (list_max_bound l _ H) as Hb.
    assert (list_max l <= Nat.max x (list_max l)) by apply Nat.le_max_r. lia.
Qed.

Lemma open_lc_inv : forall k t u,
    lc_at k (open_rec k u t) -> lc_at (S k) t.
Proof.
  intros k t u.
  revert k u.
  induction t; intros k u H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + constructor; apply Nat.eqb_eq in E; lia.
    + inversion H; constructor; apply Nat.eqb_neq in E; lia.
  - constructor.
  - inversion H; constructor; eauto.
  - inversion H; constructor. apply IHt with (k := S k) (u := u). assumption.
  - constructor.
  - constructor.
  - constructor.
  - inversion H; constructor; eauto.
  - inversion H; constructor; eauto.
  - inversion H; constructor; eauto.
Qed.

Lemma typing_lc : forall Gamma t T, <{ Gamma |-- t \in T }> -> locally_closed t.
Proof.
  (* *)
  intros Gamma t T H; induction H using has_type_ind.
  - constructor.
  - unfold locally_closed. apply lc_abs.
    pose proof (fresh_not_in L) as Hfresh.
    specialize (H (S (list_max L)) Hfresh).
    apply (open_lc_inv 0 t1 (tm_fvar (S (list_max L)))).
    unfold locally_closed; apply H0; exact Hfresh.
  - constructor; eauto.
  - constructor.
  - constructor.
  - constructor.
  - constructor; eauto.
  - constructor; eauto.
  - constructor; eauto.
Qed.

Lemma subst_lc_at : forall rho k t,
    lc_at k t -> (forall x, locally_closed (rho x)) ->
    lc_at k (subst rho t).
Proof.
  intros rho k t H; induction H; intros Hrho; simpl.
  - constructor; assumption.
  - apply lc_weaken with (k := 0); [apply Hrho | lia].
  - constructor; eauto.
  - constructor. apply IHlc_at. intros x; apply lc_weaken with (k := 0); [apply Hrho | lia].
  - constructor.
  - constructor.
  - constructor.
  - constructor. eauto.
  - constructor; eauto.
  - constructor; eauto.
Qed.

Lemma open_lc_at : forall k t, lc_at (S k) t -> forall u,
    lc_at k u -> lc_at k (open_rec k u t).
Proof.
  intros k t H u Hu.
  dependent induction H; simpl in *.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E; subst i. exact Hu.
    + apply lc_bvar. apply Nat.eqb_neq in E.
      assert (i <= k) by lia.
      destruct (Nat.eq_dec i k) as [Eq|Eq]; [exfalso; apply E; symmetry; exact Eq | lia].
  - constructor.
  - constructor; eauto.
  - constructor. apply (IHlc_at (S k) eq_refl u).
    exact (lc_weaken k u Hu (S k) (Nat.le_succ_diag_r k)).
  - constructor.
  - constructor.
  - constructor.
  - constructor. eauto.
  - constructor; eauto.
  - constructor; eauto.
Qed.

Lemma numeric_value_lc : forall n, numeric_value n -> locally_closed n.
Proof.
  intros n H; induction H; constructor; auto.
Qed.

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v H; destruct H as [T t Hlc | | | n Hn].
  - exact Hlc.
  - constructor.
  - constructor.
  - exact (numeric_value_lc n Hn).
Qed.

Lemma step_lc : forall t t', t --> t' -> locally_closed t -> locally_closed t'.
Proof.
  intros t t' H; induction H; intros Hlc; unfold locally_closed in *;
    inversion Hlc; subst; unfold open in *;
    eauto using open_lc_at, value_lc, numeric_value_lc.
  all: try apply open_lc_at.
  all: try assumption.
  all: try inversion H4.
  all: try assumption.
  apply lc_app; [apply lc_app | apply lc_rec]; eauto.
  all: inversion H6; assumption.
Qed.

Lemma sn_step : forall t, strongly_normalizing t -> forall t', t --> t' ->
    strongly_normalizing t'.
Proof.
  intros t H; inversion H; eauto.
Qed.

Fixpoint red (T : ty) (t : tm) : Prop :=
  locally_closed t /\ strongly_normalizing t /\
  match T with
  | Ty_Bool => True
  | Ty_Nat => True
  | Ty_Arrow A B => forall v, value v -> red A v -> red B (tm_app t v)
  end.

Lemma red_lc : forall T t, red T t -> locally_closed t.
Proof. intros T t H; destruct T; simpl in H; destruct H as [Hlc [Hsn Hsem]]; exact Hlc. Qed.

Lemma red_sn : forall T t, red T t -> strongly_normalizing t.
Proof. intros T t H; destruct T; simpl in H; destruct H as [Hlc [Hsn Hsem]]; exact Hsn. Qed.

Lemma red_fun : forall A B t v, red (Ty_Arrow A B) t ->
    value v -> red A v -> red B (tm_app t v).
Proof.
  intros A B t v H Hv HvA. simpl in H; destruct H as [Hlc [Hsn Hsem]].
  apply Hsem; assumption.
Qed.

Lemma numeric_no_step : forall n, numeric_value n -> forall n', ~ (n --> n').
Proof.
  intros n H; induction H as [|n H IH]; intros n' Hs.
  - inversion Hs.
  - inversion Hs. eapply IH; eauto.
Qed.

Lemma value_no_step : forall v v', value v -> ~ (v --> v').
Proof.
  intros v v' Hv Hs. destruct Hv as [T t Hlc | | | n Hn].
  - inversion Hs.
  - inversion Hs.
  - inversion Hs.
  - eapply numeric_no_step; eauto.
Qed.

Definition is_app (t : tm) : bool :=
  match t with tm_app _ _ => true | _ => false end.

Lemma value_is_app_false : forall t, value t -> is_app t = false.
Proof.
  intros t H; destruct H as [T b Hlc | | | n Hn]; simpl; try reflexivity.
  induction Hn; simpl; auto.
Qed.

Lemma app_not_value : forall t u, ~ value (tm_app t u).
Proof.
  intros t u H. pose proof (value_is_app_false (tm_app t u) H) as E.
  simpl in E. discriminate.
Qed.

Lemma red_step : forall T t, red T t -> forall t', t --> t' -> red T t'.
Proof.
  intros T; induction T as [| |A IHA B IHB]; intros t H;
    simpl in H; destruct H as [Hlc [Hsn Hsem]]; intros t' Hstep.
  - constructor; [eapply step_lc; eauto |]. constructor; [eapply sn_step; eauto | constructor].
  - constructor; [eapply step_lc; eauto |]. constructor; [eapply sn_step; eauto | constructor].
  - constructor; [eapply step_lc; eauto |]. constructor; [eapply sn_step; eauto |].
    intros v Hv Hvred.
    apply IHB with (t := tm_app t v).
    + apply Hsem; assumption.
    + apply ST_App1; [assumption | apply (red_lc A v); assumption].
Qed.

Lemma red_neutral : forall T t,
    locally_closed t -> ~ value t ->
    (forall t', t --> t' -> red T t') -> red T t.
Proof.
  intros T; induction T as [| |A IHA B IHB]; intros t Hlc Hnv Hall.
  - constructor; [exact Hlc|]. constructor.
    + apply SN_intro. intros t' Hst. apply red_sn with (T := Ty_Bool). apply Hall; assumption.
    + constructor.
  - constructor; [exact Hlc|]. constructor.
    + apply SN_intro. intros t' Hst. apply red_sn with (T := Ty_Nat). apply Hall; assumption.
    + constructor.
  - constructor; [exact Hlc|]. constructor.
    + apply SN_intro. intros t' Hst. apply red_sn with (T := Ty_Arrow A B). apply Hall; assumption.
    + intros v Hv HvA.
      assert (Hlcapp : locally_closed (tm_app t v)).
      { apply lc_app; [exact Hlc | exact (red_lc A v HvA)]. }
      assert (Hnvapp : ~ value (tm_app t v)).
      { apply app_not_value. }
      apply (IHB (tm_app t v) Hlcapp Hnvapp).
      intros z Hz; inversion Hz; subst.
      * exfalso; apply Hnv; apply v_abs; assumption.
      * eapply red_fun; eauto.
      * exfalso; apply Hnv; assumption.
  all: try (exfalso; apply Hnv; apply v_abs; assumption).
  all: try (eapply red_fun; eauto).
Qed.

Lemma red_app_value : forall A B f,
    value f -> red (Ty_Arrow A B) f ->
    forall a, red A a -> red B (tm_app f a).
Proof.
  intros A B f Hfv Hf a Ha.
  pose proof (red_sn A a Ha) as Has.
  induction Has as [a0 Hsteps IH].
  destruct (classic (value a0)) as [Hav|Hnav].
  - apply (red_fun A B f a0); assumption.
  - assert (Hlcapp : locally_closed (tm_app f a0)).
    { apply lc_app; [apply (red_lc (Ty_Arrow A B) f); assumption |
                      apply (red_lc A a0); assumption]. }
    assert (Hnvapp : ~ value (tm_app f a0)).
    { apply app_not_value. }
    apply (red_neutral B (tm_app f a0) Hlcapp Hnvapp).
    intros z Hz; inversion Hz; subst.
    * exfalso; apply Hnav; assumption.
    * exfalso; eapply value_no_step; eauto.
    * apply IH.
      -- exact H3.
      -- apply red_step with (T := A) (t := a0); assumption.
Qed.

Lemma red_app : forall A B f a,
    red (Ty_Arrow A B) f -> red A a -> red B (tm_app f a).
Proof.
  intros A B f a Hf Ha.
  pose proof (red_sn (Ty_Arrow A B) f Hf) as Hfs.
  induction Hfs as [f0 Hsteps IH].
  destruct (classic (value f0)) as [Hfv|Hfnv].
  - apply (red_app_value A B f0); assumption.
  - assert (Hlcapp : locally_closed (tm_app f0 a)).
    { apply lc_app; [apply (red_lc (Ty_Arrow A B) f0); assumption |
                      apply (red_lc A a); assumption]. }
    assert (Hnvapp : ~ value (tm_app f0 a)).
    { apply app_not_value. }
    apply (red_neutral B (tm_app f0 a) Hlcapp Hnvapp).
    intros z Hz; inversion Hz; subst.
    * exfalso; apply Hfnv; apply v_abs; assumption.
    * apply IH.
      -- exact H1.
      -- apply red_step with (T := Ty_Arrow A B) (t := f0); assumption.
    * exfalso; apply Hfnv; assumption.
Qed.

Lemma red_beta : forall B T b v,
    locally_closed (tm_abs T b) -> value v ->
    red B (open b v) ->
    red B (tm_app (tm_abs T b) v).
Proof.
  intros B T b v Habs Hv Hq.
  assert (Hlcapp : locally_closed (tm_app (tm_abs T b) v)).
  { apply lc_app; [exact Habs | apply value_lc; exact Hv]. }
  apply (red_neutral B (tm_app (tm_abs T b) v) Hlcapp).
  { apply app_not_value. }
  intros z Hz; inversion Hz; subst.
  - exact Hq.
  - exfalso; eapply value_no_step; [apply v_abs; exact Habs | eassumption].
  - exfalso; eapply value_no_step; [exact Hv | eassumption].
Qed.

Definition env_ok (Gamma : context) (rho : atom -> tm) : Prop :=
  (forall x, locally_closed (rho x)) /\
  (forall x T, Gamma x = Some T -> red T (rho x)).

Lemma env_ok_update : forall Gamma rho x T v,
    env_ok Gamma rho -> red T v ->
    env_ok (update Gamma x T) (fun y => if Nat.eqb x y then v else rho y).
Proof.
  intros Gamma rho x T v Henv0 Hv. destruct Henv0 as [Hrlc Henv].
  split.
  - intros y; destruct (Nat.eqb x y) eqn:E; [apply red_lc with (T := T); exact Hv | apply Hrlc].
  - intros y U Hy. unfold update in Hy. destruct (Nat.eqb x y) eqn:E.
    + inversion Hy; subst; exact Hv.
    + apply Henv; exact Hy.
Qed.

Lemma red_true : red Ty_Bool tm_true.
Proof. constructor; [constructor |]. constructor; [apply SN_intro; intros; inversion H | constructor]. Qed.

Lemma red_false : red Ty_Bool tm_false.
Proof. constructor; [constructor |]. constructor; [apply SN_intro; intros; inversion H | constructor]. Qed.

Lemma red_zero : red Ty_Nat tm_zero.
Proof. constructor; [constructor |]. constructor; [apply SN_intro; intros; inversion H | constructor]. Qed.

Lemma sn_succ : forall n, strongly_normalizing n -> strongly_normalizing (tm_succ n).
Proof.
  intros n H; induction H as [n Hsteps IHsn]; constructor; intros z Hz; inversion Hz; apply IHsn; assumption.
Qed.

Lemma red_succ : forall n, red Ty_Nat n -> red Ty_Nat (tm_succ n).
Proof.
  intros n Hn. constructor; [apply lc_succ; apply (red_lc Ty_Nat n); exact Hn |].
  constructor; [apply sn_succ; apply red_sn with (T := Ty_Nat); exact Hn | constructor].
Qed.

Definition is_rec (t : tm) : bool :=
  match t with tm_natrec _ _ _ => true | _ => false end.

Lemma value_is_rec_false : forall t, value t -> is_rec t = false.
Proof.
  intros t H; destruct H as [T b Hlc | | | n Hn]; simpl; try reflexivity.
  induction Hn; simpl; auto.
Qed.

Lemma rec_not_value : forall n b s, ~ value (tm_natrec n b s).
Proof.
  intros n b s H. pose proof (value_is_rec_false (tm_natrec n b s) H) as E.
  simpl in E. discriminate.
Qed.

Lemma red_numeric : forall n, numeric_value n -> red Ty_Nat n.
Proof.
  intros n H; induction H; [exact red_zero | apply red_succ; exact IHnumeric_value].
Qed.

Lemma red_rec_numeric : forall n, numeric_value n -> forall b s T,
    red T b -> red (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
    red T (tm_natrec n b s).
Proof.
  intros n Hn; induction Hn as [|n Hn IHn]; intros b s T Hb Hs.
  - revert s Hs.
    induction (red_sn T b Hb) as [b Hbstep IHb]; intros s Hs.
    induction (red_sn (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s Hs) as [s Hsstep IHs].
    assert (Hlc : locally_closed (tm_natrec tm_zero b s)).
    { apply lc_rec; [constructor | apply red_lc with (T := T); exact Hb |
                       apply red_lc with (T := Ty_Arrow Ty_Nat (Ty_Arrow T T)); exact Hs]. }
    apply (red_neutral T (tm_natrec tm_zero b s) Hlc); [apply rec_not_value |].
    intros z Hz; inversion Hz; subst.
    * exfalso; eapply numeric_no_step; [exact nv_zero | exact H2].
    * apply IHb.
      -- assumption.
      -- exact (red_step T b Hb b' H4).
      -- exact Hs.
    * apply IHs.
      -- assumption.
      -- exact (red_step (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s Hs s' H5).
    * exact Hb.
  - revert s Hs.
    induction (red_sn T b Hb) as [b Hbstep IHb]; intros s Hs.
    induction (red_sn (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s Hs) as [s Hsstep IHs].
    assert (Hlc : locally_closed (tm_natrec (tm_succ n) b s)).
    { apply lc_rec; [apply lc_succ; apply numeric_value_lc; exact Hn |
                       apply red_lc with (T := T); exact Hb |
                       apply red_lc with (T := Ty_Arrow Ty_Nat (Ty_Arrow T T)); exact Hs]. }
    apply (red_neutral T (tm_natrec (tm_succ n) b s) Hlc); [apply rec_not_value |].
    intros z Hz; inversion Hz; subst.
    * exfalso; eapply numeric_no_step; [apply nv_succ; exact Hn | exact H2].
    * apply IHb.
      -- assumption.
      -- exact (red_step T b Hb b' H4).
      -- exact Hs.
    * apply IHs.
      -- assumption.
      -- exact (red_step (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s Hs s' H5).
    * apply (red_app T T (tm_app s n) (tm_natrec n b s)).
      -- apply (red_app Ty_Nat (Ty_Arrow T T) s n); [exact Hs | apply red_numeric; exact Hn].
      -- apply IHn; assumption.
Qed.

Definition is_choice (t : tm) : bool :=
  match t with tm_choice _ _ => true | _ => false end.

Lemma value_is_choice_false : forall t, value t -> is_choice t = false.
Proof.
  intros t H; destruct H as [T b Hlc | | | n Hn]; simpl; try reflexivity.
  induction Hn; simpl; auto.
Qed.

Lemma choice_not_value : forall t u, ~ value (tm_choice t u).
Proof.
  intros t u H. pose proof (value_is_choice_false (tm_choice t u) H) as E.
  simpl in E. discriminate.
Qed.

Lemma red_choice : forall T t1 t2, red T t1 -> red T t2 -> red T (tm_choice t1 t2).
Proof.
  intros T t1 t2 H1 H2.
  assert (Hlc : locally_closed (tm_choice t1 t2)).
  { apply lc_choice; [apply red_lc with (T := T); exact H1 | apply red_lc with (T := T); exact H2]. }
  apply (red_neutral T (tm_choice t1 t2) Hlc); [apply choice_not_value |].
  intros z Hz; inversion Hz; subst; assumption.
Qed.

Lemma fundamental : forall Gamma t T,
    <{ Gamma |-- t \in T }> -> forall rho, env_ok Gamma rho ->
    red T (subst rho t).
Proof.
  intros Gamma t T H; induction H using has_type_ind;
    intros rho Henv.
  - unfold env_ok in Henv. destruct Henv as [Hrlc Henv].
    apply Henv with (x := x); assumption.
  - unfold env_ok in Henv. destruct Henv as [Hrlc Henv].
    assert (Habs : locally_closed (tm_abs T1 (subst rho t1))).
    { apply lc_abs.
      apply subst_lc_at with (rho := rho) (k := 1).
      - pose proof (typing_lc Gamma (tm_abs T1 t1) (Ty_Arrow T1 T2)
          (T_Abs L Gamma T1 T2 t1 H)) as Hl.
        inversion Hl; assumption.
      - exact Hrlc. }
    constructor; [exact Habs |]. constructor.
    + apply SN_intro; intros z Hz; inversion Hz.
    + intros v Hv HvA.
      pose (x := S (list_max (L ++ fv t1))).
      assert (HxL : ~ In x L).
      { unfold x; intro Hi; apply (fresh_not_in (L ++ fv t1)); apply in_or_app; left; exact Hi. }
      assert (HxF : ~ In x (fv t1)).
      { unfold x; intro Hi; apply (fresh_not_in (L ++ fv t1)); apply in_or_app; right; exact Hi. }
      specialize (H x HxL).
      assert (Henv' : env_ok (update Gamma x T1) (fun y => if Nat.eqb x y then v else rho y)).
      { apply env_ok_update; [split; assumption | exact HvA]. }
      pose proof (H0 x HxL (fun y => if Nat.eqb x y then v else rho y) Henv') as Hbody.
      rewrite (subst_open rho x v t1 Hrlc (red_lc T1 v HvA) HxF) in Hbody.
      apply (red_beta T2 T1 (subst rho t1) v); assumption.
  - apply (red_app T1 T2 (subst rho t1) (subst rho t2)).
    + apply IHhas_type1; assumption.
    + apply IHhas_type2; assumption.
  - exact red_true.
  - exact red_false.
  - exact red_zero.
  - apply red_succ; apply IHhas_type; assumption.
  - apply red_rec_numeric.
    + apply IHhas_type1; assumption.
    + apply IHhas_type2; assumption.
    + apply IHhas_type3; assumption.
  - apply red_choice; [apply IHhas_type1 | apply IHhas_type2]; assumption.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  (* The proof is below. *)
Qed.

End STLCNormalizationNondeterminismRecursionHardTask.
