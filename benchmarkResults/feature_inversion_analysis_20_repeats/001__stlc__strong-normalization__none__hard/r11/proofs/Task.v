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

(* ================================================================== *)
(** * Auxiliary development for the strong normalization proof        *)
(* ================================================================== *)

(** ** Fresh atoms *)

Fixpoint max_list (L : list atom) : atom :=
  match L with
  | nil => 0
  | x :: L' => Nat.max x (max_list L')
  end.

Lemma max_list_spec : forall (L : list atom) (x : atom),
  In x L -> x <= max_list L.
Proof.
  induction L as [| a L' IH]; intros x Hin.
  - destruct Hin.
  - destruct Hin as [-> | Hin].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; exact Hin | apply Nat.le_max_r].
Qed.

Definition fresh (L : list atom) : atom := S (max_list L).

Lemma fresh_notin : forall L : list atom, ~ In (fresh L) L.
Proof.
  intros L Hin. unfold fresh in Hin.
  pose proof (max_list_spec L _ Hin). lia.
Qed.

Lemma fresh_notin_left : forall L1 L2 : list atom,
  ~ In (fresh (L1 ++ L2)) L1.
Proof.
  intros L1 L2 Hin. apply fresh_notin with (L := L1 ++ L2).
  rewrite in_app_iff. left. exact Hin.
Qed.

Lemma fresh_notin_right : forall L1 L2 : list atom,
  ~ In (fresh (L1 ++ L2)) L2.
Proof.
  intros L1 L2 Hin. apply fresh_notin with (L := L1 ++ L2).
  rewrite in_app_iff. right. exact Hin.
Qed.

(** ** Free variables of a term *)

Fixpoint fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ => nil
  | tm_fvar x => x :: nil
  | tm_app t1 t2 => fv t1 ++ fv t2
  | tm_abs _ t1 => fv t1
  | tm_true => nil
  | tm_false => nil
  end.

Lemma fv_app_notin_1 : forall (x : atom) t1 t2,
  ~ In x (fv (tm_app t1 t2)) -> ~ In x (fv t1).
Proof.
  intros x t1 t2 H Hin. apply H.
  simpl. rewrite in_app_iff. left. exact Hin.
Qed.

Lemma fv_app_notin_2 : forall (x : atom) t1 t2,
  ~ In x (fv (tm_app t1 t2)) -> ~ In x (fv t2).
Proof.
  intros x t1 t2 H Hin. apply H.
  simpl. rewrite in_app_iff. right. exact Hin.
Qed.

(** ** Basic properties of local closure *)

Lemma lc_at_mono : forall k t, lc_at k t -> forall k', k <= k' -> lc_at k' t.
Proof.
  intros k t H.
  induction H as [k i Hi | k x | k t1 t2 H1 IH1 H2 IH2 | k T t1 H1 IH1 | k | k];
    intros k' Hle.
  - constructor. lia.
  - constructor.
  - constructor; [apply IH1 | apply IH2]; exact Hle.
  - constructor. apply IH1. lia.
  - constructor.
  - constructor.
Qed.

Lemma open_lc : forall k t, lc_at k t -> forall u, open_rec k u t = t.
Proof.
  intros k t H.
  induction H as [k i Hi | k x | k t1 t2 H1 IH1 H2 IH2 | k T t1 H1 IH1 | k | k];
    intros u; simpl.
  - assert (E : Nat.eqb k i = false) by (apply Nat.eqb_neq; lia).
    rewrite E. reflexivity.
  - reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH1. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma lc_open : forall t k, lc_at (S k) t ->
  forall u, lc_at k u -> lc_at k (open_rec k u t).
Proof.
  intro t. induction t as [n | y | t1 IH1 t2 IH2 | T0 t1 IH1 | | ];
    intros k Hlc u Hu; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. exact Hu.
    + apply Nat.eqb_neq in E. constructor. inversion Hlc; subst. lia.
  - constructor.
  - inversion Hlc as [| | kk a b H1 H2 | | |]; subst.
    constructor.
    + eapply IH1; [exact H1 | exact Hu].
    + eapply IH2; [exact H2 | exact Hu].
  - inversion Hlc as [| | | kk T1 a H1 | |]; subst. constructor.
    eapply IH1. exact H1. eapply lc_at_mono; [exact Hu | lia].
  - constructor.
  - constructor.
Qed.

Lemma lc_open_fvar_inv : forall t k x,
  lc_at k (open_rec k (tm_fvar x) t) -> lc_at (S k) t.
Proof.
  intro t. induction t as [n | y | t1 IH1 t2 IH2 | T0 t1 IH1 | | ];
    intros k x H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. constructor. lia.
    + apply Nat.eqb_neq in E. constructor. inversion H; lia.
  - constructor.
  - inversion H as [| | kk a b H1 H2 | | |]; subst.
    constructor.
    + eapply IH1; exact H1.
    + eapply IH2; exact H2.
  - inversion H as [| | | kk T1 a H1 | |]; subst. constructor.
    eapply IH1. exact H1.
  - constructor.
  - constructor.
Qed.

(** ** Substitution of free variables *)

Fixpoint tsubst (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_app t1 t2 => tm_app (tsubst sigma t1) (tsubst sigma t2)
  | tm_abs T t1 => tm_abs T (tsubst sigma t1)
  | tm_true => tm_true
  | tm_false => tm_false
  end.

Definition extend (x : atom) (u : tm) (sigma : atom -> tm) : atom -> tm :=
  fun y => if Nat.eqb x y then u else sigma y.

Lemma tsubst_id : forall t, tsubst (fun x => tm_fvar x) t = t.
Proof.
  induction t as [n | y | t1 IH1 t2 IH2 | T0 t1 IH1 | | ]; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH1. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma tsubst_lc : forall t k sigma,
  lc_at k t ->
  (forall x, locally_closed (sigma x)) ->
  lc_at k (tsubst sigma t).
Proof.
  intro t. induction t as [n | y | t1 IH1 t2 IH2 | T0 t1 IH1 | | ];
    intros k sigma Hlc Hsig; simpl.
  - inversion Hlc as [k' i Hi | | | | |]; subst. constructor. exact Hi.
  - apply lc_at_mono with (k := 0); [apply Hsig | lia].
  - inversion Hlc as [| | kk a b H1 H2 | | |]; subst.
    constructor.
    + eapply IH1; [exact H1 | exact Hsig].
    + eapply IH2; [exact H2 | exact Hsig].
  - inversion Hlc as [| | | kk T1 a H1 | |]; subst. constructor.
    eapply IH1. exact H1. exact Hsig.
  - constructor.
  - constructor.
Qed.

Lemma tsubst_open_gen : forall t k x u sigma,
  ~ In x (fv t) ->
  (forall y, locally_closed (sigma y)) ->
  tsubst (extend x u sigma) (open_rec k (tm_fvar x) t)
    = open_rec k u (tsubst sigma t).
Proof.
  intro t. induction t as [n | y | t1 IH1 t2 IH2 | T0 t1 IH1 | | ];
    intros k x u sigma Hfresh Hsig; simpl.
  - (* bvar *) destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. simpl. unfold extend.
      rewrite Nat.eqb_refl. reflexivity.
    + apply Nat.eqb_neq in E. reflexivity.
  - (* fvar *)
    assert (Hxy : x <> y).
    { intro Hxy'. apply Hfresh. subst y. simpl. auto. }
    assert (Ey : Nat.eqb x y = false) by (apply Nat.eqb_neq; exact Hxy).
    unfold extend. rewrite Ey.
    symmetry. apply open_lc.
    apply lc_at_mono with (k := 0); [apply Hsig | lia].
  - (* app *) simpl.
    rewrite (IH1 k x u sigma).
    + rewrite (IH2 k x u sigma).
      * reflexivity.
      * apply fv_app_notin_2 with (t1 := t1). exact Hfresh.
      * exact Hsig.
    + apply fv_app_notin_1 with (t2 := t2). exact Hfresh.
    + exact Hsig.
  - (* abs *) simpl.
    rewrite (IH1 (S k) x u sigma).
    + reflexivity.
    + simpl in Hfresh. exact Hfresh.
    + exact Hsig.
  - reflexivity.
  - reflexivity.
Qed.

Lemma tsubst_open : forall t x u sigma,
  ~ In x (fv t) ->
  (forall y, locally_closed (sigma y)) ->
  tsubst (extend x u sigma) (open t (tm_fvar x)) = open (tsubst sigma t) u.
Proof.
  intros. unfold open. apply tsubst_open_gen; assumption.
Qed.

(** ** Values and steps *)

Lemma value_no_step : forall t, value t -> forall t', t --> t' -> False.
Proof.
  intros t Hv. induction Hv; intros t' Hstep; inversion Hstep.
Qed.

Lemma value_lc : forall t, value t -> locally_closed t.
Proof.
  intros t Hv. destruct Hv as [T body Hlc | |].
  - exact Hlc.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma SN_value : forall t, value t -> strongly_normalizing t.
Proof.
  intros t Hv. apply SN_intro. intros t' Hstep.
  exfalso. eapply value_no_step; eassumption.
Qed.

Lemma value_multi_eq : forall t t', multi step t t' -> value t -> t' = t.
Proof.
  intros t t' Hm. induction Hm as [| a b c Hstep Hrest IH]; intro Hv.
  - reflexivity.
  - exfalso. eapply value_no_step; eassumption.
Qed.

Lemma step_preserves_lc : forall t t', t --> t' ->
  locally_closed t -> locally_closed t'.
Proof.
  intros t t' Hstep.
  induction Hstep as [T0 body v0 Hlcabs Hv0 | t1 t1' t2 Hst1 IH Hlc2 | v1 t2 t2' Hval Hst2 IH];
    intros Hlc.
  - (* ST_AppAbs *) simpl in Hlc.
    inversion Hlc as [| | k a b H1 H2 | | |]; subst.
    simpl. apply lc_open.
    + inversion Hlcabs as [| | | k0 T1 body' Hbody | |]; subst. exact Hbody.
    + exact H2.
  - (* ST_App1 *) simpl in Hlc.
    inversion Hlc as [| | k a b H1 H2 | | |]; subst.
    simpl. constructor.
    + apply IH. exact H1.
    + exact H2.
  - (* ST_App2 *) simpl in Hlc.
    inversion Hlc as [| | k a b H1 H2 | | |]; subst.
    simpl. constructor.
    + exact H1.
    + apply IH. exact H2.
Qed.

Lemma multi_preserves_lc : forall t t', multi step t t' ->
  locally_closed t -> locally_closed t'.
Proof.
  intros t t' Hm. induction Hm as [| a b c Hstep Hrest IH]; intro Hlc.
  - exact Hlc.
  - apply IH. eapply step_preserves_lc; eassumption.
Qed.

Lemma SN_step : forall t t', strongly_normalizing t -> t --> t' ->
  strongly_normalizing t'.
Proof.
  intros t t' Hsn Hstep. inversion Hsn as [t0 Hred]. subst.
  apply Hred. exact Hstep.
Qed.

Lemma SN_multi : forall t t', strongly_normalizing t -> multi step t t' ->
  strongly_normalizing t'.
Proof.
  intros t t' Hsn Hm. revert Hsn.
  induction Hm as [| a b c Hstep Hrest IH]; intro Hsn.
  - exact Hsn.
  - apply IH. eapply SN_step; eassumption.
Qed.

Lemma multi_trans : forall t1 t2 t3 : tm,
  multi step t1 t2 -> multi step t2 t3 -> multi step t1 t3.
Proof.
  intros t1 t2 t3 H12 H23. revert t3 H23.
  induction H12 as [| a b c Hstep Hrest IH]; intros t3 H23.
  - exact H23.
  - eapply multi_step; [exact Hstep | apply IH; exact H23].
Qed.

(** ** The logical relation *)

Fixpoint R (T : ty) (t : tm) : Prop :=
  locally_closed t /\
  strongly_normalizing t /\
  match T with
  | Ty_Bool =>
      forall v, multi step t v -> value v -> (v = tm_true \/ v = tm_false)
  | Ty_Arrow T1 T2 =>
      forall v, multi step t v -> value v ->
        (forall w, value w -> R T1 w -> R T2 (tm_app v w))
  end.

Lemma R_lc : forall T t, R T t -> locally_closed t.
Proof.
  intros T t H. destruct T; simpl in H; tauto.
Qed.

Lemma R_sn : forall T t, R T t -> strongly_normalizing t.
Proof.
  intros T t H. destruct T; simpl in H; tauto.
Qed.

Lemma R_multi : forall T t t', R T t -> multi step t t' -> R T t'.
Proof.
  intros T t t' HR Hm. destruct T as [| T1 T2]; simpl in *.
  - destruct HR as [Hlc [Hsn Hcl]]. split.
    + eapply multi_preserves_lc; eassumption.
    + split.
      * eapply SN_multi; eassumption.
      * intros v Hmv Hval. eapply Hcl; [| exact Hval].
        eapply multi_trans; eassumption.
  - destruct HR as [Hlc [Hsn Hcl]]. split.
    + eapply multi_preserves_lc; eassumption.
    + split.
      * eapply SN_multi; eassumption.
      * intros v Hmv Hval w Hwval HRw. eapply Hcl; [| exact Hval | exact Hwval | exact HRw].
        eapply multi_trans; eassumption.
Qed.

(** ** Decomposition of reduction sequences of an application *)

Lemma value_app_absurd : forall t1 t2, value (tm_app t1 t2) -> False.
Proof. intros t1 t2 H. inversion H. Qed.

Lemma app_multi_value_inv : forall (a c : tm),
  multi step a c -> value c ->
  forall (u v : tm), a = tm_app u v ->
  exists (T : ty) (body v' : tm),
    multi step u (tm_abs T body) /\
    multi step v v' /\ value v' /\ multi step (open body v') c.
Proof.
  intros a c Hm. induction Hm as [a0 | x y z Hstep Hrest IH];
    intros Hval u v E.
  - subst a0. exfalso. eapply value_app_absurd; eassumption.
  - subst x.
    inversion Hstep as [T0 body0 w Hlcabs Hvw | t1 t1' t2 Hst1 Hlc2 | v1 t2 t2' Hval1 Hst2];
      subst.
    + (* beta step *) exists T0, body0, v. split.
      * apply multi_refl.
      * split.
        -- apply multi_refl.
        -- split; [exact Hvw | exact Hrest].
    + (* reduce the function *) destruct (IH Hval t1' v eq_refl) as
        (T & body & v' & Hmu & Hmv & Hvv' & Hmz).
      exists T, body, v'. split.
      * eapply multi_step; eassumption.
      * split; [exact Hmv | split; [exact Hvv' | exact Hmz]].
    + (* reduce the argument *) destruct (IH Hval u t2' eq_refl) as
        (T & body & v' & Hmu & Hmv & Hvv' & Hmz).
      exists T, body, v'. split.
      * exact Hmu.
      * split.
        -- eapply multi_step; eassumption.
        -- split; [exact Hvv' | exact Hmz].
Qed.

(** ** Strong normalization of applications *)

Lemma sn_app_value : forall (v : tm), strongly_normalizing v ->
  forall (u : tm), value u -> locally_closed v ->
  (forall (T : ty) (body v' : tm),
      multi step u (tm_abs T body) -> multi step v v' -> value v' ->
      strongly_normalizing (open body v')) ->
  strongly_normalizing (tm_app u v).
Proof.
  intros v Hsn. induction Hsn as [v Hredv IH].
  intros u Huval Hlcv Hcompat.
  apply SN_intro. intros t' Hstep.
  inversion Hstep as [T0 body0 w Hlcabs Hvw | t1 t1' t2 Hst1 Hlc2 | v1 t2 t2' Hval1 Hst2];
    subst.
  - eapply Hcompat; [apply multi_refl | apply multi_refl | exact Hvw].
  - exfalso. eapply value_no_step; eassumption.
  - eapply IH.
    + exact Hst2.
    + exact Huval.
    + eapply step_preserves_lc; eassumption.
    + intros T body v' Hmu Hmv Hvv'. eapply Hcompat; [exact Hmu | | exact Hvv'].
      eapply multi_step; eassumption.
Qed.

Lemma sn_app : forall (u : tm), locally_closed u -> strongly_normalizing u ->
  forall (v : tm), locally_closed v -> strongly_normalizing v ->
  (forall (T : ty) (body v' : tm),
      multi step u (tm_abs T body) -> multi step v v' -> value v' ->
      strongly_normalizing (open body v')) ->
  strongly_normalizing (tm_app u v).
Proof.
  intros u Hlcu Hsn. induction Hsn as [u Hredu IH].
  intros v Hlcv Hsnv Hcompat.
  apply SN_intro. intros t' Hstep.
  inversion Hstep as [T0 body0 w Hlcabs Hvw | t1 t1' t2 Hst1 Hlc2 | v1 t2 t2' Hval1 Hst2];
    subst.
  - eapply Hcompat; [apply multi_refl | apply multi_refl | exact Hvw].
  - eapply IH.
    + exact Hst1.
    + eapply step_preserves_lc; eassumption.
    + exact Hlcv.
    + exact Hsnv.
    + intros T body v' Hmu Hmv Hvv'. eapply Hcompat; [| exact Hmv | exact Hvv'].
      eapply multi_step; eassumption.
  - eapply sn_app_value.
    + eapply SN_step; eassumption.
    + exact Hval1.
    + eapply step_preserves_lc; eassumption.
    + intros T body v' Hmu Hmv Hvv'. eapply Hcompat; [exact Hmu | | exact Hvv'].
      eapply multi_step; eassumption.
Qed.

Lemma R_app : forall (T1 T2 : ty) (u v : tm),
  R (Ty_Arrow T1 T2) u -> R T1 v -> R T2 (tm_app u v).
Proof.
  intros T1 T2 u v Hu Hv.
  simpl in Hu. destruct Hu as [Hlcu [HSnu Hclu]].
  assert (Hlcv : locally_closed v) by (eapply R_lc; eassumption).
  assert (HSnv : strongly_normalizing v) by (eapply R_sn; eassumption).
  assert (Hlcapp : locally_closed (tm_app u v)) by (constructor; assumption).
  assert (Hsnapp : strongly_normalizing (tm_app u v)).
  { eapply sn_app; [exact Hlcu | exact HSnu | exact Hlcv | exact HSnv |].
    intros T body v' Hmu Hmv Hvv'.
    assert (Hlcabs : locally_closed (tm_abs T body)).
    { eapply multi_preserves_lc; [exact Hmu | exact Hlcu]. }
    assert (Hvala : value (tm_abs T body)) by (apply v_abs; exact Hlcabs).
    assert (HRv' : R T1 v') by (eapply R_multi; eassumption).
    assert (HRapp : R T2 (tm_app (tm_abs T body) v'))
      by (eapply Hclu; [exact Hmu | exact Hvala | exact Hvv' | exact HRv']).
    eapply SN_step; [eapply R_sn; exact HRapp |].
    apply ST_AppAbs; assumption. }
  destruct T2 as [| T2a T2b].
  - (* result type Bool *) simpl. split; [exact Hlcapp | split; [exact Hsnapp |]].
    intros z Hmz Hvalz.
    destruct (app_multi_value_inv _ _ Hmz Hvalz u v eq_refl)
      as (T & body & v' & Hmu & Hmv & Hvv' & Hmz').
    assert (Hlcabs : locally_closed (tm_abs T body)).
    { eapply multi_preserves_lc; [exact Hmu | exact Hlcu]. }
    assert (Hvala : value (tm_abs T body)) by (apply v_abs; exact Hlcabs).
    assert (HRv' : R T1 v') by (eapply R_multi; eassumption).
    assert (HRapp : R Ty_Bool (tm_app (tm_abs T body) v'))
      by (eapply Hclu; [exact Hmu | exact Hvala | exact Hvv' | exact HRv']).
    simpl in HRapp. destruct HRapp as [HlcB [HsnB HclB]].
    eapply HclB; [| exact Hvalz].
    eapply multi_step; [apply ST_AppAbs; assumption | exact Hmz'].
  - (* result type arrow *) simpl. split; [exact Hlcapp | split; [exact Hsnapp |]].
    intros z Hmz Hvalz y Hvy HRy.
    destruct (app_multi_value_inv _ _ Hmz Hvalz u v eq_refl)
      as (T & body & v' & Hmu & Hmv & Hvv' & Hmz').
    assert (Hlcabs : locally_closed (tm_abs T body)).
    { eapply multi_preserves_lc; [exact Hmu | exact Hlcu]. }
    assert (Hvala : value (tm_abs T body)) by (apply v_abs; exact Hlcabs).
    assert (HRv' : R T1 v') by (eapply R_multi; eassumption).
    assert (HRapp : R (Ty_Arrow T2a T2b) (tm_app (tm_abs T body) v'))
      by (eapply Hclu; [exact Hmu | exact Hvala | exact Hvv' | exact HRv']).
    simpl in HRapp. destruct HRapp as [HlcB [HsnB HclB]].
    eapply HclB; [| exact Hvalz | exact Hvy | exact HRy].
    eapply multi_step; [apply ST_AppAbs; assumption | exact Hmz'].
Qed.

(** ** Interpretation of typing contexts *)

Definition env_rel (Gamma : context) (sigma : atom -> tm) : Prop :=
  (forall x, locally_closed (sigma x)) /\
  (forall (x : atom) (T : ty), Gamma x = Some T -> R T (sigma x)).

Lemma has_type_lc : forall (Gamma : context) (t : tm) (T : ty),
  has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T H.
  induction H as [Gamma0 x T0 Hlookup
    | L Gamma0 T1 T2 t1 Hprem IH
    | Gamma0 t1 t2 T1 T2 Ht1 IH1 Ht2 IH2
    | Gamma0 | Gamma0].
  - apply lc_fvar.
  - apply lc_abs.
    pose proof (IH (fresh (L ++ fv t1)) (fresh_notin_left L (fv t1))) as H0.
    apply lc_open_fvar_inv with (x := fresh (L ++ fv t1)). exact H0.
  - apply lc_app; assumption.
  - apply lc_true.
  - apply lc_false.
Qed.

(** ** Fundamental theorem *)

Lemma fundamental : forall (Gamma : context) (t : tm) (T : ty),
  has_type Gamma t T ->
  forall sigma, env_rel Gamma sigma -> R T (tsubst sigma t).
Proof.
  intros Gamma t T H.
  induction H as [Gamma0 x T0 Hlookup
    | L Gamma0 T1 T2 t1 Hprem IH
    | Gamma0 t1 t2 T1 T2 Ht1 IH1 Ht2 IH2
    | Gamma0 | Gamma0];
    intros sigma [Hlcsig Hsem].
  - (* T_Var *) simpl. apply Hsem. exact Hlookup.
  - (* T_Abs *)
    simpl.
    assert (Hlc1 : lc_at 1 t1).
    { pose proof (has_type_lc _ _ _
        (Hprem (fresh (L ++ fv t1)) (fresh_notin_left L (fv t1)))) as H0.
      apply lc_open_fvar_inv with (x := fresh (L ++ fv t1)). exact H0. }
    assert (Hlcbody : lc_at 1 (tsubst sigma t1))
      by (eapply tsubst_lc; [exact Hlc1 | exact Hlcsig]).
    assert (Hlcabs : locally_closed (tm_abs T1 (tsubst sigma t1)))
      by (apply lc_abs; exact Hlcbody).
    assert (Hvalabs : value (tm_abs T1 (tsubst sigma t1)))
      by (apply v_abs; exact Hlcabs).
    split.
    + exact Hlcabs.
    + split.
      * apply SN_value. exact Hvalabs.
      * intros v Hmv Hvv w Hwval HRw.
        assert (Hveq : v = tm_abs T1 (tsubst sigma t1))
          by (eapply value_multi_eq; [exact Hmv | exact Hvalabs]).
        subst v.
        (* the body, opened with the argument w, is reducible *)
        assert (Hxfv : ~ In (fresh (L ++ fv t1)) (fv t1))
          by (apply fresh_notin_right).
        assert (HxL : ~ In (fresh (L ++ fv t1)) L)
          by (apply fresh_notin_left).
        pose (sigmay := extend (fresh (L ++ fv t1)) w sigma).
        assert (Henv : env_rel (update Gamma0 (fresh (L ++ fv t1)) T1) sigmay).
        { split.
          - intros y. unfold sigmay, extend.
            destruct (Nat.eqb (fresh (L ++ fv t1)) y).
            + apply value_lc. exact Hwval.
            + apply Hlcsig.
          - intros y S Hy. unfold sigmay, extend.
            unfold update in Hy.
            destruct (Nat.eqb (fresh (L ++ fv t1)) y) eqn:Ey.
            + injection Hy as HS. subst S. exact HRw.
            + apply Hsem. exact Hy. }
        pose proof (IH (fresh (L ++ fv t1)) HxL sigmay Henv) as HRbody.
        assert (Heq : tsubst sigmay (open t1 (tm_fvar (fresh (L ++ fv t1))))
                    = open (tsubst sigma t1) w).
        { unfold sigmay. eapply tsubst_open.
          - exact Hxfv.
          - exact Hlcsig. }
        rewrite Heq in HRbody.
        (* the application of the abstraction to w *)
        assert (Hlcw : locally_closed w) by (apply value_lc; exact Hwval).
        assert (Hlcapp2 : locally_closed
          (tm_app (tm_abs T1 (tsubst sigma t1)) w)) by (constructor; assumption).
        assert (Hsnapp2 : strongly_normalizing
          (tm_app (tm_abs T1 (tsubst sigma t1)) w)).
        { eapply sn_app_value.
          - apply SN_value. exact Hwval.
          - exact Hvalabs.
          - exact Hlcw.
          - intros T0 body0 v0 Hmu1 Hmv1 Hvv1.
            assert (Habs : tm_abs T0 body0 = tm_abs T1 (tsubst sigma t1))
              by (eapply value_multi_eq; [exact Hmu1 | exact Hvalabs]).
            assert (Hv0 : v0 = w)
              by (eapply value_multi_eq; [exact Hmv1 | exact Hwval]).
            injection Habs as HT Hb. subst T0 body0. subst v0.
            eapply R_sn. exact HRbody. }
        destruct T2 as [| T2a T2b].
        -- (* codomain Bool *) simpl. split.
           ++ exact Hlcapp2.
           ++ split.
              ** exact Hsnapp2.
              ** intros z Hmz Hvalz.
                 destruct (app_multi_value_inv _ _ Hmz Hvalz
                   (tm_abs T1 (tsubst sigma t1)) w eq_refl)
                   as (T0 & body0 & v0 & Hmu2 & Hmv2 & Hvv2 & Hmz').
                 assert (Habs : tm_abs T0 body0 = tm_abs T1 (tsubst sigma t1))
                   by (eapply value_multi_eq; [exact Hmu2 | exact Hvalabs]).
                 assert (Hv0 : v0 = w)
                   by (eapply value_multi_eq; [exact Hmv2 | exact Hwval]).
                 injection Habs as HT Hb. subst T0 body0. subst v0.
                 simpl in HRbody. destruct HRbody as [HlcB [HsnB HclB]].
                 eapply HclB; [exact Hmz' | exact Hvalz].
        -- (* codomain arrow *) simpl. split.
           ++ exact Hlcapp2.
           ++ split.
              ** exact Hsnapp2.
              ** intros z Hmz Hvalz y Hvy HRy.
                 destruct (app_multi_value_inv _ _ Hmz Hvalz
                   (tm_abs T1 (tsubst sigma t1)) w eq_refl)
                   as (T0 & body0 & v0 & Hmu3 & Hmv3 & Hvv3 & Hmz').
                 assert (Habs : tm_abs T0 body0 = tm_abs T1 (tsubst sigma t1))
                   by (eapply value_multi_eq; [exact Hmu3 | exact Hvalabs]).
                 assert (Hv0 : v0 = w)
                   by (eapply value_multi_eq; [exact Hmv3 | exact Hwval]).
                 injection Habs as HT Hb. subst T0 body0. subst v0.
                 simpl in HRbody. destruct HRbody as [HlcB [HsnB HclB]].
                 eapply HclB; [exact Hmz' | exact Hvalz | exact Hvy | exact HRy].
  - (* T_App *) simpl. eapply R_app.
    + apply IH1. split; assumption.
    + apply IH2. split; assumption.
  - (* T_True *) simpl. split.
    + apply lc_true.
    + split.
      * apply SN_value. apply v_true.
      * intros v Hmv Hval. left. eapply value_multi_eq; [exact Hmv | apply v_true].
  - (* T_False *) simpl. split.
    + apply lc_false.
    + split.
      * apply SN_value. apply v_false.
      * intros v Hmv Hval. right. eapply value_multi_eq; [exact Hmv | apply v_false].
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  assert (Henv : env_rel empty (fun x => tm_fvar x)).
  { split.
    - intros x. apply lc_fvar.
    - intros x T0 Hx. unfold empty in Hx. discriminate Hx. }
  pose proof (fundamental empty t T Hty (fun x => tm_fvar x) Henv) as HR.
  rewrite tsubst_id in HR.
  eapply R_sn. exact HR.
Qed.

End STLCNormalizationNoneHardTask.
