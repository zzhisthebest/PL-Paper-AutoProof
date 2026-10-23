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

(** ============================================================ *)
(** * Auxiliary development for the strong normalization proof.  *)
(** ============================================================ *)

(** Free variables of a term, as a list of atoms. *)

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

(** Simultaneous substitution for all free variables. *)

Fixpoint subst_all (rho : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => rho x
  | tm_app t1 t2 => tm_app (subst_all rho t1) (subst_all rho t2)
  | tm_abs T t1 => tm_abs T (subst_all rho t1)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 =>
      tm_if (subst_all rho t1) (subst_all rho t2) (subst_all rho t3)
  end.

(** Updating a semantic environment at one variable. *)

Definition update_env (rho : atom -> tm) (x : atom) (u : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then u else rho y.

(** The identity environment (interprets each free variable by itself). *)

Definition rho_id : atom -> tm := fun x => tm_fvar x.

Lemma subst_all_id : forall t : tm, subst_all rho_id t = t.
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

(** ** Freshness of atoms *)

Lemma in_fold_max : forall (l : list atom) (x : atom),
    In x l -> x <= fold_right max 0 l.
Proof.
  induction l as [| a l IH]; intros x Hin; simpl in *.
  - destruct Hin.
  - destruct Hin as [-> | Hin].
    + lia.
    + apply IH in Hin. lia.
Qed.

Lemma exists_fresh : forall (l : list atom), exists x : atom, ~ In x l.
Proof.
  intros l. exists (S (fold_right max 0 l)).
  intros Hin. apply in_fold_max in Hin. lia.
Qed.

Lemma exists_fresh_two : forall (l1 l2 : list atom),
    exists x : atom, ~ In x l1 /\ ~ In x l2.
Proof.
  intros l1 l2. destruct (exists_fresh (l1 ++ l2)) as [x Hx].
  exists x. rewrite in_app_iff in Hx. tauto.
Qed.

(** ** Local closure lemmas *)

Lemma lc_at_weaken : forall (t : tm) (k k' : nat),
    lc_at k t -> k <= k' -> lc_at k' t.
Proof.
  induction t as [n | x | t1 IH1 t2 IH2 | T t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
    intros k k' Hlc Hle.
  - (* bvar *) inversion Hlc; subst. constructor. lia.
  - (* fvar *) inversion Hlc; subst. constructor.
  - (* app *) inversion Hlc; subst. constructor.
    + apply IH1 with (k := k); assumption.
    + apply IH2 with (k := k); assumption.
  - (* abs *) inversion Hlc; subst. apply lc_abs.
    apply IH1 with (k := S k); auto. lia.
  - (* true *) inversion Hlc; subst. constructor.
  - (* false *) inversion Hlc; subst. constructor.
  - (* if *) inversion Hlc; subst. constructor;
      [apply IH1 with (k := k) | apply IH2 with (k := k) | apply IH3 with (k := k)];
      assumption.
Qed.

Lemma open_rec_lc : forall (t : tm) (k : nat) (u : tm),
    lc_at (S k) t -> lc_at k u -> lc_at k (open_rec k u t).
Proof.
  induction t as [n | x | t1 IH1 t2 IH2 | T t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
    intros k u Ht Hu; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. exact Hu.
    + apply Nat.eqb_neq in E. constructor. inversion Ht. lia.
  - constructor.
  - inversion Ht; subst. constructor; auto.
  - inversion Ht; subst. apply lc_abs. apply IH1 with (k := S k).
    + assumption.
    + apply lc_at_weaken with (k := k); [assumption | lia].
  - constructor.
  - constructor.
  - inversion Ht; subst. constructor; auto.
Qed.

Lemma open_rec_no_bvar : forall (t : tm) (k : nat),
    lc_at k t -> forall u : tm, open_rec k u t = t.
Proof.
  induction t as [n | x | t1 IH1 t2 IH2 | T t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
    intros k Hlc u; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. inversion Hlc. lia.
    + reflexivity.
  - reflexivity.
  - f_equal; [apply IH1 | apply IH2]; inversion Hlc; subst; assumption.
  - f_equal. apply IH1. inversion Hlc; subst. assumption.
  - reflexivity.
  - reflexivity.
  - f_equal; [apply IH1 | apply IH2 | apply IH3]; inversion Hlc; subst; assumption.
Qed.

Lemma lc0_open_rec : forall (t : tm), locally_closed t ->
    forall (k : nat) (u : tm), open_rec k u t = t.
Proof.
  intros t Hlc k u. apply open_rec_no_bvar.
  apply lc_at_weaken with (k := 0); auto. lia.
Qed.

Lemma lc_open_inv : forall (t : tm) (k : nat) (x : atom),
    lc_at k (open_rec k (tm_fvar x) t) -> lc_at (S k) t.
Proof.
  induction t as [n | y | t1 IH1 t2 IH2 | T t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
    intros k x H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. constructor. lia.
    + apply Nat.eqb_neq in E. inversion H; subst. constructor. lia.
  - constructor.
  - inversion H; subst. constructor.
    + apply IH1 with (x := x). assumption.
    + apply IH2 with (x := x). assumption.
  - inversion H; subst. apply lc_abs. apply IH1 with (x := x). assumption.
  - constructor.
  - constructor.
  - inversion H; subst. constructor.
    + apply IH1 with (x := x). assumption.
    + apply IH2 with (x := x). assumption.
    + apply IH3 with (x := x). assumption.
Qed.

(** ** Step preserves local closure *)

Lemma lc_app_inv : forall (k : nat) (t1 t2 : tm),
    lc_at k (tm_app t1 t2) -> lc_at k t1 /\ lc_at k t2.
Proof. intros k t1 t2 H. inversion H; subst. auto. Qed.

Lemma lc_abs_inv : forall (k : nat) (T : ty) (t : tm),
    lc_at k (tm_abs T t) -> lc_at (S k) t.
Proof. intros k T t H. inversion H; subst. assumption. Qed.

Lemma lc_if_inv : forall (k : nat) (b t2 t3 : tm),
    lc_at k (tm_if b t2 t3) -> lc_at k b /\ lc_at k t2 /\ lc_at k t3.
Proof. intros k b t2 t3 H. inversion H; subst. auto. Qed.

Lemma step_lc : forall (t t' : tm),
    t --> t' -> locally_closed t -> locally_closed t'.
Proof.
  intros t t' H. induction H as
    [ T t0 v Hlcabs Hv
    | t1 t1' t2 Hstep IH Hlc2
    | v1 t2 t2' Hv Hstep IH
    | t1 t2 H1 H2
    | t1 t2 H1 H2
    | t1 t1' t2 t3 Hstep IH H2 H3 ]; intros Hlc.
  - (* ST_AppAbs *)
    destruct (lc_app_inv 0 (tm_abs T t0) v Hlc) as [Hlca Hlcv].
    apply open_rec_lc with (k := 0).
    + exact (lc_abs_inv 0 T t0 Hlca).
    + exact Hlcv.
  - (* ST_App1 *)
    destruct (lc_app_inv 0 t1 t2 Hlc) as [Ha Hb].
    constructor.
    + apply IH. exact Ha.
    + exact Hb.
  - (* ST_App2 *)
    destruct (lc_app_inv 0 v1 t2 Hlc) as [Ha Hb].
    constructor.
    + exact Ha.
    + apply IH. exact Hb.
  - (* ST_IfTrue *)
    destruct (lc_if_inv 0 tm_true t1 t2 Hlc) as [Hb [H1' H2']].
    exact H1'.
  - (* ST_IfFalse *)
    destruct (lc_if_inv 0 tm_false t1 t2 Hlc) as [Hb [H1' H2']].
    exact H2'.
  - (* ST_If *)
    destruct (lc_if_inv 0 t1 t2 t3 Hlc) as [Hb [H2' H3']].
    constructor.
    + apply IH. exact Hb.
    + exact H2'.
    + exact H3'.
Qed.

(** ** Strong normalization basics *)

Lemma SN_step : forall (t t' : tm),
    t --> t' -> strongly_normalizing t -> strongly_normalizing t'.
Proof.
  intros t t' Hstep Hsn. destruct Hsn as [t0 Hreds]. apply Hreds. exact Hstep.
Qed.

Lemma SN_abs : forall (T : ty) (t : tm), strongly_normalizing (tm_abs T t).
Proof.
  intros T t. apply SN_intro. intros t' H. inversion H.
Qed.

Lemma SN_true : strongly_normalizing tm_true.
Proof.
  apply SN_intro. intros t' H. inversion H.
Qed.

Lemma SN_false : strongly_normalizing tm_false.
Proof.
  apply SN_intro. intros t' H. inversion H.
Qed.

(** ** Inversion lemmas for the step relation *)

Lemma not_value_app : forall (t u : tm), ~ value (tm_app t u).
Proof. intros t u H. inversion H. Qed.

Lemma not_value_if : forall (b t2 t3 : tm), ~ value (tm_if b t2 t3).
Proof. intros b t2 t3 H. inversion H. Qed.

Lemma abs_no_step : forall (T : ty) (t t' : tm), ~ (tm_abs T t --> t').
Proof. intros T t t' H. inversion H. Qed.

Lemma step_app_inv : forall (t u w : tm),
    tm_app t u --> w ->
    (exists (T0 : ty) (body : tm),
        t = tm_abs T0 body /\ value u /\ w = open body u) \/
    (exists t' : tm, t --> t' /\ w = tm_app t' u) \/
    (exists u' : tm, value t /\ u --> u' /\ w = tm_app t u').
Proof.
  intros t u w H. inversion H; subst.
  - left. eexists. eexists. split; [reflexivity|]. split; [eassumption|reflexivity].
  - right. left. eexists. split; [eassumption|reflexivity].
  - right. right. eexists. split; [eassumption|]. split; [eassumption|reflexivity].
Qed.

Lemma step_abs_app_inv : forall (T1 : ty) (body u w : tm),
    tm_app (tm_abs T1 body) u --> w ->
    (value u /\ w = open body u) \/
    (exists u' : tm, u --> u' /\ w = tm_app (tm_abs T1 body) u').
Proof.
  intros T1 body u w H. inversion H; subst.
  - left. split; [eassumption|reflexivity].
  - (* ST_App1 case: impossible because abstractions do not step *)
    exfalso. eapply abs_no_step. eassumption.
  - right. eexists. split; [eassumption|reflexivity].
Qed.

Lemma step_if_inv : forall (b t2 t3 s : tm),
    tm_if b t2 t3 --> s ->
    (b = tm_true /\ s = t2) \/
    (b = tm_false /\ s = t3) \/
    (exists b' : tm, b --> b' /\ s = tm_if b' t2 t3).
Proof.
  intros b t2 t3 s H. inversion H; subst.
  - left. split; reflexivity.
  - right. left. split; reflexivity.
  - right. right. eexists. split; [eassumption|reflexivity].
Qed.

(** ============================================================ *)
(** * The logical relation and strong normalization.             *)
(** ============================================================ *)

(** The reducibility relation.  At every type it contains strong
    normalization and local closure; at function types it is closed
    under application to related arguments. *)

Fixpoint R (T : ty) (t : tm) : Prop :=
  match T with
  | Ty_Bool => locally_closed t /\ strongly_normalizing t
  | Ty_Arrow T1 T2 =>
      locally_closed t /\ strongly_normalizing t /\
      (forall u : tm, R T1 u -> R T2 (tm_app t u))
  end.

(** Semantic typing of environments: every variable is mapped to a
    locally closed term of the appropriate semantic type. *)

Definition env_sem (Gamma : context) (rho : atom -> tm) : Prop :=
  (forall x : atom, locally_closed (rho x)) /\
  (forall (x : atom) (T : ty), Gamma x = Some T -> R T (rho x)).

Lemma R_lc : forall (T : ty) (t : tm), R T t -> locally_closed t.
Proof.
  induction T; intros t HR; simpl in HR; tauto.
Qed.

Lemma R_sn : forall (T : ty) (t : tm), R T t -> strongly_normalizing t.
Proof.
  induction T; intros t HR; simpl in HR; tauto.
Qed.

(** The relation is closed under reduction. *)

Lemma R_step : forall (T : ty) (t t' : tm), R T t -> t --> t' -> R T t'.
Proof.
  intros T. induction T; intros t t' HR Hstep; simpl in HR.
  - (* Bool *) destruct HR as [Hlc Hsn]. split.
    + apply step_lc with (t := t); assumption.
    + apply SN_step with (t := t); assumption.
  - (* Arrow *) destruct HR as [Hlc [Hsn Hcl]]. split.
    + apply step_lc with (t := t); assumption.
    + split.
      * apply SN_step with (t := t); assumption.
      * intros u Hu. apply IHT2 with (t := tm_app t u).
        -- apply Hcl. exact Hu.
        -- apply ST_App1.
           ++ exact Hstep.
           ++ apply R_lc with (T := T1). exact Hu.
Qed.

(** A neutral term all of whose one-step reducts are related is itself
    related.  ("Closure under expansion".) *)

Lemma R_expand : forall (T : ty) (t : tm),
    locally_closed t ->
    ~ value t ->
    strongly_normalizing t ->
    (forall t' : tm, t --> t' -> R T t') ->
    R T t.
Proof.
  induction T; intros t Hlc Hnv Hsn Hred; simpl.
  - (* Bool *) split; assumption.
  - (* Arrow *) split; [assumption |]. split; [assumption |].
    intros u Hu.
    assert (Hcase1 : forall t' : tm, t --> t' -> R T2 (tm_app t' u)).
    { intros t' Hstep. destruct (Hred t' Hstep) as [Hlc' [Hsn' Hcl']].
      apply Hcl'. exact Hu. }
    apply IHT2.
    + (* locally_closed (tm_app t u) *) constructor; [assumption |].
      apply R_lc with (T := T1). exact Hu.
    + apply not_value_app.
    + (* SN (tm_app t u) *) apply SN_intro. intros w Hw.
      destruct (step_app_inv t u w Hw) as
        [[T0 [body [Heq1 [Hvu Heq2]]]] | [[t' [Hstep Heq]] | [u' [Hv [Hstep Heq]]]]];
        subst.
      * exfalso. apply Hnv. apply v_abs. assumption.
      * apply R_sn with (T := T2). apply Hcase1. exact Hstep.
      * exfalso. apply Hnv. exact Hv.
    + (* all reducts of (t u) related *) intros w Hw.
      destruct (step_app_inv t u w Hw) as
        [[T0 [body [Heq1 [Hvu Heq2]]]] | [[t' [Hstep Heq]] | [u' [Hv [Hstep Heq]]]]];
        subst.
      * exfalso. apply Hnv. apply v_abs. assumption.
      * apply Hcase1. exact Hstep.
      * exfalso. apply Hnv. exact Hv.
Qed.

(** If the branches are related, so is the conditional. *)

Lemma R_if : forall (T : ty) (b t2 t3 : tm),
    R Ty_Bool b -> R T t2 -> R T t3 -> R T (tm_if b t2 t3).
Proof.
  intros T b0 t2 t3 Hb H2 H3.
  destruct Hb as [Hlcb Hsnb].
  assert (H : forall b : tm,
             strongly_normalizing b ->
             locally_closed b ->
             (forall s' : tm, tm_if b t2 t3 --> s' -> R T s') /\
             strongly_normalizing (tm_if b t2 t3)).
  { intros b Hsn. induction Hsn as [b Hreds IH]. intros Hlcb'.
    split.
    - (* reducts are related *) intros s' Hs'.
      destruct (step_if_inv b t2 t3 s' Hs') as
        [[Hb' Heq] | [[Hb' Heq] | [b' [Hstep Heq]]]]; subst.
      + exact H2.
      + exact H3.
      + apply R_expand with (t := tm_if b' t2 t3).
        * constructor.
          -- apply step_lc with (t := b); assumption.
          -- apply R_lc with (T := T). exact H2.
          -- apply R_lc with (T := T). exact H3.
        * apply not_value_if.
        * apply (proj2 (IH b' Hstep (step_lc b b' Hstep Hlcb'))).
        * apply (proj1 (IH b' Hstep (step_lc b b' Hstep Hlcb'))).
    - (* the conditional is strongly normalizing *)
      apply SN_intro. intros s' Hs'.
      destruct (step_if_inv b t2 t3 s' Hs') as
        [[Hb' Heq] | [[Hb' Heq] | [b' [Hstep Heq]]]]; subst.
      + apply R_sn with (T := T). exact H2.
      + apply R_sn with (T := T). exact H3.
      + apply (proj2 (IH b' Hstep (step_lc b b' Hstep Hlcb'))).
  }
  apply R_expand with (t := tm_if b0 t2 t3).
  - constructor; [exact Hlcb | apply R_lc with (T := T) | apply R_lc with (T := T)];
      assumption.
  - apply not_value_if.
  - apply (proj2 (H b0 Hsnb Hlcb)).
  - apply (proj1 (H b0 Hsnb Hlcb)).
Qed.

(** Applying an abstraction (whose body is locally closed) to a
    related argument yields a related result. *)

Lemma R_abs_app : forall (T1 T2 : ty) (body : tm),
    lc_at 1 body ->
    (forall v : tm, R T1 v -> R T2 (open body v)) ->
    forall u : tm, strongly_normalizing u -> R T1 u ->
      R T2 (tm_app (tm_abs T1 body) u).
Proof.
  intros T1 T2 body Hlc Hbeta u Hsn.
  induction Hsn as [u Hreds IH].
  intros Hu.
  apply R_expand with (t := tm_app (tm_abs T1 body) u).
  - (* locally closed *) constructor.
    + apply lc_abs. exact Hlc.
    + apply R_lc with (T := T1). exact Hu.
  - apply not_value_app.
  - (* strongly normalizing *) apply SN_intro. intros w Hw.
    destruct (step_abs_app_inv T1 body u w Hw) as
      [[Hvu Heq] | [u' [Hstep Heq]]]; subst.
    + apply R_sn with (T := T2). apply Hbeta. exact Hu.
    + apply R_sn with (T := T2). apply IH.
      * exact Hstep.
      * apply R_step with (t := u); assumption.
  - (* reducts related *) intros w Hw.
    destruct (step_abs_app_inv T1 body u w Hw) as
      [[Hvu Heq] | [u' [Hstep Heq]]]; subst.
    + apply Hbeta. exact Hu.
    + apply IH.
      * exact Hstep.
      * apply R_step with (t := u); assumption.
Qed.

(** ** Substitution lemmas *)

Lemma subst_all_lc : forall (t : tm) (rho : atom -> tm),
    (forall x : atom, locally_closed (rho x)) ->
    forall (k : nat), lc_at k t -> lc_at k (subst_all rho t).
Proof.
  induction t as [n | x | t1 IH1 t2 IH2 | T t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
    intros rho Hrho k Hlc; simpl.
  - (* bvar *) inversion Hlc; subst. constructor. assumption.
  - (* fvar *) apply lc_at_weaken with (k := 0).
    + exact (Hrho x).
    + lia.
  - (* app *) inversion Hlc; subst. constructor.
    + apply IH1; assumption.
    + apply IH2; assumption.
  - (* abs *) inversion Hlc; subst. apply lc_abs. apply IH1; assumption.
  - (* true *) constructor.
  - (* false *) constructor.
  - (* if *) inversion Hlc; subst. constructor;
      [apply IH1 | apply IH2 | apply IH3]; assumption.
Qed.

(** Opening a term at a free variable and then substituting that
    variable commutes with opening at the substituted term. *)

Lemma open_rec_bvar : forall (k : nat) (u : tm) (n : nat),
    open_rec k u (tm_bvar n) = if Nat.eqb k n then u else tm_bvar n.
Proof. reflexivity. Qed.

Lemma open_rec_fvar : forall (k : nat) (u : tm) (x : atom),
    open_rec k u (tm_fvar x) = tm_fvar x.
Proof. reflexivity. Qed.

Lemma subst_all_fvar : forall (rho : atom -> tm) (x : atom),
    subst_all rho (tm_fvar x) = rho x.
Proof. reflexivity. Qed.

Lemma subst_all_bvar : forall (rho : atom -> tm) (n : nat),
    subst_all rho (tm_bvar n) = tm_bvar n.
Proof. reflexivity. Qed.

Lemma update_env_eq : forall (rho : atom -> tm) (x : atom) (u : tm),
    update_env rho x u x = u.
Proof. intros. unfold update_env. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma update_env_neq : forall (rho : atom -> tm) (x : atom) (u : tm) (y : atom),
    x <> y -> update_env rho x u y = rho y.
Proof.
  intros rho x u y Hxy. unfold update_env.
  destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. exfalso. apply Hxy. exact E.
  - reflexivity.
Qed.

Lemma update_eq : forall (Gamma : context) (x : atom) (T : ty),
    update Gamma x T x = Some T.
Proof. intros. unfold update. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma update_neq : forall (Gamma : context) (x : atom) (T : ty) (y : atom),
    x <> y -> update Gamma x T y = Gamma y.
Proof.
  intros Gamma x T y Hxy. unfold update.
  destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. exfalso. apply Hxy. exact E.
  - reflexivity.
Qed.

Lemma not_in_app_l : forall (l1 l2 : list atom) (x : atom),
    ~ In x (l1 ++ l2) -> ~ In x l1.
Proof.
  intros l1 l2 x H Hin. apply H. apply in_app_iff. left. exact Hin.
Qed.

Lemma not_in_app_r : forall (l1 l2 : list atom) (x : atom),
    ~ In x (l1 ++ l2) -> ~ In x l2.
Proof.
  intros l1 l2 x H Hin. apply H. apply in_app_iff. right. exact Hin.
Qed.

Lemma subst_all_open_rec : forall (rho : atom -> tm),
    (forall x : atom, locally_closed (rho x)) ->
    forall (t : tm) (x : atom) (u : tm) (k : nat),
      ~ In x (fv t) ->
      subst_all (update_env rho x u) (open_rec k (tm_fvar x) t) =
      open_rec k u (subst_all rho t).
Proof.
  intros rho Hrho t.
  induction t as [n | y | t1 IH1 t2 IH2 | T t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
    intros x u k Hfresh; cbn [open_rec subst_all].
  - (* bvar *)
    destruct (Nat.eqb k n) eqn:E; cbn [open_rec subst_all].
    + apply update_env_eq.
    + reflexivity.
  - (* fvar *)
    simpl in Hfresh.
    assert (Hxy : x <> y) by (intro Hc; subst; apply Hfresh; simpl; auto).
    rewrite update_env_neq by exact Hxy.
    symmetry. apply lc0_open_rec. apply Hrho.
  - (* app *)
    f_equal.
    + apply IH1. apply not_in_app_l in Hfresh. exact Hfresh.
    + apply IH2. apply not_in_app_r in Hfresh. exact Hfresh.
  - (* abs *)
    f_equal. apply IH1. exact Hfresh.
  - (* true *) reflexivity.
  - (* false *) reflexivity.
  - (* if *)
    f_equal.
    + apply IH1. apply not_in_app_l in Hfresh. exact Hfresh.
    + apply IH2. apply not_in_app_r in Hfresh. apply not_in_app_l in Hfresh.
      exact Hfresh.
    + apply IH3. apply not_in_app_r in Hfresh. apply not_in_app_r in Hfresh.
      exact Hfresh.
Qed.

(** ============================================================ *)
(** * Fundamental theorem of logical relations.                  *)
(** ============================================================ *)

Theorem fundamental : forall (Gamma : context) (t : tm) (T : ty),
    <{ Gamma |-- t \in T }> ->
    locally_closed t /\
    (forall rho : atom -> tm, env_sem Gamma rho -> R T (subst_all rho t)).
Proof.
  intros Gamma t T H.
  induction H as
    [ Gamma x T Hx
    | L Gamma T1 T2 t1 Hprem IH
    | Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
    | Gamma
    | Gamma
    | Gamma t1 t2 t3 T H1 IH1 H2 IH2 H3 IH3 ].
  - (* T_Var *) simpl. split.
    + constructor.
    + intros rho Henv. simpl. apply (proj2 Henv). exact Hx.
  - (* T_Abs *) split.
    + (* locally_closed (tm_abs T1 t1) *)
      apply lc_abs.
      destruct (exists_fresh L) as [x Hx].
      apply lc_open_inv with (x := x).
      exact (proj1 (IH x Hx)).
    + intros rho Henv. simpl.
      assert (Hlc1 : lc_at 1 t1).
      { destruct (exists_fresh L) as [x Hx].
        apply lc_open_inv with (x := x).
        exact (proj1 (IH x Hx)). }
      split.
      * (* locally closed *) apply lc_abs.
        apply subst_all_lc with (rho := rho); [apply Henv | exact Hlc1].
      * split.
        -- (* strongly normalizing *) apply SN_abs.
        -- (* arrow clause *) intros u Hu.
           apply R_abs_app with (body := subst_all rho t1).
           ++ apply subst_all_lc with (rho := rho); [apply Henv | exact Hlc1].
           ++ intros v Hv.
              destruct (exists_fresh_two L (fv t1)) as [x [HxL Hxfv]].
              assert (HIH : R T2 (subst_all (update_env rho x v)
                                             (open t1 (tm_fvar x)))).
              { apply (proj2 (IH x HxL)). split.
                - (* locally closed images *) intro y.
                  destruct (Nat.eqb x y) eqn:E.
                  + apply Nat.eqb_eq in E. subst y. rewrite update_env_eq.
                    apply R_lc with (T := T1). exact Hv.
                  + apply Nat.eqb_neq in E. rewrite update_env_neq by exact E.
                    apply (proj1 Henv).
                - (* semantic types *) intros y S Hy.
                  destruct (Nat.eqb x y) eqn:E.
                  + apply Nat.eqb_eq in E. subst y. rewrite update_env_eq.
                    rewrite update_eq in Hy. injection Hy as Hy. subst S.
                    exact Hv.
                  + apply Nat.eqb_neq in E. rewrite update_env_neq by exact E.
                    rewrite update_neq in Hy by exact E.
                    apply (proj2 Henv). exact Hy. }
              unfold open in HIH.
              rewrite (subst_all_open_rec rho (proj1 Henv) t1 x v 0 Hxfv) in HIH.
              exact HIH.
           ++ apply R_sn with (T := T1). exact Hu.
           ++ exact Hu.
  - (* T_App *) simpl. split.
    + constructor; [apply (proj1 IH1) | apply (proj1 IH2)].
    + intros rho Henv.
      pose proof (proj2 IH1 rho Henv) as HR1.
      pose proof (proj2 IH2 rho Henv) as HR2.
      simpl in HR1, HR2. destruct HR1 as [Hlc1 [Hsn1 Hcl1]].
      apply Hcl1. exact HR2.
  - (* T_True *) simpl. split.
    + constructor.
    + intros rho Henv. split; [constructor | apply SN_true].
  - (* T_False *) simpl. split.
    + constructor.
    + intros rho Henv. split; [constructor | apply SN_false].
  - (* T_If *) simpl. split.
    + constructor; [apply (proj1 IH1) | apply (proj1 IH2) | apply (proj1 IH3)].
    + intros rho Henv.
      apply R_if.
      * exact (proj2 IH1 rho Henv).
      * exact (proj2 IH2 rho Henv).
      * exact (proj2 IH3 rho Henv).
Qed.

(** ============================================================ *)
(** * The target theorem.                                       *)
(** ============================================================ *)

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T H.
  destruct (fundamental empty t T H) as [Hlc HR].
  assert (Henv : env_sem empty rho_id).
  { split.
    - intro x. constructor.
    - intros x S Hx. unfold empty in Hx. discriminate Hx. }
  pose proof (HR rho_id Henv) as HR'.
  rewrite subst_all_id in HR'.
  apply R_sn with (T := T). exact HR'.
Qed.

End STLCCBVNormalizationTask.
