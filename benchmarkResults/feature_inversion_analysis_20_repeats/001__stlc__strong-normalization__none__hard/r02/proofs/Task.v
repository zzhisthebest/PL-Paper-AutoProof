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

(* ================================================================ *)
(* Auxiliary definitions and lemmas for the normalization proof.    *)
(* None of the supplied language definitions or the target theorem  *)
(* statement are changed.                                           *)
(* ================================================================ *)

(* ---------- Free variables and fresh atoms ---------- *)

Fixpoint fvars (t : tm) : list atom :=
  match t with
  | tm_bvar _ => nil
  | tm_fvar x => x :: nil
  | tm_app t1 t2 => fvars t1 ++ fvars t2
  | tm_abs _ t1 => fvars t1
  | tm_true => nil
  | tm_false => nil
  end.

Fixpoint max_atom (l : list atom) : atom :=
  match l with
  | nil => 0
  | x :: xs => Nat.max x (max_atom xs)
  end.

Definition fresh (l : list atom) : atom := S (max_atom l).

Lemma In_max_atom : forall (l : list atom) (x : atom),
  In x l -> x <= max_atom l.
Proof.
  induction l as [| y ys IH]; intros x Hin.
  - inversion Hin.
  - simpl in Hin. destruct Hin as [-> | Hin].
    + apply Nat.le_max_l.
    + apply Nat.le_trans with (max_atom ys);
        [apply IH; assumption | apply Nat.le_max_r].
Qed.

Lemma fresh_notin : forall l, ~ In (fresh l) l.
Proof.
  intros l Hin. unfold fresh in Hin.
  pose proof (In_max_atom l (S (max_atom l)) Hin). lia.
Qed.

(* ---------- Simultaneous substitution of free variables ---------- *)

Fixpoint subst_fvar (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_app t1 t2 => tm_app (subst_fvar sigma t1) (subst_fvar sigma t2)
  | tm_abs T t1 => tm_abs T (subst_fvar sigma t1)
  | tm_true => tm_true
  | tm_false => tm_false
  end.

Definition extend (sigma : atom -> tm) (x : atom) (u : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then u else sigma y.

Lemma subst_fvar_id : forall t, subst_fvar tm_fvar t = t.
Proof.
  induction t as [i | x | t1 IH1 t2 IH2 | T t1 IH | | ]; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(* ---------- Local closure lemmas ---------- *)

Lemma lc_at_bvar_inv : forall k i, lc_at k (tm_bvar i) -> i < k.
Proof. intros k i H. inversion H. assumption. Qed.

Lemma lc_at_app_inv : forall k t1 t2,
  lc_at k (tm_app t1 t2) -> lc_at k t1 /\ lc_at k t2.
Proof. intros k t1 t2 H. inversion H. split; assumption. Qed.

Lemma lc_at_abs_inv : forall k T t1,
  lc_at k (tm_abs T t1) -> lc_at (S k) t1.
Proof. intros k T t1 H. inversion H. assumption. Qed.

Lemma lc_at_weaken : forall k t, lc_at k t -> lc_at (S k) t.
Proof.
  intros k t H. induction H.
  - apply lc_bvar. lia.
  - apply lc_fvar.
  - apply lc_app; assumption.
  - apply lc_abs. assumption.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma lc_at_mono : forall k k', k <= k' -> forall t, lc_at k t -> lc_at k' t.
Proof.
  intros k k' Hle. induction Hle as [| k'' Hle IH]; intros t H.
  - exact H.
  - apply lc_at_weaken. apply IH. exact H.
Qed.

Lemma lc_open_rec : forall k u t,
  lc_at (S k) t -> lc_at k u -> lc_at k (open_rec k u t).
Proof.
  intros k u t. revert k.
  induction t as [i | x | t1 IH1 t2 IH2 | T t1 IH | | ];
    intros k Ht Hu; simpl.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst i. exact Hu.
    + apply lc_bvar. apply Nat.eqb_neq in E.
      pose proof (lc_at_bvar_inv _ _ Ht). lia.
  - apply lc_fvar.
  - destruct (lc_at_app_inv _ _ _ Ht) as [H1 H2]. apply lc_app; auto.
  - apply lc_abs. apply IH with (k := S k).
    + apply lc_at_abs_inv in Ht. exact Ht.
    + apply lc_at_weaken. exact Hu.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma lc_open_rec_inv : forall k u t,
  lc_at k (open_rec k u t) -> lc_at (S k) t.
Proof.
  intros k u t. revert k.
  induction t as [i | x | t1 IH1 t2 IH2 | T t1 IH | | ];
    intros k H; simpl in *.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst i. apply lc_bvar. lia.
    + apply lc_bvar. apply Nat.eqb_neq in E.
      pose proof (lc_at_bvar_inv _ _ H). lia.
  - apply lc_fvar.
  - destruct (lc_at_app_inv _ _ _ H) as [H1 H2]. apply lc_app; auto.
  - apply lc_abs. apply IH with (k := S k).
    apply lc_at_abs_inv in H. exact H.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma open_rec_lc_id : forall k u t, lc_at k t -> open_rec k u t = t.
Proof.
  intros k u t. revert k.
  induction t as [i | x | t1 IH1 t2 IH2 | T t1 IH | | ];
    intros k H; simpl.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. pose proof (lc_at_bvar_inv _ _ H). lia.
    + reflexivity.
  - reflexivity.
  - destruct (lc_at_app_inv _ _ _ H) as [H1 H2].
    rewrite IH1 by assumption. rewrite IH2 by assumption. reflexivity.
  - rewrite IH with (k := S k) by (apply lc_at_abs_inv in H; exact H).
    reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(* ---------- Substitution and opening commute ---------- *)

Lemma subst_fvar_open_rec : forall sigma x u t k,
  (forall y, locally_closed (sigma y)) ->
  ~ In x (fvars t) ->
  subst_fvar (extend sigma x u) (open_rec k (tm_fvar x) t)
    = open_rec k u (subst_fvar sigma t).
Proof.
  intros sigma x u t. induction t as [i | y | t1 IH1 t2 IH2 | T t1 IH | | ];
    intros k Hcl Hfresh; simpl.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst i.
      unfold extend. simpl. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - unfold extend. simpl.
    destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst y. exfalso. apply Hfresh.
      simpl. left. reflexivity.
    + symmetry. apply open_rec_lc_id.
      apply lc_at_mono with (k := 0); [lia | apply Hcl].
  - assert (Hf1 : ~ In x (fvars t1)).
    { intros H; apply Hfresh. apply in_or_app. left. exact H. }
    assert (Hf2 : ~ In x (fvars t2)).
    { intros H; apply Hfresh. apply in_or_app. right. exact H. }
    rewrite (IH1 k Hcl Hf1). rewrite (IH2 k Hcl Hf2). reflexivity.
  - rewrite (IH (S k) Hcl Hfresh). reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma subst_fvar_open : forall sigma x u t,
  (forall y, locally_closed (sigma y)) ->
  ~ In x (fvars t) ->
  subst_fvar (extend sigma x u) (open t (tm_fvar x))
    = open (subst_fvar sigma t) u.
Proof.
  intros. unfold open. apply subst_fvar_open_rec; assumption.
Qed.

(* ---------- Elementary facts about values and steps ---------- *)

Lemma step_abs_inv : forall T t t', ~ (tm_abs T t --> t').
Proof. intros T t t' H. inversion H. Qed.

Lemma step_true_inv : forall t', ~ (tm_true --> t').
Proof. intros t' H. inversion H. Qed.

Lemma step_false_inv : forall t', ~ (tm_false --> t').
Proof. intros t' H. inversion H. Qed.

Lemma value_app_inv : forall t1 t2, ~ value (tm_app t1 t2).
Proof. intros t1 t2 H. inversion H. Qed.

Lemma SN_no_step : forall t, (forall t', ~ (t --> t')) -> strongly_normalizing t.
Proof.
  intros t H. apply SN_intro. intros t' Hs. exfalso. exact (H t' Hs).
Qed.

Lemma SN_step : forall t t',
  strongly_normalizing t -> t --> t' -> strongly_normalizing t'.
Proof.
  intros t t' Hsn Hs. destruct Hsn as [u Hred]. apply Hred. exact Hs.
Qed.

Lemma lc_step : forall t t',
  locally_closed t -> t --> t' -> locally_closed t'.
Proof.
  intros t t' Hlc Hs. induction Hs.
  - simpl in Hlc. destruct (lc_at_app_inv _ _ _ Hlc) as [H1 H2].
    apply lc_at_abs_inv in H1.
    apply lc_open_rec with (k := 0); assumption.
  - simpl in Hlc. destruct (lc_at_app_inv _ _ _ Hlc) as [H1 H2].
    apply lc_app; [apply IHHs; assumption | assumption].
  - simpl in Hlc. destruct (lc_at_app_inv _ _ _ Hlc) as [H1 H2].
    apply lc_app; [assumption | apply IHHs; assumption].
Qed.

(* ---------- Characterization of steps at an application ---------- *)

Lemma step_app_inv : forall t u r,
  tm_app t u --> r ->
  (exists T body v, t = tm_abs T body /\ value t /\ u = v /\ r = open body v) \/
  (exists t', t --> t' /\ r = tm_app t' u) \/
  (exists u', value t /\ u --> u' /\ r = tm_app t u').
Proof.
  intros t u r H.
  inversion H; subst.
  - left. eexists; eexists; eexists. repeat split; try reflexivity.
    apply v_abs. match goal with Hlc : locally_closed _ |- _ => exact Hlc end.
  - right; left. eexists. split; [eassumption | reflexivity].
  - right; right. eexists. repeat split; try eassumption; try reflexivity.
Qed.

(* ---------- The logical relation (reducibility predicates) ---------- *)

Fixpoint Red (T : ty) (t : tm) : Prop :=
  match T with
  | Ty_Bool => locally_closed t /\ strongly_normalizing t
  | Ty_Arrow T1 T2 =>
      locally_closed t /\ strongly_normalizing t /\
      (forall u, Red T1 u -> Red T2 (tm_app t u))
  end.

Lemma Red_lc : forall T t, Red T t -> locally_closed t.
Proof. intros T; destruct T; intros t H; simpl in H; tauto. Qed.

Lemma Red_sn : forall T t, Red T t -> strongly_normalizing t.
Proof. intros T; destruct T; intros t H; simpl in H; tauto. Qed.

Lemma Red_app : forall T1 T2 (t u : tm),
  Red (Ty_Arrow T1 T2) t -> Red T1 u -> Red T2 (tm_app t u).
Proof.
  intros T1 T2 t u H1 H2. simpl in H1.
  destruct H1 as [Hl [Hs Hf]]. apply Hf. exact H2.
Qed.

(* Red is closed under reduction. *)
Lemma Red_step : forall T t t', Red T t -> t --> t' -> Red T t'.
Proof.
  induction T as [| T1 IH1 T2 IH2]; intros t t' HR Hs; simpl in *.
  - destruct HR as [Hlc Hsn]. split.
    + apply lc_step with (t := t); assumption.
    + apply SN_step with (t := t); assumption.
  - destruct HR as [Hlc [Hsn Hforall]]. split.
    + apply lc_step with (t := t); assumption.
    + split.
      * apply SN_step with (t := t); assumption.
      * intros u Hu.
        apply IH2 with (t := tm_app t u).
        -- apply Hforall. exact Hu.
        -- apply ST_App1. exact Hs.
           apply Red_lc with (T := T1). exact Hu.
Qed.

(* Expansion for terms that are not values.  This is the "neutral"
   rule of the call-by-value reducibility candidates. *)
Lemma Red_nonvalue : forall T t,
  locally_closed t ->
  strongly_normalizing t ->
  (forall t', t --> t' -> Red T t') ->
  ~ value t ->
  Red T t.
Proof.
  induction T as [| T1 IHT1 T2 IHT2]; intros t Hlc Hsn Hred Hnv; simpl.
  - split; assumption.
  - split; [assumption |]. split; [assumption |].
    intros u Hu.
    apply IHT2 with (t := tm_app t u).
    + apply lc_app; [assumption | apply Red_lc with (T := T1); assumption].
    + apply SN_intro. intros r Hr.
      destruct (step_app_inv _ _ _ Hr) as
        [[T0 [body [v [Et [Hv [Eu Er]]]]]] |
         [[t' [Hs Er]] | [u' [Hv [Hs Er]]]]].
      * subst t. exfalso. apply Hnv. exact Hv.
      * subst r. apply Red_sn with (T := T2).
        pose proof (Hred t' Hs) as HRt'.
        exact (Red_app T1 T2 t' u HRt' Hu).
      * exfalso. apply Hnv. exact Hv.
    + intros r Hr.
      destruct (step_app_inv _ _ _ Hr) as
        [[T0 [body [v [Et [Hv [Eu Er]]]]]] |
         [[t' [Hs Er]] | [u' [Hv [Hs Er]]]]].
      * subst t. exfalso. apply Hnv. exact Hv.
      * subst r. exact (Red_app T1 T2 t' u (Hred t' Hs) Hu).
      * exfalso. apply Hnv. exact Hv.
    + apply value_app_inv.
Qed.

(* Beta-expansion at an abstraction: if the body is related to every
   related argument, then the application of the abstraction is
   related.  The proof is by well-founded induction on the argument. *)
Lemma Red_abs_app : forall u, strongly_normalizing u ->
  forall T1 T2 (t : tm),
    lc_at 1 t ->
    (forall v, Red T1 v -> Red T2 (open t v)) ->
    Red T1 u -> Red T2 (tm_app (tm_abs T1 t) u).
Proof.
  intros u Hsn. induction Hsn as [u Hreds IH].
  intros T1 T2 t Hlc Hbody Hu.
  apply Red_nonvalue with (t := tm_app (tm_abs T1 t) u).
  - apply lc_app. apply lc_abs. exact Hlc.
    apply Red_lc with (T := T1). exact Hu.
  - apply SN_intro. intros r Hr.
    destruct (step_app_inv _ _ _ Hr) as
      [[T0 [body [v [Et [Hv [Eu Er]]]]]] |
       [[t' [Hs Er]] | [u' [Hv [Hs Er]]]]].
    + injection Et as HT Heq. subst T0. subst t. subst v. subst r.
      apply Red_sn with (T := T2). apply Hbody. exact Hu.
    + exfalso. exact (step_abs_inv T1 t t' Hs).
    + subst r. apply Red_sn with (T := T2).
      exact (IH u' Hs T1 T2 t Hlc Hbody (Red_step T1 u u' Hu Hs)).
  - intros r Hr.
    destruct (step_app_inv _ _ _ Hr) as
      [[T0 [body [v [Et [Hv [Eu Er]]]]]] |
       [[t' [Hs Er]] | [u' [Hv [Hs Er]]]]].
    + injection Et as HT Heq. subst T0. subst t. subst v. subst r.
      apply Hbody. exact Hu.
    + exfalso. exact (step_abs_inv T1 t t' Hs).
    + subst r. exact (IH u' Hs T1 T2 t Hlc Hbody (Red_step T1 u u' Hu Hs)).
  - apply value_app_inv.
Qed.

(* Free variables are related at every type. *)
Lemma Red_var : forall T x, Red T (tm_fvar x).
Proof.
  intros T x.
  apply Red_nonvalue.
  - apply lc_fvar.
  - apply SN_no_step. intros t' H. inversion H.
  - intros t' H. inversion H.
  - intro H. inversion H.
Qed.

(* ---------- Semantic typing ---------- *)

Definition valuation (Gamma : context) (sigma : atom -> tm) : Prop :=
  (forall x T, Gamma x = Some T -> Red T (sigma x)) /\
  (forall x, locally_closed (sigma x)).

Theorem fundamental : forall Gamma t T,
  has_type Gamma t T ->
  forall sigma, valuation Gamma sigma -> Red T (subst_fvar sigma t).
Proof.
  intros Gamma t T HT.
  induction HT as [Gamma x T Hx
                | L Gamma T1 T2 t1 Hprem IHprem
                | Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
                | Gamma
                | Gamma];
  intros sigma Hval; destruct Hval as [Hval1 Hval2].
  - (* T_Var *) simpl. apply Hval1. exact Hx.
  - (* T_Abs *)
    simpl.
    set (body := subst_fvar sigma t1).
    remember (fresh (L ++ fvars t1)) as x eqn:Ex.
    assert (HxL : ~ In x L).
    { intros Hin. apply fresh_notin with (l := L ++ fvars t1).
      rewrite <- Ex. apply in_or_app. left. exact Hin. }
    assert (Hxt : ~ In x (fvars t1)).
    { intros Hin. apply fresh_notin with (l := L ++ fvars t1).
      rewrite <- Ex. apply in_or_app. right. exact Hin. }
    assert (Hvalx : valuation (update Gamma x T1)
                               (extend sigma x (tm_fvar x))).
    { split.
      - intros y T' Hy. unfold extend. simpl.
        destruct (Nat.eqb x y) eqn:E.
        + apply Nat.eqb_eq in E. subst y.
          assert (Hup : update Gamma x T1 x = Some T1).
          { unfold update. rewrite Nat.eqb_refl. reflexivity. }
          rewrite Hup in Hy. injection Hy as HTeq. subst T'. apply Red_var.
        + assert (Hy' : Gamma y = Some T').
          { unfold update in Hy. rewrite E in Hy. exact Hy. }
          apply Hval1. exact Hy'.
      - intros y. unfold extend. simpl.
        destruct (Nat.eqb x y) eqn:E.
        + apply Nat.eqb_eq in E. subst y. apply lc_fvar.
        + apply Hval2. }
    assert (Hid : subst_fvar (extend sigma x (tm_fvar x))
                             (open t1 (tm_fvar x)) = open body (tm_fvar x)).
    { apply subst_fvar_open; assumption. }
    assert (Hres : Red T2 (open body (tm_fvar x))).
    { rewrite <- Hid.
      exact (IHprem x HxL (extend sigma x (tm_fvar x)) Hvalx). }
    assert (Hlcbody : lc_at 1 body).
    { apply lc_open_rec_inv with (k := 0) (u := tm_fvar x).
      apply Red_lc with (T := T2). exact Hres. }
    split.
    + apply lc_abs. exact Hlcbody.
    + split.
      * apply SN_no_step. intros t' Hs.
        exfalso. exact (step_abs_inv T1 body t' Hs).
      * intros u Hu.
        apply Red_abs_app with (u := u).
        -- apply Red_sn with (T := T1). exact Hu.
        -- exact Hlcbody.
        -- intros v Hv.
           assert (Hvalv : valuation (update Gamma x T1) (extend sigma x v)).
           { split.
             - intros y T' Hy. unfold extend. simpl.
               destruct (Nat.eqb x y) eqn:E.
               + apply Nat.eqb_eq in E. subst y.
                 assert (Hup : update Gamma x T1 x = Some T1).
                 { unfold update. rewrite Nat.eqb_refl. reflexivity. }
                 rewrite Hup in Hy. injection Hy as HTeq. subst T'. exact Hv.
               + assert (Hy' : Gamma y = Some T').
                 { unfold update in Hy. rewrite E in Hy. exact Hy. }
                 apply Hval1. exact Hy'.
             - intros y. unfold extend. simpl.
               destruct (Nat.eqb x y) eqn:E.
               + apply Nat.eqb_eq in E. subst y.
                 apply Red_lc with (T := T1). exact Hv.
               + apply Hval2. }
           assert (Hidv : subst_fvar (extend sigma x v)
                                     (open t1 (tm_fvar x)) = open body v).
           { apply subst_fvar_open; assumption. }
           rewrite <- Hidv.
           exact (IHprem x HxL (extend sigma x v) Hvalv).
        -- exact Hu.
  - (* T_App *)
    simpl.
    pose proof (IH1 sigma (conj Hval1 Hval2)) as HR1.
    pose proof (IH2 sigma (conj Hval1 Hval2)) as HR2.
    exact (Red_app T1 T2 (subst_fvar sigma t1) (subst_fvar sigma t2) HR1 HR2).
  - (* T_True *)
    simpl. split.
    + apply lc_true.
    + apply SN_no_step. intros t' Hs. exfalso. exact (step_true_inv t' Hs).
  - (* T_False *)
    simpl. split.
    + apply lc_false.
    + apply SN_no_step. intros t' Hs. exfalso. exact (step_false_inv t' Hs).
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T HT.
  assert (Hval : valuation empty (fun x => tm_fvar x)).
  { split.
    - intros x T' Hx. unfold empty in Hx. discriminate.
    - intros x. apply lc_fvar. }
  pose proof (fundamental empty t T HT (fun x => tm_fvar x) Hval) as H.
  rewrite subst_fvar_id in H.
  apply Red_sn with (T := T). exact H.
Qed.

End STLCNormalizationNoneHardTask.
