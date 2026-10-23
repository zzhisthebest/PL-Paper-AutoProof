(** STLC call-by-value strong-normalization benchmark task. *)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Relations.Relation_Definitions.
From Stdlib Require Import Bool.Bool.
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

(** ** Auxiliary definitions and lemmas for the normalization proof. *)

(** *** Fresh atoms and free variables. *)

Fixpoint max_list (l : list atom) : atom :=
  match l with
  | nil => 0
  | x :: l' => Nat.max x (max_list l')
  end.

Lemma max_list_spec : forall (l : list atom) (x : atom),
  In x l -> x <= max_list l.
Proof.
  intros l x H. induction l as [| y l' IH].
  - inversion H.
  - simpl in H. destruct H as [-> | H].
    + apply Nat.le_max_l.
    + apply Nat.le_trans with (max_list l');
        [apply IH; exact H | apply Nat.le_max_r].
Qed.

Definition fresh (l : list atom) : atom := S (max_list l).

Lemma fresh_not_in : forall l, ~ In (fresh l) l.
Proof.
  intros l H. apply max_list_spec in H. unfold fresh in H. lia.
Qed.

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

Lemma not_in_fv_app_l : forall x t1 t2,
  ~ In x (fv t1 ++ fv t2) -> ~ In x (fv t1).
Proof.
  intros x t1 t2 H Hin. apply H. apply in_or_app. left. exact Hin.
Qed.

Lemma not_in_fv_app_r : forall x t1 t2,
  ~ In x (fv t1 ++ fv t2) -> ~ In x (fv t2).
Proof.
  intros x t1 t2 H Hin. apply H. apply in_or_app. right. exact Hin.
Qed.

(** *** Decidable tests for local closure and values. *)

Fixpoint lcb (k : nat) (t : tm) : bool :=
  match t with
  | tm_bvar i => Nat.ltb i k
  | tm_fvar _ => true
  | tm_app t1 t2 => andb (lcb k t1) (lcb k t2)
  | tm_abs _ t1 => lcb (S k) t1
  | tm_true => true
  | tm_false => true
  | tm_if t1 t2 t3 => andb (lcb k t1) (andb (lcb k t2) (lcb k t3))
  end.

Lemma lcb_spec : forall t k, lcb k t = true <-> lc_at k t.
Proof.
  induction t; intros k; simpl.
  - (* bvar *) split; intro H.
    + apply Nat.ltb_lt in H. constructor. exact H.
    + apply Nat.ltb_lt. inversion H. subst. lia.
  - (* fvar *) split; intro H; constructor.
  - (* app *) rewrite andb_true_iff. split.
    + intros [H1 H2]. constructor.
      * apply (proj1 (IHt1 k)); exact H1.
      * apply (proj1 (IHt2 k)); exact H2.
    + intro H. inversion H; subst. split.
      * apply (proj2 (IHt1 k)); assumption.
      * apply (proj2 (IHt2 k)); assumption.
  - (* abs *) split; intro H.
    + apply lc_abs. apply (proj1 (IHt (S k))); exact H.
    + apply (proj2 (IHt (S k))). inversion H. subst. assumption.
  - (* true *) split; intro H; constructor.
  - (* false *) split; intro H; constructor.
  - (* if *) rewrite andb_true_iff. rewrite andb_true_iff. split.
    + intros [H1 [H2 H3]]. constructor.
      * apply (proj1 (IHt1 k)); exact H1.
      * apply (proj1 (IHt2 k)); exact H2.
      * apply (proj1 (IHt3 k)); exact H3.
    + intro H. inversion H; subst. split.
      * apply (proj2 (IHt1 k)); assumption.
      * split.
        -- apply (proj2 (IHt2 k)); assumption.
        -- apply (proj2 (IHt3 k)); assumption.
Qed.

Definition valueb (t : tm) : bool :=
  match t with
  | tm_abs _ t1 => lcb 1 t1
  | tm_true => true
  | tm_false => true
  | _ => false
  end.

Lemma valueb_spec : forall t, valueb t = true <-> value t.
Proof.
  intros t. destruct t as [n | x | a1 a2 | T0 b0 | | | c1 c2 c3]; simpl.
  - (* bvar *) split; intro H; [discriminate H | inversion H].
  - (* fvar *) split; intro H; [discriminate H | inversion H].
  - (* app *) split; intro H; [discriminate H | inversion H].
  - (* abs *) split; intro H.
    + apply v_abs. apply lc_abs. apply (proj1 (lcb_spec b0 1)); exact H.
    + inversion H; subst.
      apply (proj2 (lcb_spec b0 1)).
      match goal with
      | Hlc : locally_closed (tm_abs T0 b0) |- _ => inversion Hlc; assumption
      end.
  - (* true *) split; intro H; [apply v_true | reflexivity].
  - (* false *) split; intro H; [apply v_false | reflexivity].
  - (* if *) split; intro H; [discriminate H | inversion H].
Qed.

Lemma value_lc : forall v, value v -> lc_at 0 v.
Proof.
  intros v Hv. induction Hv.
  - exact H.
  - constructor.
  - constructor.
Qed.

Lemma value_no_step : forall v, value v -> forall v', ~ (v --> v').
Proof.
  intros v Hv. induction Hv; intros v' Hstep; inversion Hstep.
Qed.

(** *** Deciding values and stepping. *)

Lemma valueb_true : forall t, valueb t = true -> value t.
Proof. intros t H. exact (proj1 (valueb_spec t) H). Qed.

Lemma valueb_false : forall t, valueb t = false -> value t -> False.
Proof.
  intros t H Hv. apply (proj2 (valueb_spec t)) in Hv. rewrite Hv in H. discriminate H.
Qed.

Lemma lcb_true : forall t k, lcb k t = true -> lc_at k t.
Proof. intros t k H. exact (proj1 (lcb_spec t k) H). Qed.

Lemma lcb_false : forall t k, lcb k t = false -> lc_at k t -> False.
Proof.
  intros t k H Hc. apply (proj2 (lcb_spec t k)) in Hc. rewrite Hc in H. discriminate H.
Qed.

Lemma value_dec : forall t, { value t } + { value t -> False }.
Proof.
  intro t. destruct (valueb t) eqn:E.
  - left. apply valueb_true. exact E.
  - right. apply valueb_false. exact E.
Qed.

Lemma ty_eq_dec : forall (T1 T2 : ty), {T1 = T2} + {T1 <> T2}.
Proof. decide equality. Qed.

Lemma tm_eq_dec : forall (t1 t2 : tm), {t1 = t2} + {t1 <> t2}.
Proof. decide equality; try apply ty_eq_dec; try apply Nat.eq_dec. Qed.

(** *** Basic no-step facts. *)

Lemma lc_at_abs_inv : forall k T t, lc_at k (tm_abs T t) -> lc_at (S k) t.
Proof. intros k T t H; inversion H; assumption. Qed.

Lemma step_abs : forall T t s, tm_abs T t --> s -> False.
Proof. intros T t s H; inversion H. Qed.
Lemma step_bvar : forall i s, tm_bvar i --> s -> False.
Proof. intros i s H; inversion H. Qed.
Lemma step_fvar : forall x s, tm_fvar x --> s -> False.
Proof. intros x s H; inversion H. Qed.
Lemma step_true : forall s, tm_true --> s -> False.
Proof. intros s H; inversion H. Qed.
Lemma step_false : forall s, tm_false --> s -> False.
Proof. intros s H; inversion H. Qed.

Ltac ns_all :=
  try (exfalso; eapply value_no_step; eassumption);
  try (exfalso; match goal with Hn : (forall s : tm, ?a --> s -> False), Hs : ?a --> ?w |- _ => exact (Hn w Hs) end);
  try (exfalso; match goal with Hc : lc_at ?k ?t, Hn : (lc_at ?k ?t -> False) |- _ => exact (Hn Hc) end);
  try (exfalso; match goal with Hc : locally_closed ?t, Hn : (lc_at 0 ?t -> False) |- _ => exact (Hn Hc) end);
  try (exfalso; match goal with Hv : value ?v, Hn : (value ?v -> False) |- _ => exact (Hn Hv) end);
  try (exfalso; match goal with Hv : value ?v, Hn : (lc_at ?k ?v -> False) |- _ => exact (Hn (value_lc v Hv)) end);
  try (exfalso; match goal with Hlc : locally_closed (tm_abs ?T ?b), Hn : (value (tm_abs ?T ?b) -> False) |- _ => exact (Hn (v_abs T b Hlc)) end);
  try (exfalso; match goal with Hn : (value tm_true -> False) |- _ => exact (Hn v_true) end);
  try (exfalso; match goal with Hn : (value tm_false -> False) |- _ => exact (Hn v_false) end);
  try (exfalso; match goal with Hn : (value (tm_abs ?T ?b) -> False), Hc : locally_closed (tm_abs ?T ?b) |- _ => exact (Hn (v_abs T b Hc)) end);
  try (exfalso; match goal with Hs : tm_abs ?T ?b --> ?w |- _ => exact (step_abs T b w Hs) end);
  try (exfalso; match goal with Hs : tm_true --> ?w |- _ => exact (step_true w Hs) end);
  try (exfalso; match goal with Hs : tm_false --> ?w |- _ => exact (step_false w Hs) end);
  try (exfalso; match goal with Hs : tm_bvar ?i --> ?w |- _ => exact (step_bvar i w Hs) end);
  try (exfalso; match goal with Hs : tm_fvar ?x --> ?w |- _ => exact (step_fvar x w Hs) end);
  try (exfalso; match goal with Hn : (lc_at 0 ?a /\ lc_at 0 ?b -> False), Ha : locally_closed ?a, Hb : locally_closed ?b |- _ => exact (Hn (conj Ha Hb)) end);
  try (exfalso; match goal with Hn : (?a = ?a -> False) |- _ => exact (Hn eq_refl) end);
  try discriminate.

Lemma app_no_step : forall t1 t2,
  (forall s, t1 --> s -> False) -> (value t1 -> False) -> forall s, tm_app t1 t2 --> s -> False.
Proof. intros t1 t2 Hns1 Hnv1 s H. inversion H; subst. all: ns_all. Qed.

Lemma app_step_no_lc : forall t1 s1 t2,
  t1 --> s1 -> (lc_at 0 t2 -> False) -> forall s, tm_app t1 t2 --> s -> False.
Proof. intros t1 s1 t2 Hstep Hnlc s H. inversion H; subst. all: ns_all. Qed.

Lemma app_abs_no_step : forall T0 b0 t2,
  lc_at 0 (tm_abs T0 b0) -> (value t2 -> False) -> (forall s, t2 --> s -> False) ->
  forall s, tm_app (tm_abs T0 b0) t2 --> s -> False.
Proof. intros T0 b0 t2 Hlc Hnv Hns s H. inversion H; subst. all: ns_all. Qed.

Lemma app_abs_nolc_no_step : forall T0 b0 t2,
  (lc_at 0 (tm_abs T0 b0) -> False) -> forall s, tm_app (tm_abs T0 b0) t2 --> s -> False.
Proof. intros T0 b0 t2 Hnlc s H. inversion H; subst. all: ns_all. Qed.

Lemma app_true_no_step : forall t2,
  (forall s, t2 --> s -> False) -> forall s, tm_app tm_true t2 --> s -> False.
Proof. intros t2 Hns s H. inversion H; subst. all: ns_all. Qed.

Lemma app_false_no_step : forall t2,
  (forall s, t2 --> s -> False) -> forall s, tm_app tm_false t2 --> s -> False.
Proof. intros t2 Hns s H. inversion H; subst. all: ns_all. Qed.

Lemma if_no_step : forall t1 t2 t3,
  (forall s, t1 --> s -> False) -> (t1 = tm_true -> False) -> (t1 = tm_false -> False) ->
  forall s, tm_if t1 t2 t3 --> s -> False.
Proof. intros t1 t2 t3 Hns1 Ht Hf s H. inversion H; subst. all: ns_all. Qed.

Lemma if_step_no_lc2 : forall t1 s1 t2 t3,
  t1 --> s1 -> (lc_at 0 t2 -> False) -> forall s, tm_if t1 t2 t3 --> s -> False.
Proof. intros t1 s1 t2 t3 Hstep Hnlc s H. inversion H; subst. all: ns_all. Qed.

Lemma if_step_lc_no_lc3 : forall t1 s1 t2 t3,
  t1 --> s1 -> lc_at 0 t2 -> (lc_at 0 t3 -> False) -> forall s, tm_if t1 t2 t3 --> s -> False.
Proof. intros t1 s1 t2 t3 Hstep Hlc2 Hnlc s H. inversion H; subst. all: ns_all. Qed.

Lemma if_true_no_lc2 : forall t2 t3,
  (lc_at 0 t2 -> False) -> forall s, tm_if tm_true t2 t3 --> s -> False.
Proof. intros t2 t3 Hnlc s H. inversion H; subst. all: ns_all. Qed.

Lemma if_true_no_lc3 : forall t2 t3,
  lc_at 0 t2 -> (lc_at 0 t3 -> False) -> forall s, tm_if tm_true t2 t3 --> s -> False.
Proof. intros t2 t3 Hlc Hnlc s H. inversion H; subst. all: ns_all. Qed.

Lemma if_false_no_lc2 : forall t2 t3,
  (lc_at 0 t2 -> False) -> forall s, tm_if tm_false t2 t3 --> s -> False.
Proof. intros t2 t3 Hnlc s H. inversion H; subst. all: ns_all. Qed.

Lemma if_false_no_lc3 : forall t2 t3,
  lc_at 0 t2 -> (lc_at 0 t3 -> False) -> forall s, tm_if tm_false t2 t3 --> s -> False.
Proof. intros t2 t3 Hlc Hnlc s H. inversion H; subst. all: ns_all. Qed.

(** *** Determinism and decidability of the step relation. *)

Lemma step_det : forall t t1, t --> t1 -> forall t2, t --> t2 -> t1 = t2.
Proof.
  intros t t1 H.
  induction H as [T t0 v Hlc Hv
                | t1 a1 t2 Hstep IHHstep Hlc
                | v1 t2 t2' Hv Hstep IHHstep
                | t1 t2 Hlc1 Hlc2
                | t1 t2 Hlc1 Hlc2
                | t1 t1' t2 t3 Hstep IHHstep Hlc2 Hlc3];
    intros s Hs; inversion Hs; subst.
  - reflexivity.
  - exfalso. match goal with H' : tm_abs ?T ?b --> ?w |- _ => exact (step_abs T b w H') end.
  - exfalso. match goal with Hv' : value ?v, H' : ?v --> ?w |- _ => exact (value_no_step v Hv' w H') end.
  - exfalso. match goal with H' : tm_abs ?T ?b --> ?w |- _ => exact (step_abs T b w H') end.
  - apply (f_equal (fun x => tm_app x t2)). eapply IHHstep. eassumption.
  - exfalso. match goal with Hv' : value ?v, H' : ?v --> ?w |- _ => exact (value_no_step v Hv' w H') end.
  - exfalso. match goal with Hv' : value ?v, H' : ?v --> ?w |- _ => exact (value_no_step v Hv' w H') end.
  - exfalso. match goal with Hv' : value ?v, H' : ?v --> ?w |- _ => exact (value_no_step v Hv' w H') end.
  - apply (f_equal (fun x => tm_app v1 x)). eapply IHHstep. eassumption.
  - reflexivity.
  - exfalso. match goal with H' : tm_true --> ?w |- _ => exact (step_true w H') end.
  - reflexivity.
  - exfalso. match goal with H' : tm_false --> ?w |- _ => exact (step_false w H') end.
  - exfalso. match goal with H' : tm_true --> ?w |- _ => exact (step_true w H') end.
  - exfalso. match goal with H' : tm_false --> ?w |- _ => exact (step_false w H') end.
  - apply (f_equal (fun x => tm_if x t2 t3)). eapply IHHstep. eassumption.
Qed.

Lemma step_dec : forall t, { t' | t --> t' } + { forall t', t --> t' -> False }.
Proof.
  induction t as [n | x | a1 iha1 a2 iha2 | T0 b0 ihb0 | | | c1 ihc1 c2 ihc2 c3 ihc3].
  - right. intros s Hs. exact (step_bvar n s Hs).
  - right. intros s Hs. exact (step_fvar x s Hs).
  - destruct iha1 as [[s1 Hstep1] | Hnostep1].
    + destruct (lcb 0 a2) eqn:E2.
      * left. exists (tm_app s1 a2). apply ST_App1.
        -- exact Hstep1.
        -- apply lcb_true. exact E2.
      * right. intros s Hs. exact (app_step_no_lc a1 s1 a2 Hstep1 (lcb_false a2 0 E2) s Hs).
    + destruct (value_dec a1) as [Hv1 | Hnv1].
      * destruct a1 as [n1 | x1 | d1 d2 | T1 e1 | | | f1 f2 f3].
        -- exfalso. inversion Hv1.
        -- exfalso. inversion Hv1.
        -- exfalso. inversion Hv1.
        -- destruct (lcb 1 e1) eqn:E1.
           ++ destruct (value_dec a2) as [Hv2 | Hnv2].
              ** left. exists (open e1 a2). apply ST_AppAbs.
                 --- apply lcb_true. exact E1.
                 --- exact Hv2.
              ** destruct iha2 as [[s2 Hstep2] | Hnostep2].
                 --- left. exists (tm_app (tm_abs T1 e1) s2). apply ST_App2.
                     +++ apply v_abs. apply lc_abs. apply lcb_true. exact E1.
                     +++ exact Hstep2.
                 --- right. intros s Hs.
                     exact (app_abs_no_step T1 e1 a2
                              (lc_abs 0 T1 e1 (lcb_true e1 1 E1)) Hnv2 Hnostep2 s Hs).
           ++ right. intros s Hs.
              exact (app_abs_nolc_no_step T1 e1 a2
                       (fun Hc => lcb_false e1 1 E1 (lc_at_abs_inv 0 T1 e1 Hc)) s Hs).
        -- destruct iha2 as [[s2 Hstep2] | Hnostep2].
           ++ left. exists (tm_app tm_true s2). apply ST_App2.
              ** apply v_true.
              ** exact Hstep2.
           ++ right. intros s Hs. exact (app_true_no_step a2 Hnostep2 s Hs).
        -- destruct iha2 as [[s2 Hstep2] | Hnostep2].
           ++ left. exists (tm_app tm_false s2). apply ST_App2.
              ** apply v_false.
              ** exact Hstep2.
           ++ right. intros s Hs. exact (app_false_no_step a2 Hnostep2 s Hs).
        -- exfalso. inversion Hv1.
      * right. intros s Hs. exact (app_no_step a1 a2 Hnostep1 Hnv1 s Hs).
  - right. intros s Hs. exact (step_abs T0 b0 s Hs).
  - right. intros s Hs. exact (step_true s Hs).
  - right. intros s Hs. exact (step_false s Hs).
  - destruct (tm_eq_dec c1 tm_true) as [-> | Hnt].
    + destruct (lcb 0 c2) eqn:E2.
      * destruct (lcb 0 c3) eqn:E3.
        -- left. exists c2. apply ST_IfTrue.
           ++ apply lcb_true. exact E2.
           ++ apply lcb_true. exact E3.
        -- right. intros s Hs.
           exact (if_true_no_lc3 c2 c3 (lcb_true c2 0 E2) (lcb_false c3 0 E3) s Hs).
      * right. intros s Hs. exact (if_true_no_lc2 c2 c3 (lcb_false c2 0 E2) s Hs).
    + destruct (tm_eq_dec c1 tm_false) as [-> | Hnf].
      * destruct (lcb 0 c2) eqn:E2.
        -- destruct (lcb 0 c3) eqn:E3.
           ++ left. exists c3. apply ST_IfFalse.
              ** apply lcb_true. exact E2.
              ** apply lcb_true. exact E3.
           ++ right. intros s Hs.
              exact (if_false_no_lc3 c2 c3 (lcb_true c2 0 E2) (lcb_false c3 0 E3) s Hs).
        -- right. intros s Hs. exact (if_false_no_lc2 c2 c3 (lcb_false c2 0 E2) s Hs).
      * destruct ihc1 as [[s1 Hstep1] | Hnostep1].
        -- destruct (lcb 0 c2) eqn:E2.
           ++ destruct (lcb 0 c3) eqn:E3.
              ** left. exists (tm_if s1 c2 c3). apply ST_If.
                 --- exact Hstep1.
                 --- apply lcb_true. exact E2.
                 --- apply lcb_true. exact E3.
              ** right. intros s Hs.
                 exact (if_step_lc_no_lc3 c1 s1 c2 c3 Hstep1 (lcb_true c2 0 E2) (lcb_false c3 0 E3) s Hs).
           ++ right. intros s Hs.
              exact (if_step_no_lc2 c1 s1 c2 c3 Hstep1 (lcb_false c2 0 E2) s Hs).
        -- right. intros s Hs. exact (if_no_step c1 c2 c3 Hnostep1 Hnt Hnf s Hs).
Qed.


(** *** Local closure, opening and free-variable substitution. *)

Lemma lc_at_weaken : forall k t, lc_at k t -> forall k', k <= k' -> lc_at k' t.
Proof.
  intros k t H. induction H as [k i Hi | k x | k t1 t2 _ IH1 _ IH2
                               | k T t1 _ IH | k | k | k t1 t2 t3 _ IH1 _ IH2 _ IH3];
    intros k' Hle.
  - apply lc_bvar. lia.
  - apply lc_fvar.
  - apply lc_app; [apply IH1 | apply IH2]; lia.
  - apply lc_abs. apply IH. lia.
  - apply lc_true.
  - apply lc_false.
  - apply lc_if; [apply IH1 | apply IH2 | apply IH3]; lia.
Qed.

Lemma lc_at_zero : forall k t, lc_at 0 t -> lc_at k t.
Proof. intros k t H. apply (lc_at_weaken 0 t H k). lia. Qed.

Lemma open_rec_lc_at : forall t k j u, j <= k -> lc_at j t -> open_rec k u t = t.
Proof.
  induction t as [n | x | a1 iha1 a2 iha2 | T0 b0 ihb0 | | | c1 ihc1 c2 ihc2 c3 ihc3];
    intros k j u Hjk Hlc; simpl.
  - inversion Hlc; subst. destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. lia.
    + reflexivity.
  - reflexivity.
  - inversion Hlc; subst.
    assert (HA1 : open_rec k u a1 = a1) by (apply (iha1 k j u Hjk); assumption).
    assert (HA2 : open_rec k u a2 = a2) by (apply (iha2 k j u Hjk); assumption).
    rewrite HA1, HA2. reflexivity.
  - assert (H1 : open_rec (S k) u b0 = b0)
        by (apply (ihb0 (S k) (S j) u); [lia | inversion Hlc; assumption]).
    rewrite H1. reflexivity.
  - reflexivity.
  - reflexivity.
  - inversion Hlc; subst.
    assert (HC1 : open_rec k u c1 = c1) by (apply (ihc1 k j u Hjk); assumption).
    assert (HC2 : open_rec k u c2 = c2) by (apply (ihc2 k j u Hjk); assumption).
    assert (HC3 : open_rec k u c3 = c3) by (apply (ihc3 k j u Hjk); assumption).
    rewrite HC1, HC2, HC3. reflexivity.
Qed.

Lemma open_rec_lc : forall t k u, lc_at 0 t -> open_rec k u t = t.
Proof. intros t k u H. apply (open_rec_lc_at t k 0 u). lia. exact H. Qed.

Lemma lc_at_open_rec : forall t k u, lc_at (S k) t -> lc_at k u -> lc_at k (open_rec k u t).
Proof.
  induction t as [n | x | a1 iha1 a2 iha2 | T0 b0 ihb0 | | | c1 ihc1 c2 ihc2 c3 ihc3];
    intros k u Ht Hu; simpl.
  - inversion Ht; subst. destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. exact Hu.
    + apply Nat.eqb_neq in E. apply lc_bvar. lia.
  - apply lc_fvar.
  - inversion Ht; subst. apply lc_app; [apply iha1 | apply iha2]; assumption.
  - apply lc_abs. apply (ihb0 (S k) u).
    + inversion Ht; assumption.
    + apply (lc_at_weaken k u Hu (S k)). lia.
  - apply lc_true.
  - apply lc_false.
  - inversion Ht; subst. apply lc_if; [apply ihc1 | apply ihc2 | apply ihc3]; assumption.
Qed.

Lemma lc_at_open_rec_inv : forall t k u, lc_at k (open_rec k u t) -> lc_at (S k) t.
Proof.
  induction t as [n | x | a1 iha1 a2 iha2 | T0 b0 ihb0 | | | c1 ihc1 c2 ihc2 c3 ihc3];
    intros k u H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. apply lc_bvar. lia.
    + apply Nat.eqb_neq in E. inversion H; subst. apply lc_bvar. lia.
  - apply lc_fvar.
  - inversion H; subst. apply lc_app.
    + apply iha1 with u. assumption.
    + apply iha2 with u. assumption.
  - inversion H; subst. apply lc_abs. apply ihb0 with u. assumption.
  - apply lc_true.
  - apply lc_false.
  - inversion H; subst. apply lc_if.
    + apply ihc1 with u. assumption.
    + apply ihc2 with u. assumption.
    + apply ihc3 with u. assumption.
Qed.

(** *** Free-variable substitution. *)

Fixpoint subst (gamma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => gamma x
  | tm_app t1 t2 => tm_app (subst gamma t1) (subst gamma t2)
  | tm_abs T t1 => tm_abs T (subst gamma t1)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (subst gamma t1) (subst gamma t2) (subst gamma t3)
  end.

Definition update_tm (gamma : atom -> tm) (x : atom) (u : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then u else gamma y.

Definition lc_env (gamma : atom -> tm) : Prop := forall x, lc_at 0 (gamma x).

Lemma update_tm_eq : forall gamma x u, update_tm gamma x u x = u.
Proof. intros. unfold update_tm. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma update_tm_neq : forall gamma x y u, x <> y -> update_tm gamma x u y = gamma y.
Proof. intros. unfold update_tm. apply Nat.eqb_neq in H. rewrite H. reflexivity. Qed.

Lemma lc_env_update : forall gamma x u, lc_env gamma -> lc_at 0 u -> lc_env (update_tm gamma x u).
Proof.
  intros gamma x u Henv Hu y. unfold update_tm.
  destruct (Nat.eqb x y) eqn:E.
  - exact Hu.
  - apply Henv.
Qed.

Lemma lc_at_subst : forall t gamma k, lc_at k t -> lc_env gamma -> lc_at k (subst gamma t).
Proof.
  induction t as [n | x | a1 iha1 a2 iha2 | T0 b0 ihb0 | | | c1 ihc1 c2 ihc2 c3 ihc3];
    intros gamma k Hlc Henv; simpl.
  - exact Hlc.
  - apply lc_at_zero. apply Henv.
  - inversion Hlc; subst. apply lc_app; [apply iha1 | apply iha2]; assumption.
  - apply lc_abs. apply ihb0 with (k := S k); [inversion Hlc; assumption | exact Henv].
  - apply lc_true.
  - apply lc_false.
  - inversion Hlc; subst. apply lc_if; [apply ihc1 | apply ihc2 | apply ihc3]; assumption.
Qed.

Lemma subst_id : forall t, subst (fun x => tm_fvar x) t = t.
Proof.
  induction t as [n | x | a1 iha1 a2 iha2 | T0 b0 ihb0 | | | c1 ihc1 c2 ihc2 c3 ihc3]; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite iha1, iha2. reflexivity.
  - rewrite ihb0. reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite ihc1, ihc2, ihc3. reflexivity.
Qed.

Lemma subst_open_fvar : forall t gamma k x u,
  lc_env gamma -> ~ In x (fv t) ->
  subst (update_tm gamma x u) (open_rec k (tm_fvar x) t) = open_rec k u (subst gamma t).
Proof.
  induction t as [n | y | a1 iha1 a2 iha2 | T0 b0 ihb0 | | | c1 ihc1 c2 ihc2 c3 ihc3];
    intros gamma k x u Henv Hx; simpl.
  - destruct (Nat.eqb k n) eqn:E; simpl.
    + apply update_tm_eq.
    + reflexivity.
  - assert (Hne : x <> y).
    { intro Hc. apply Hx. subst. simpl. auto. }
    rewrite update_tm_neq by exact Hne.
    rewrite open_rec_lc; [reflexivity | apply Henv].
  - assert (Hx1 : ~ In x (fv a1)) by (apply (not_in_fv_app_l x a1 a2); exact Hx).
    assert (Hx2 : ~ In x (fv a2)) by (apply (not_in_fv_app_r x a1 a2); exact Hx).
    assert (HA1 : subst (update_tm gamma x u) (open_rec k (tm_fvar x) a1) = open_rec k u (subst gamma a1))
      by (apply (iha1 gamma k x u); [exact Henv | exact Hx1]).
    assert (HA2 : subst (update_tm gamma x u) (open_rec k (tm_fvar x) a2) = open_rec k u (subst gamma a2))
      by (apply (iha2 gamma k x u); [exact Henv | exact Hx2]).
    rewrite HA1, HA2. reflexivity.
  - rewrite ihb0; [reflexivity | exact Henv | exact Hx].
  - reflexivity.
  - reflexivity.
  - assert (Hx1 : ~ In x (fv c1)).
    { intro Hin. apply Hx. change (In x (fv c1 ++ fv c2 ++ fv c3)).
      apply in_or_app. left. exact Hin. }
    assert (Hx2 : ~ In x (fv c2)).
    { intro Hin. apply Hx. change (In x (fv c1 ++ fv c2 ++ fv c3)).
      apply in_or_app. right. apply in_or_app. left. exact Hin. }
    assert (Hx3 : ~ In x (fv c3)).
    { intro Hin. apply Hx. change (In x (fv c1 ++ fv c2 ++ fv c3)).
      apply in_or_app. right. apply in_or_app. right. exact Hin. }
    assert (HC1 : subst (update_tm gamma x u) (open_rec k (tm_fvar x) c1) = open_rec k u (subst gamma c1))
      by (apply (ihc1 gamma k x u); [exact Henv | exact Hx1]).
    assert (HC2 : subst (update_tm gamma x u) (open_rec k (tm_fvar x) c2) = open_rec k u (subst gamma c2))
      by (apply (ihc2 gamma k x u); [exact Henv | exact Hx2]).
    assert (HC3 : subst (update_tm gamma x u) (open_rec k (tm_fvar x) c3) = open_rec k u (subst gamma c3))
      by (apply (ihc3 gamma k x u); [exact Henv | exact Hx3]).
    rewrite HC1, HC2, HC3. reflexivity.
Qed.

(** *** Local closure under reduction and typing. *)

Lemma lc_step : forall t t', lc_at 0 t -> t --> t' -> lc_at 0 t'.
Proof.
  intros t t' Hlc Hstep. revert Hlc. induction Hstep as
    [T t0 v Hlc0 Hv
    | t1 t1' t2 Hstep1 IH1 Hlc2
    | v1 t2 t2' Hv Hstep2 IH2
    | t1 t2 Hlc1 Hlc2
    | t1 t2 Hlc1 Hlc2
    | t1 t1' t2 t3 Hstep1 IH1 Hlc2 Hlc3];
    intros Hlc.
  - simpl. inversion Hlc; subst.
    apply lc_at_open_rec with (k := 0).
    + apply lc_at_abs_inv with (T := T). assumption.
    + apply value_lc. exact Hv.
  - simpl in Hlc. inversion Hlc; subst. apply lc_app.
    + apply IH1. assumption.
    + assumption.
  - simpl in Hlc. inversion Hlc; subst. apply lc_app.
    + assumption.
    + apply IH2. assumption.
  - simpl in Hlc. inversion Hlc; subst. assumption.
  - simpl in Hlc. inversion Hlc; subst. assumption.
  - simpl in Hlc. inversion Hlc; subst. apply lc_if.
    + apply IH1. assumption.
    + assumption.
    + assumption.
Qed.

Lemma has_type_lc : forall Gamma t T, has_type Gamma t T -> lc_at 0 t.
Proof.
  intros Gamma t T H. induction H as
    [Gamma x T Hlookup
    | L Gamma T1 T2 t1 Hbody IHbody
    | Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
    | Gamma
    | Gamma
    | Gamma t1 t2 t3 T H1 IH1 H2 IH2 H3 IH3].
  - apply lc_fvar.
  - apply lc_abs.
    pose (x := fresh (L ++ fv t1)).
    assert (Hx : ~ In x L).
    { intro Hc. apply (fresh_not_in (L ++ fv t1)). apply in_or_app. left. exact Hc. }
    apply (lc_at_open_rec_inv t1 0 (tm_fvar x)).
    apply IHbody. exact Hx.
  - apply lc_app; assumption.
  - apply lc_true.
  - apply lc_false.
  - apply lc_if; assumption.
Qed.


(** *** The type-indexed logical relation. *)

Fixpoint LR (T : ty) (t : tm) : Prop :=
  match T with
  | Ty_Bool => strongly_normalizing t /\ lc_at 0 t
  | Ty_Arrow T1 T2 =>
      strongly_normalizing t /\ lc_at 0 t /\
      (forall u, LR T1 u -> LR T2 (tm_app t u))
  end.

Definition env_ok (Gamma : context) (gamma : atom -> tm) : Prop :=
  lc_env gamma /\ (forall x T, Gamma x = Some T -> LR T (gamma x)).

Lemma LR_SN : forall T t, LR T t -> strongly_normalizing t.
Proof.
  intros T. induction T; intros t H; simpl in H; exact (proj1 H).
Qed.

Lemma LR_lc : forall T t, LR T t -> lc_at 0 t.
Proof.
  intros T. induction T; intros t H; simpl in H.
  - exact (proj2 H).
  - exact (proj1 (proj2 H)).
Qed.

Lemma LR_step : forall T t t', LR T t -> t --> t' -> LR T t'.
Proof.
  intros T. induction T as [| A IHA B IHB]; intros t t' HLR Hstep; simpl in *.
  - destruct HLR as [HSN Hlc]. split.
    + destruct HSN as [t0 Hred]. exact (Hred t' Hstep).
    + apply lc_step with t; assumption.
  - destruct HLR as [HSN [Hlc Harr]]. split.
    + destruct HSN as [t0 Hred]. exact (Hred t' Hstep).
    + split.
      * apply lc_step with t; assumption.
      * intros u Hu. apply (IHB (tm_app t u) (tm_app t' u)).
        -- apply Harr. exact Hu.
        -- apply ST_App1; [exact Hstep | exact (LR_lc _ _ Hu)].
Qed.

Lemma LR_back : forall T t t', lc_at 0 t -> t --> t' -> LR T t' -> LR T t.
Proof.
  intros T. induction T as [| A IHA B IHB]; intros t t' Hlc Hstep HLR; simpl in *.
  - destruct HLR as [HSN Hlc']. split.
    + apply SN_intro. intros s Hs.
      assert (Heq : t' = s) by (apply (step_det t t' Hstep s); exact Hs).
      subst s. exact HSN.
    + exact Hlc.
  - destruct HLR as [HSN [Hlc' Harr]]. split.
    + apply SN_intro. intros s Hs.
      assert (Heq : t' = s) by (apply (step_det t t' Hstep s); exact Hs).
      subst s. exact HSN.
    + split.
      * exact Hlc.
      * intros u Hu. apply (IHB (tm_app t u) (tm_app t' u)).
        -- apply lc_app; [exact Hlc | exact (LR_lc _ _ Hu)].
        -- apply ST_App1; [exact Hstep | exact (LR_lc _ _ Hu)].
        -- apply Harr. exact Hu.
Qed.

Lemma LR_stuck : forall T t,
  lc_at 0 t -> (value t -> False) -> (forall t', t --> t' -> False) -> LR T t.
Proof.
  intros T. induction T as [| A IHA B IHB]; intros t Hlc Hnv Hns; simpl.
  - split.
    + apply SN_intro. intros s Hs. exfalso. exact (Hns s Hs).
    + exact Hlc.
  - split.
    + apply SN_intro. intros s Hs. exfalso. exact (Hns s Hs).
    + split.
      * exact Hlc.
      * intros u Hu. apply IHB.
        -- apply lc_app; [exact Hlc | exact (LR_lc _ _ Hu)].
        -- intro Hv. inversion Hv.
        -- intros s Hs. inversion Hs; subst. all: ns_all.
Qed.

Lemma LR_abs_app : forall A B body u,
  lc_at 0 (tm_abs A body) ->
  (forall v, LR A v -> LR B (open body v)) ->
  LR A u ->
  LR B (tm_app (tm_abs A body) u).
Proof.
  intros A B body u Hlc Hprem Hu.
  assert (HSN : strongly_normalizing u) by (apply (LR_SN A); exact Hu).
  revert Hu.
  induction HSN as [u Hred IHu]; intros Hu.
  destruct (value_dec u) as [Hv | Hnv].
  - apply LR_back with (t' := open body u).
    + apply lc_app; [exact Hlc | exact (LR_lc _ _ Hu)].
    + apply ST_AppAbs; [exact Hlc | exact Hv].
    + apply Hprem. exact Hu.
  - destruct (step_dec u) as [[u' Hstep] | Hnostep].
    + apply LR_back with (t' := tm_app (tm_abs A body) u').
      * apply lc_app; [exact Hlc | exact (LR_lc _ _ Hu)].
      * apply ST_App2; [apply v_abs; exact Hlc | exact Hstep].
      * apply IHu; [exact Hstep | apply LR_step with u; assumption].
    + apply LR_stuck with (t := tm_app (tm_abs A body) u).
      * apply lc_app; [exact Hlc | exact (LR_lc _ _ Hu)].
      * intro Hv. inversion Hv.
      * intros s Hs. inversion Hs; subst. all: ns_all.
Qed.

Lemma LR_if : forall T b t2 t3,
  LR Ty_Bool b -> LR T t2 -> LR T t3 -> LR T (tm_if b t2 t3).
Proof.
  intros T b t2 t3 Hb H2 H3.
  assert (HSN : strongly_normalizing b) by (apply (LR_SN Ty_Bool); exact Hb).
  revert Hb.
  induction HSN as [b Hred IHb]; intros Hb.
  destruct (value_dec b) as [Hv | Hnv].
  - destruct Hv as [T0 b0 Hlcb | | ].
    + apply LR_stuck with (t := tm_if (tm_abs T0 b0) t2 t3).
      * apply lc_if; [apply lc_abs; apply (lc_at_abs_inv 0 T0 b0); exact Hlcb | exact (LR_lc _ _ H2) | exact (LR_lc _ _ H3)].
      * intro Hv'. inversion Hv'.
      * intros s Hs. inversion Hs; subst. all: ns_all.
    + apply LR_back with (t' := t2).
      * apply lc_if; [apply lc_true | exact (LR_lc _ _ H2) | exact (LR_lc _ _ H3)].
      * apply ST_IfTrue; [exact (LR_lc _ _ H2) | exact (LR_lc _ _ H3)].
      * exact H2.
    + apply LR_back with (t' := t3).
      * apply lc_if; [apply lc_false | exact (LR_lc _ _ H2) | exact (LR_lc _ _ H3)].
      * apply ST_IfFalse; [exact (LR_lc _ _ H2) | exact (LR_lc _ _ H3)].
      * exact H3.
  - destruct (step_dec b) as [[b' Hstep] | Hnostep].
    + apply LR_back with (t' := tm_if b' t2 t3).
      * apply lc_if; [exact (LR_lc _ _ Hb) | exact (LR_lc _ _ H2) | exact (LR_lc _ _ H3)].
      * apply ST_If; [exact Hstep | exact (LR_lc _ _ H2) | exact (LR_lc _ _ H3)].
      * apply IHb; [exact Hstep | apply LR_step with b; assumption].
    + apply LR_stuck with (t := tm_if b t2 t3).
      * apply lc_if; [exact (LR_lc _ _ Hb) | exact (LR_lc _ _ H2) | exact (LR_lc _ _ H3)].
      * intro Hv'. inversion Hv'.
      * intros s Hs. inversion Hs; subst. all: ns_all.
Qed.

Lemma env_ok_update : forall Gamma gamma x T u,
  env_ok Gamma gamma -> LR T u -> env_ok (update Gamma x T) (update_tm gamma x u).
Proof.
  intros Gamma gamma x T u [Hlc Hty] Hu. split.
  - intros y. unfold update_tm. destruct (Nat.eqb x y) eqn:E.
    + exact (LR_lc _ _ Hu).
    + apply Hlc.
  - intros y T' Hy. unfold update_tm. destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst y. unfold update in Hy. rewrite Nat.eqb_refl in Hy.
      injection Hy as ->. exact Hu.
    + unfold update in Hy. rewrite E in Hy. apply Hty with (x := y). exact Hy.
Qed.

(** *** The fundamental theorem. *)

Lemma fundamental : forall Gamma t T, has_type Gamma t T ->
  forall gamma, env_ok Gamma gamma -> LR T (subst gamma t).
Proof.
  intros Gamma t T H. induction H as
    [Gamma x T Hlookup
    | L Gamma T1 T2 t1 Hbody IHbody
    | Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
    | Gamma
    | Gamma
    | Gamma t1 t2 t3 T H1 IH1 H2 IH2 H3 IH3].
  - intros gamma Henv. simpl. destruct Henv as [Hlcenv Htyenv].
    apply Htyenv with (x := x). exact Hlookup.
  - intros gamma Henv. simpl. destruct Henv as [Hlcenv Htyenv].
    pose (x := fresh (L ++ fv t1)).
    assert (HxL : ~ In x L).
    { intro Hc. apply (fresh_not_in (L ++ fv t1)). apply in_or_app. left. exact Hc. }
    assert (Hxfv : ~ In x (fv t1)).
    { intro Hc. apply (fresh_not_in (L ++ fv t1)). apply in_or_app. right. exact Hc. }
    assert (Hlcb : lc_at 1 t1).
    { apply (lc_at_open_rec_inv t1 0 (tm_fvar x)).
      apply (has_type_lc (update Gamma x T1) (open t1 (tm_fvar x)) T2).
      apply Hbody. exact HxL. }
    assert (Hlcabs : lc_at 0 (tm_abs T1 (subst gamma t1))).
    { apply lc_abs. apply lc_at_subst with (gamma := gamma); [exact Hlcb | exact Hlcenv]. }
    split.
    + apply SN_intro. intros s Hs. inversion Hs.
    + split.
      * exact Hlcabs.
      * intros u Hu.
        apply LR_abs_app with (A := T1) (B := T2) (body := subst gamma t1) (u := u).
        -- exact Hlcabs.
        -- intros v Hv.
           assert (Hbody_v : LR T2 (subst (update_tm gamma x v) (open t1 (tm_fvar x)))).
           { apply IHbody. exact HxL. split.
             - apply lc_env_update; [exact Hlcenv | exact (LR_lc _ _ Hv)].
             - intros y Ty Hupd. unfold update_tm. destruct (Nat.eqb x y) eqn:E.
               + apply Nat.eqb_eq in E. subst y. unfold update in Hupd.
                 rewrite Nat.eqb_refl in Hupd. injection Hupd as ->. exact Hv.
               + unfold update in Hupd. rewrite E in Hupd. apply Htyenv with (x := y). exact Hupd. }
           unfold open in Hbody_v. fold open in Hbody_v.
           rewrite subst_open_fvar in Hbody_v.
           ++ exact Hbody_v.
           ++ exact Hlcenv.
           ++ exact Hxfv.
        -- exact Hu.
  - intros gamma Henv. simpl. apply IH1 in Henv as H.
    destruct H as [HSN [Hlc Harr]]. apply Harr. apply IH2. exact Henv.
  - intros gamma Henv. simpl. split.
    + apply SN_intro. intros s Hs. inversion Hs.
    + apply lc_true.
  - intros gamma Henv. simpl. split.
    + apply SN_intro. intros s Hs. inversion Hs.
    + apply lc_false.
  - intros gamma Henv. simpl. apply LR_if.
    + apply IH1. exact Henv.
    + apply IH2. exact Henv.
    + apply IH3. exact Henv.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  assert (Hlr : LR T (subst (fun x => tm_fvar x) t)).
  { apply (fundamental empty t T Hty). split.
    - intro x. apply lc_fvar.
    - intros x Ty Hx. unfold empty in Hx. discriminate Hx. }
  rewrite subst_id in Hlr.
  exact (LR_SN T t Hlr).
Qed.

End STLCCBVNormalizationTask.
