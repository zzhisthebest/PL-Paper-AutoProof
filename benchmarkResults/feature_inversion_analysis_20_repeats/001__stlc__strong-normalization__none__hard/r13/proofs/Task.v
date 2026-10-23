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

(** * Strong normalization proof *)

(** We use a Tait-style reducibility relation [C T t] on terms that may
    contain free variables.  It is defined by recursion on the type:
    at [Bool] it is local closure plus strong normalization; at an
    arrow type it additionally requires that the term be reducible
    after application to any reducible argument.

    The proof rests on two closure properties of [C]:
      - forward closure under the one-step relation, and
      - "neutral expansion": a locally closed term that is not a value
        and all of whose one-step reducts are reducible is reducible.
    The second property is what makes call-by-value work: a beta-redex
    whose argument is not yet a value is not a value itself, so it can
    be handled by expansion; once the argument reaches a value, the
    beta-reduct is reducible by the abstraction hypothesis. *)

(** ** Fresh atoms from a finite list *)

Fixpoint fresh_bound (L : list atom) : atom :=
  match L with
  | nil => 0
  | x :: xs => Nat.max x (fresh_bound xs)
  end.

Definition fresh_atom (L : list atom) : atom := S (fresh_bound L).

Lemma fresh_bound_ge : forall L x, In x L -> x <= fresh_bound L.
Proof.
  induction L as [| y ys IH]; intros x Hin.
  - destruct Hin.
  - simpl in Hin. destruct Hin as [-> | Hin].
    + apply Nat.le_max_l.
    + apply Nat.le_trans with (fresh_bound ys); [apply IH; exact Hin | apply Nat.le_max_r].
Qed.

Lemma fresh_atom_notin : forall L, ~ In (fresh_atom L) L.
Proof.
  intros L Hin. unfold fresh_atom in Hin.
  pose proof (fresh_bound_ge L (S (fresh_bound L)) Hin). lia.
Qed.

(** ** Free variables, environments and substitution *)

Fixpoint fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ => nil
  | tm_fvar x => x :: nil
  | tm_app t1 t2 => fv t1 ++ fv t2
  | tm_abs _ t1 => fv t1
  | tm_true => nil
  | tm_false => nil
  end.

Definition upd_env (theta : atom -> tm) (x : atom) (v : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then v else theta y.

Definition lc_env (theta : atom -> tm) : Prop :=
  forall x, lc_at 0 (theta x).

Fixpoint subst_tm (theta : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => theta x
  | tm_app t1 t2 => tm_app (subst_tm theta t1) (subst_tm theta t2)
  | tm_abs T t1 => tm_abs T (subst_tm theta t1)
  | tm_true => tm_true
  | tm_false => tm_false
  end.

Lemma subst_tm_id : forall t, subst_tm (fun x => tm_fvar x) t = t.
Proof. induction t; simpl; congruence. Qed.

Lemma upd_env_eq : forall theta x v, upd_env theta x v x = v.
Proof.
  intros. unfold upd_env. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma upd_env_neq : forall theta x y v, x <> y -> upd_env theta x v y = theta y.
Proof.
  intros theta x y v H. unfold upd_env.
  destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. subst y. exfalso. exact (H eq_refl).
  - reflexivity.
Qed.

(** ** Local closure lemmas *)

Lemma lc_at_mono : forall k k' t, k <= k' -> lc_at k t -> lc_at k' t.
Proof.
  intros k k' t Hle H. revert k' Hle.
  induction H as [k i Hi | k x | k a b Ha IHa Hb IHb | k T b Hb IHb | k | k];
    intros k' Hle.
  - apply lc_bvar. lia.
  - apply lc_fvar.
  - apply lc_app.
    + exact (IHa k' Hle).
    + exact (IHb k' Hle).
  - apply lc_abs. apply IHb. lia.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma lc_at_open_rec_id : forall k v t, lc_at k t -> open_rec k v t = t.
Proof.
  intros k v t. revert k v.
  induction t as [n | x | t1 IH1 t2 IH2 | T t1 IH1 | | ]; intros k v H.
  - cbn [open_rec]. inversion H; subst. destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. exfalso. lia.
    + reflexivity.
  - cbn [open_rec]. reflexivity.
  - cbn [open_rec]. inversion H; subst. f_equal.
    + apply IH1. assumption.
    + apply IH2. assumption.
  - cbn [open_rec]. inversion H; subst. f_equal.
    apply IH1 with (k := S k) (v := v). assumption.
  - cbn [open_rec]. reflexivity.
  - cbn [open_rec]. reflexivity.
Qed.

Lemma lc_at_open_inv : forall k u t, lc_at k (open_rec k u t) -> lc_at (S k) t.
Proof.
  intros k u t. revert k u.
  induction t as [n | x | t1 IH1 t2 IH2 | T t1 IH1 | | ]; intros k u H.
  - cbn [open_rec] in H. destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. apply lc_bvar. lia.
    + inversion H; subst. apply lc_bvar. lia.
  - cbn [open_rec] in H. inversion H; subst. apply lc_fvar.
  - cbn [open_rec] in H. inversion H; subst. apply lc_app.
    + apply IH1 with (k := k) (u := u). assumption.
    + apply IH2 with (k := k) (u := u). assumption.
  - cbn [open_rec] in H. inversion H; subst. apply lc_abs.
    apply IH1 with (k := S k) (u := u). assumption.
  - cbn [open_rec] in H. inversion H; subst. apply lc_true.
  - cbn [open_rec] in H. inversion H; subst. apply lc_false.
Qed.

Lemma lc_at_open : forall k t, lc_at (S k) t -> forall u, lc_at k u -> lc_at k (open_rec k u t).
Proof.
  intros k t. revert k.
  induction t as [n | x | t1 IH1 t2 IH2 | T t1 IH1 | | ]; intros k H u Hu.
  - cbn [open_rec]. destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. exact Hu.
    + inversion H; subst. apply lc_bvar.
      destruct (Nat.lt_ge_cases n k) as [Hlt | Hge].
      * exact Hlt.
      * exfalso. apply Nat.eqb_neq in E.
        assert (Hnk : n = k).
        { apply Nat.le_antisymm.
          - apply (proj1 (Nat.lt_succ_r n k)). assumption.
          - exact Hge. }
        exact (E (eq_sym Hnk)).
  - cbn [open_rec]. apply lc_fvar.
  - cbn [open_rec]. inversion H; subst. apply lc_app.
    + apply IH1 with (k := k). assumption. exact Hu.
    + apply IH2 with (k := k). assumption. exact Hu.
  - cbn [open_rec]. inversion H; subst. apply lc_abs.
    apply IH1 with (k := S k).
    + assumption.
    + exact (lc_at_mono k (S k) u (Nat.le_succ_diag_r k) Hu).
  - cbn [open_rec]. apply lc_true.
  - cbn [open_rec]. apply lc_false.
Qed.

Lemma lc_at_subst : forall t theta k,
  lc_at k t -> lc_env theta -> lc_at k (subst_tm theta t).
Proof.
  intros t theta k. revert theta k.
  induction t as [n | x | t1 IH1 t2 IH2 | T t1 IH1 | | ];
    intros theta k H Hlc.
  - cbn [subst_tm]. inversion H; subst. apply lc_bvar. assumption.
  - cbn [subst_tm]. exact (lc_at_mono 0 k (theta x) (Nat.le_0_l k) (Hlc x)).
  - cbn [subst_tm]. inversion H; subst. apply lc_app.
    + apply IH1; assumption.
    + apply IH2; assumption.
  - cbn [subst_tm]. inversion H; subst. apply lc_abs.
    apply IH1 with (k := S k); assumption.
  - cbn [subst_tm]. apply lc_true.
  - cbn [subst_tm]. apply lc_false.
Qed.

(** ** Inversion lemmas for local closure and values *)

Lemma lc_at_app_inv : forall k t1 t2,
  lc_at k (tm_app t1 t2) -> lc_at k t1 /\ lc_at k t2.
Proof. intros k t1 t2 H. inversion H. split; assumption. Qed.

Lemma lc_at_abs_inv : forall k T t, lc_at k (tm_abs T t) -> lc_at (S k) t.
Proof. intros k T t H. inversion H. assumption. Qed.

Lemma value_abs : forall T body, lc_at 1 body -> value (tm_abs T body).
Proof.
  intros T body H. apply v_abs. unfold locally_closed.
  apply lc_abs with (k := 0). exact H.
Qed.

Lemma value_lc : forall v, value v -> lc_at 0 v.
Proof.
  intros v H. induction H as [T body Hlc | | ].
  - unfold locally_closed in Hlc. exact Hlc.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma value_no_step : forall v, value v -> forall t', ~ step v t'.
Proof.
  intros v H. induction H as [T body Hlc | | ]; intros t' Hs; inversion Hs.
Qed.

(** ** Reduction lemmas *)

Lemma lc_at_step : forall t t', step t t' -> lc_at 0 t -> lc_at 0 t'.
Proof.
  intros t t' H. induction H as [T body v Hlcabs Hval
                                | t1 t1' t2 Hstep12 IH12 Hlct2
                                | v1 t2 t2' Hval Hstep22 IH22]; intros Hlc.
  - destruct (lc_at_app_inv 0 (tm_abs T body) v Hlc) as [H1 H2].
    apply lc_at_open with (k := 0).
    + apply lc_at_abs_inv with (k := 0) (T := T). exact H1.
    + exact H2.
  - destruct (lc_at_app_inv 0 t1 t2 Hlc) as [H1 H2].
    apply lc_app.
    + apply IH12. exact H1.
    + exact H2.
  - destruct (lc_at_app_inv 0 v1 t2 Hlc) as [H1 H2].
    apply lc_app.
    + exact H1.
    + apply IH22. exact H2.
Qed.

Lemma SN_step : forall t, strongly_normalizing t ->
  forall t', step t t' -> strongly_normalizing t'.
Proof.
  intros t Hsn. induction Hsn as [t0 Hreds IH]. exact Hreds.
Qed.

Lemma SN_abs : forall T body, strongly_normalizing (tm_abs T body).
Proof.
  intros. apply SN_intro. intros t' Hs. inversion Hs.
Qed.

Lemma SN_true : strongly_normalizing tm_true.
Proof. apply SN_intro. intros t' Hs. inversion Hs. Qed.

Lemma SN_false : strongly_normalizing tm_false.
Proof. apply SN_intro. intros t' Hs. inversion Hs. Qed.

(** A complete inversion principle for steps of an application. *)
Lemma step_app_inv : forall a b c,
  step (tm_app a b) c ->
  (exists T body v, a = tm_abs T body /\ b = v /\ c = open body v /\ value v)
  \/ (exists a', c = tm_app a' b /\ step a a')
  \/ (exists b', c = tm_app a b' /\ value a /\ step b b').
Proof.
  intros a b c H. inversion H; subst; eauto 10.
Qed.

(** ** Substitution commutes with opening a fresh variable *)

Lemma subst_open_rec : forall k t theta v x,
  ~ In x (fv t) ->
  (forall y, In y (fv t) -> lc_at 0 (theta y)) ->
  subst_tm (upd_env theta x v) (open_rec k (tm_fvar x) t)
    = open_rec k v (subst_tm theta t).
Proof.
  intros k t theta v x. revert k theta v x.
  induction t as [n | y | t1 IH1 t2 IH2 | T t1 IH1 | | ];
    intros k theta v x Hfresh Hlc.
  - cbn [open_rec]. destruct (Nat.eqb k n) eqn:E.
    + cbn [subst_tm open_rec]. rewrite upd_env_eq. rewrite E. reflexivity.
    + cbn [subst_tm open_rec]. rewrite E. reflexivity.
  - cbn [open_rec subst_tm]. unfold upd_env.
    destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst y. exfalso. apply Hfresh.
      simpl. left. reflexivity.
    + symmetry. apply lc_at_open_rec_id.
      exact (lc_at_mono 0 k (theta y) (Nat.le_0_l k) (Hlc y (or_introl eq_refl))).
  - cbn [open_rec subst_tm]. f_equal.
    + apply IH1 with (k := k) (theta := theta) (v := v) (x := x).
      * intro Hi. apply Hfresh. apply in_or_app. left. exact Hi.
      * intros y Hy. apply Hlc. apply in_or_app. left. exact Hy.
    + apply IH2 with (k := k) (theta := theta) (v := v) (x := x).
      * intro Hi. apply Hfresh. apply in_or_app. right. exact Hi.
      * intros y Hy. apply Hlc. apply in_or_app. right. exact Hy.
  - cbn [open_rec subst_tm]. f_equal.
    apply IH1 with (k := S k) (theta := theta) (v := v) (x := x).
    + exact Hfresh.
    + exact Hlc.
  - cbn [open_rec subst_tm]. reflexivity.
  - cbn [open_rec subst_tm]. reflexivity.
Qed.

(** ** The reducibility relation *)

Fixpoint C (T : ty) (t : tm) : Prop :=
  match T with
  | Ty_Bool => lc_at 0 t /\ strongly_normalizing t
  | Ty_Arrow A B =>
      lc_at 0 t /\ strongly_normalizing t /\
      (forall u, C A u -> C B (tm_app t u))
  end.

Lemma C_lc : forall T t, C T t -> lc_at 0 t.
Proof.
  intros T t H. destruct T; simpl in H; tauto.
Qed.

Lemma C_sn : forall T t, C T t -> strongly_normalizing t.
Proof.
  intros T t H. destruct T; simpl in H; tauto.
Qed.

Lemma C_app : forall A B t, C (Ty_Arrow A B) t ->
  forall u, C A u -> C B (tm_app t u).
Proof.
  intros A B t H u Hu. simpl in H.
  destruct H as [H1 [H2 H3]]. apply H3. exact Hu.
Qed.

(** Forward closure under reduction. *)
Lemma C_step : forall T t t', C T t -> step t t' -> C T t'.
Proof.
  induction T as [| A IHA B IHB]; intros t t' HC Hstep.
  - simpl in HC. destruct HC as [Hlc Hsn]. simpl. split.
    + exact (lc_at_step t t' Hstep Hlc).
    + exact (SN_step t Hsn t' Hstep).
  - simpl in HC. destruct HC as [Hlc [Hsn Happ]]. simpl. split.
    + exact (lc_at_step t t' Hstep Hlc).
    + split.
      * exact (SN_step t Hsn t' Hstep).
      * intros u Hu.
        apply (IHB (tm_app t u) (tm_app t' u)).
        -- apply Happ. exact Hu.
        -- apply ST_App1. exact Hstep. apply C_lc with (T := A). exact Hu.
Qed.

(** Neutral expansion. *)
Lemma C_neutral : forall T t,
  lc_at 0 t ->
  (forall t', step t t' -> C T t') ->
  ~ value t ->
  C T t.
Proof.
  induction T as [| A IHA B IHB]; intros t Hlc Hreds Hnv; simpl.
  - split.
    + exact Hlc.
    + apply SN_intro. intros t' Hs.
      exact (C_sn Ty_Bool t' (Hreds t' Hs)).
  - split.
    + exact Hlc.
    + split.
      * apply SN_intro. intros t' Hs.
        exact (C_sn (Ty_Arrow A B) t' (Hreds t' Hs)).
      * intros u Hu.
        apply IHB.
        -- apply lc_app. exact Hlc. apply C_lc with (T := A). exact Hu.
        -- intros t2' Hs.
           destruct (step_app_inv t u t2' Hs) as
             [ [Tbody [body [v [Ha [Hb [Hc Hval]]]]]]
             | [ [a' [Hc Hstep_a]] | [b' [Hc [Hval_a Hstep_b]]] ] ].
           ++ (* the function part is an abstraction, contradicting ~value t *)
              exfalso. apply Hnv. rewrite Ha. apply v_abs.
              rewrite Ha in Hlc. exact Hlc.
           ++ (* the function part reduces *)
              rewrite Hc.
              exact (C_app A B a' (Hreds a' Hstep_a) u Hu).
           ++ (* the argument reduces, but t is not a value *)
              exfalso. exact (Hnv Hval_a).
        -- intro Hv. inversion Hv.
Qed.

(** Beta-expansion: a beta-redex whose body opens to reducible terms
    (for every reducible argument) is itself reducible.  The induction
    is on the strong normalization derivation of the argument; the
    neutral-expansion lemma takes care of the application shape. *)
Lemma C_beta_aux : forall u, strongly_normalizing u ->
  forall A B body,
    lc_at 1 body ->
    (forall v, C A v -> C B (open body v)) ->
    C A u ->
    C B (tm_app (tm_abs A body) u).
Proof.
  intros u Hsn. induction Hsn as [u Hreds IH].
  intros A B body Hlc Hbody Hu.
  apply C_neutral with (T := B) (t := tm_app (tm_abs A body) u).
  - apply lc_app.
    + unfold locally_closed. apply lc_abs with (k := 0). exact Hlc.
    + apply C_lc with (T := A). exact Hu.
  - intros t' Hs.
    destruct (step_app_inv (tm_abs A body) u t' Hs) as
      [ [Tbody [body' [v [Ha [Hb [Hc Hval]]]]]]
      | [ [a' [Hc Hstep_a]] | [b' [Hc [Hval_a Hstep_b]]] ] ].
    + injection Ha as HA Hbod. subst Tbody. subst body'.
      subst v. rewrite Hc. apply Hbody. exact Hu.
    + exfalso.
      exact (value_no_step (tm_abs A body) (value_abs A body Hlc) a' Hstep_a).
    + rewrite Hc.
      apply (IH b' Hstep_b A B body Hlc Hbody).
      exact (C_step A u b' Hu Hstep_b).
  - intro Hv. inversion Hv.
Qed.

Lemma C_beta : forall A B body u,
  lc_at 1 body ->
  (forall v, C A v -> C B (open body v)) ->
  C A u ->
  C B (tm_app (tm_abs A body) u).
Proof.
  intros A B body u Hlc Hbody Hu.
  exact (C_beta_aux u (C_sn A u Hu) A B body Hlc Hbody Hu).
Qed.

(** ** Typing implies local closure *)

Lemma has_type_lc : forall Gamma t T, has_type Gamma t T -> lc_at 0 t.
Proof.
  intros Gamma t T Hty.
  induction Hty as
    [ Gamma x T Hx
    | L Gamma T1 T2 t1 Hpre IHpre
    | Gamma t1 t2 T1 T2 Ht1 IH1 Ht2 IH2
    | Gamma
    | Gamma ].
  - apply lc_fvar.
  - apply lc_abs.
    apply lc_at_open_inv with (k := 0) (u := tm_fvar (fresh_atom L)).
    exact (IHpre (fresh_atom L) (fresh_atom_notin L)).
  - apply lc_app; assumption.
  - apply lc_true.
  - apply lc_false.
Qed.

(** ** Context / substitution interpretation and the fundamental lemma *)

Definition sat (Gamma : context) (theta : atom -> tm) : Prop :=
  forall x T, Gamma x = Some T -> C T (theta x).

Lemma fundamental : forall Gamma t T,
  has_type Gamma t T ->
  forall theta, lc_env theta -> sat Gamma theta -> C T (subst_tm theta t).
Proof.
  intros Gamma t T Hty.
  induction Hty as
    [ Gamma x T Hx
    | L Gamma T1 T2 t1 Hpre IHpre
    | Gamma t1 t2 T1 T2 Ht1 IH1 Ht2 IH2
    | Gamma
    | Gamma ];
    intros theta Hlc Hsat.
  - (* T_Var *)
    cbn [subst_tm]. exact (Hsat x T Hx).
  - (* T_Abs *)
    cbn [subst_tm].
    assert (Hlc1 : lc_at 1 t1).
    { apply lc_at_open_inv with (k := 0) (u := tm_fvar (fresh_atom L)).
      exact (has_type_lc _ _ _ (Hpre (fresh_atom L) (fresh_atom_notin L))). }
    split.
    + (* local closure of the abstraction *)
      apply lc_abs.
      exact (lc_at_subst t1 theta 1 Hlc1 Hlc).
    + split.
      * apply SN_abs.
      * intros u Hu.
        apply C_beta with (A := T1) (B := T2) (body := subst_tm theta t1) (u := u).
        -- exact (lc_at_subst t1 theta 1 Hlc1 Hlc).
        -- intros v Hv.
           pose (x := fresh_atom (L ++ fv t1)).
           assert (HxL : ~ In x L).
           { unfold x. intro Hi. apply (fresh_atom_notin (L ++ fv t1)).
             apply in_or_app. left. exact Hi. }
           assert (Hxfv : ~ In x (fv t1)).
           { unfold x. intro Hi. apply (fresh_atom_notin (L ++ fv t1)).
             apply in_or_app. right. exact Hi. }
           assert (Hlc' : lc_env (upd_env theta x v)).
           { intro y. unfold upd_env.
             destruct (Nat.eqb x y) eqn:E.
             - exact (C_lc T1 v Hv).
             - apply Hlc. }
           assert (Hsat' : sat (update Gamma x T1) (upd_env theta x v)).
           { intros y T' Hy. unfold update in Hy.
             destruct (Nat.eqb x y) eqn:E.
             - apply Nat.eqb_eq in E. subst y. simpl in Hy.
               inversion Hy; subst T'.
               rewrite upd_env_eq. exact Hv.
             - apply Nat.eqb_neq in E. simpl in Hy.
               rewrite (upd_env_neq theta x y v E). apply Hsat. exact Hy. }
           pose proof (IHpre x HxL (upd_env theta x v) Hlc' Hsat') as Hres.
           change (C T2 (subst_tm (upd_env theta x v)
                           (open_rec 0 (tm_fvar x) t1))) in Hres.
           rewrite (subst_open_rec 0 t1 theta v x Hxfv
                      (fun y Hy => Hlc y)) in Hres.
           exact Hres.
        -- exact Hu.
  - (* T_App *)
    cbn [subst_tm].
    exact (C_app T1 T2 (subst_tm theta t1) (IH1 theta Hlc Hsat)
             (subst_tm theta t2) (IH2 theta Hlc Hsat)).
  - (* T_True *)
    cbn [subst_tm]. split.
    + apply lc_true.
    + apply SN_true.
  - (* T_False *)
    cbn [subst_tm]. split.
    + apply lc_false.
    + apply SN_false.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  assert (Hlc : lc_env (fun x => tm_fvar x)).
  { intro x. apply lc_fvar. }
  assert (Hsat : sat empty (fun x => tm_fvar x)).
  { intros x T' Hx. unfold empty in Hx. discriminate Hx. }
  pose proof (fundamental empty t T Hty (fun x => tm_fvar x) Hlc Hsat) as H.
  rewrite subst_tm_id in H.
  exact (C_sn T t H).
Qed.

End STLCNormalizationNoneHardTask.
