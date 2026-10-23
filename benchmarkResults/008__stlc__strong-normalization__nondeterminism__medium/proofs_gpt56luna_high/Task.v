(** STLC call-by-value strong-normalization benchmark, Medium variant.
    Non-deterministic choice is included; if-then-else and recursion are not. *)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Relations.Relation_Definitions.
From Stdlib Require Import Lia.

Module STLCNormalizationNondeterminismMediumTask.

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
Notation "'choice' t1 'or' t2" := (tm_choice t1 t2)
  (in custom stlc_tm at level 200,
   t1 custom stlc_tm,
   t2 custom stlc_tm at level 200,
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
  | tm_choice t1 t2 =>
      tm_choice (open_rec k u t1) (open_rec k u t2)
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
  | lc_choice : forall k t1 t2,
      lc_at k t1 ->
      lc_at k t2 ->
      lc_at k (tm_choice t1 t2).

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
  | ST_ChoiceLeft : forall t1 t2,
      locally_closed t1 ->
      locally_closed t2 ->
      tm_choice t1 t2 --> t1
  | ST_ChoiceRight : forall t1 t2,
      locally_closed t1 ->
      locally_closed t2 ->
      tm_choice t1 t2 --> t2
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
  | T_Choice : forall Gamma t1 t2 T,
      <{ Gamma |-- $(t1) \in T }> ->
      <{ Gamma |-- $(t2) \in T }> ->
      <{ Gamma |-- choice $(t1) or $(t2) \in T }>
where "<{ Gamma '|--' t '\in' T }>" := (has_type Gamma t T)
  : stlc_scope.

(** Target theorem: strong normalization for the supplied CBV relation. *)

Inductive strongly_normalizing : tm -> Prop :=
  | SN_intro : forall t,
      (forall t', t --> t' -> strongly_normalizing t') ->
      strongly_normalizing t.

(** Provided logical relation. *)

Fixpoint strong_value_relation (T : ty) (v : tm) : Prop :=
  value v /\
  match T with
  | Ty_Bool =>
      v = tm_true \/ v = tm_false
  | Ty_Arrow T1 T2 =>
      exists body,
        v = tm_abs T1 body /\
        forall arg,
          strong_value_relation T1 arg ->
          locally_closed (open body arg) /\
          strongly_normalizing (open body arg) /\
          forall result,
            open body arg -->* result ->
            value result ->
            strong_value_relation T2 result
  end.

Definition strong_expression_relation (T : ty) (t : tm) : Prop :=
  locally_closed t /\
  strongly_normalizing t /\
  forall v,
    t -->* v ->
    value v ->
    strong_value_relation T v.

Definition term_substitution := atom -> tm.

Definition id_substitution : term_substitution :=
  fun x => tm_fvar x.

Definition subst_update
    (rho : term_substitution) (x : atom) (v : tm) : term_substitution :=
  fun y => if Nat.eqb x y then v else rho y.

Fixpoint msubst (rho : term_substitution) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => rho x
  | tm_app t1 t2 => tm_app (msubst rho t1) (msubst rho t2)
  | tm_abs T t1 => tm_abs T (msubst rho t1)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_choice t1 t2 => tm_choice (msubst rho t1) (msubst rho t2)
  end.

Definition proper_substitution (rho : term_substitution) : Prop :=
  forall x, locally_closed (rho x).

Definition strong_related_substitution
    (Gamma : context) (rho : term_substitution) : Prop :=
  forall x T,
    Gamma x = Some T ->
    strong_value_relation T (rho x).

Lemma multi_trans : forall t u v,
  t -->* u -> u -->* v -> t -->* v.
Proof.
  intros t u v Htu Huv.
  induction Htu as [t | t u w Htu Hwv IH].
  - exact Huv.
  - apply multi_step with u.
    + exact Htu.
    + apply IH. exact Huv.
Qed.

Lemma sn_of_step : forall t t',
  strongly_normalizing t -> t --> t' -> strongly_normalizing t'.
Proof.
  intros t t' H Hstep.
  destruct H as [t H]. exact (H t' Hstep).
Qed.

Lemma sn_of_multi : forall t t',
  strongly_normalizing t -> t -->* t' -> strongly_normalizing t'.
Proof.
  intros t t' H Hmulti.
  induction Hmulti as [t | t u t' Htu Hmulti IH].
  - exact H.
  - apply IH. eapply sn_of_step; eauto.
Qed.

Lemma value_sn : forall v, value v -> strongly_normalizing v.
Proof.
  intros v Hv.
  constructor. intros v' Hstep.
  destruct Hv; inversion Hstep.
Qed.

Fixpoint max_list (L : list atom) : atom :=
  match L with
  | nil => 0
  | x :: L' => Nat.max x (max_list L')
  end.

Lemma le_max_list : forall x L, In x L -> x <= max_list L.
Proof.
  intros x L Hin.
  induction L as [| y L IH].
  - inversion Hin.
  - simpl in *. destruct Hin as [<- | Hin].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; exact Hin | apply Nat.le_max_r].
Qed.

Lemma exists_fresh : forall L : list atom, exists x, ~ In x L.
Proof.
  intros L. exists (S (max_list L)).
  intro Hin.
  pose proof (le_max_list (S (max_list L)) L Hin) as H.
  lia.
Qed.

Lemma lc_weaken : forall k j t,
  k <= j -> lc_at k t -> lc_at j t.
Proof.
  intros k j t Hkj Hlc. generalize dependent j.
  induction Hlc as
      [k i Hlt | k x | k t1 t2 H1 IH1 H2 IH2 |
       k T t H IH | k | k | k t1 t2 H1 IH1 H2 IH2].
  - intros Hkj j. constructor. lia.
  - intros Hkj j. constructor.
  - intros Hkj j. constructor.
    + apply IH1; lia.
    + apply IH2; lia.
  - intros Hkj j. constructor. apply IH. lia.
  - intros Hkj j. constructor.
  - intros Hkj j. constructor.
  - intros Hkj j. constructor.
    + apply IH1; lia.
    + apply IH2; lia.
Qed.

Lemma lc_msubst_at : forall k t rho,
  lc_at k t -> proper_substitution rho -> lc_at k (msubst rho t).
Proof.
  intros k t rho Hlc Hproper.
  induction Hlc as
      [k i Hlt | k x | k t1 t2 H1 IH1 H2 IH2 |
       k T t H IH | k | k | k t1 t2 H1 IH1 H2 IH2].
  - constructor. exact Hlt.
  - simpl. apply (lc_weaken 0 k (rho x)); [lia | apply Hproper].
  - simpl. constructor; assumption.
  - simpl. constructor. apply IH.
  - constructor.
  - constructor.
  - simpl. constructor; assumption.
Qed.

Lemma lc_msubst : forall t rho,
  locally_closed t -> proper_substitution rho -> locally_closed (msubst rho t).
Proof.
  intros t rho H Hproper. unfold locally_closed in *.
  eapply lc_msubst_at; eauto.
Qed.

Lemma open_rec_lc_at : forall j k u t,
  lc_at j t -> j <= k -> open_rec k u t = t.
Proof.
  intros j k u t Hlc. revert k.
  induction Hlc as
      [j i Hlt | j x | j t1 t2 H1 IH1 H2 IH2 |
       j T t H IH | j | j | j t1 t2 H1 IH1 H2 IH2].
  - intros k Hjk. simpl. destruct (Nat.eqb k i) eqn:Heq.
    + apply Nat.eqb_eq in Heq. lia.
    + reflexivity.
  - intros k Hjk. reflexivity.
  - intros k Hjk. simpl. rewrite (IH1 k Hjk), (IH2 k Hjk). reflexivity.
  - intros k Hjk. simpl. f_equal. apply IH. lia.
  - intros k Hjk. reflexivity.
  - intros k Hjk. reflexivity.
  - intros k Hjk. simpl. rewrite (IH1 k Hjk), (IH2 k Hjk). reflexivity.
Qed.

Lemma msubst_open_fvar : forall rho k t x,
  proper_substitution rho ->
  msubst rho (open_rec k (tm_fvar x) t) =
  open_rec k (rho x) (msubst rho t).
Proof.
  intros rho k t. revert k.
  induction t as [i | y | t1 IH1 t2 IH2 | T t IH | | |
                   t1 IH1 t2 IH2]; intros k x Hproper; simpl.
  - destruct (Nat.eqb k i); reflexivity.
  - rewrite (open_rec_lc_at 0 k (rho x) (rho y)). reflexivity.
    apply Hproper.
    lia.
  - rewrite IH1, IH2; auto.
  - rewrite IH; auto.
  - reflexivity.
  - reflexivity.
  - rewrite IH1, IH2; auto.
Qed.

Lemma msubst_open : forall rho t x,
  proper_substitution rho ->
  msubst rho (open t (tm_fvar x)) =
  open (msubst rho t) (rho x).
Proof.
  intros. apply msubst_open_fvar; assumption.
Qed.

Lemma proper_update : forall rho x v,
  proper_substitution rho -> locally_closed v ->
  proper_substitution (subst_update rho x v).
Proof.
  intros rho x v Hrho Hv y. unfold subst_update.
  destruct (Nat.eqb x y); auto.
Qed.

Lemma strong_related_update : forall Gamma rho x T v,
  strong_related_substitution Gamma rho ->
  strong_value_relation T v ->
  strong_related_substitution (update Gamma x T)
    (subst_update rho x v).
Proof.
  intros Gamma rho x T v Hrho Hv y U Hget.
  unfold update in Hget. unfold subst_update.
  destruct (Nat.eqb x y) eqn:Heq.
  - apply Nat.eqb_eq in Heq. subst y.
    injection Hget as HeqT. subst U. exact Hv.
  - apply Hrho with (x := y) (T := U).
    exact Hget.
Qed.

Lemma app_sn : forall t1 t2,
  strongly_normalizing t1 -> strongly_normalizing t2 ->
  (forall T body v1 v2,
    t1 -->* v1 -> value v1 ->
    t2 -->* v2 -> value v2 ->
    v1 = tm_abs T body ->
    strongly_normalizing (open body v2)) ->
  strongly_normalizing (tm_app t1 t2).
Proof.
  intros t1 t2 H1. revert t2.
  induction H1 as [t1 Hsteps IH1].
  intros t2 H2 Hterm.
  induction H2 as [t2 Hsteps2 IH2].
  constructor. intros t' Hstep.
  inversion Hstep as
    [T body v Hlc Hv | a a' b Haa Hblc | v b b' Hv Hbb |
     a b Halc Hblc | a b Hal c]; subst.
  - apply Hterm with (T := T) (body := body)
      (v1 := tm_abs T body) (v2 := t2).
    + apply multi_refl.
    + constructor; assumption.
    + apply multi_refl.
    + exact Hv.
    + reflexivity.
  - apply IH1 with (t' := a').
    + exact Haa.
    + constructor. exact Hsteps2.
    + intros T body v1 v2 Hmulti Hv1 Hmulti2 Hv2 Heq.
      apply Hterm with (T := T) (body := body)
        (v1 := v1) (v2 := v2).
      * apply multi_step with a'. exact Haa. exact Hmulti.
      * exact Hv1.
      * exact Hmulti2.
      * exact Hv2.
      * exact Heq.
  - apply IH2 with (t' := b').
    + exact Hbb.
    + intros T body v1 v2 Hmulti Hv1 Hmulti2 Hv2 Heq.
      apply Hterm with (T := T) (body := body)
        (v1 := v1) (v2 := v2).
      * exact Hmulti.
      * exact Hv1.
      * apply multi_step with b'. exact Hbb. exact Hmulti2.
      * exact Hv2.
      * exact Heq.
Qed.

Lemma app_value_path : forall t1 t2 v,
  tm_app t1 t2 -->* v -> value v ->
  exists T body v1 v2,
    t1 -->* v1 /\ value v1 /\
    t2 -->* v2 /\ value v2 /\
    v1 = tm_abs T body /\
    open body v2 -->* v.
Proof.
  intros t1 t2 v Hpath Hv.
  assert (Haux : forall s r, multi step s r ->
    value r -> forall p q,
      s = tm_app p q ->
      exists T body v1 v2,
        p -->* v1 /\ value v1 /\
        q -->* v2 /\ value v2 /\
        v1 = tm_abs T body /\ open body v2 -->* r).
  { apply (multi_ind tm step
      (fun s r => value r -> forall p q,
        s = tm_app p q ->
        exists T body v1 v2,
          p -->* v1 /\ value v1 /\
          q -->* v2 /\ value v2 /\
          v1 = tm_abs T body /\ open body v2 -->* r)).
    - intros s Hs p q Hsrc. destruct Hs; inversion Hsrc.
    - intros s u r Hsu Hrest IH Hr p q Hsrc.
    inversion Hsu as
      [T body a Hlc Ha | a a' b Haa Hblc | a b b' Ha Hbb |
       a b Halc Hblc | a b Halc Hblc]; subst.
    + injection H as Hp Hq. subst p. subst q.
      exists T, body, (tm_abs T body), a.
      split; [apply multi_refl |].
      split; [constructor; exact Hlc |].
      split; [apply multi_refl |].
      split; [exact Ha |].
      split; [reflexivity | exact Hrest].
    + injection H as Hp Hq. subst p. subst q.
      destruct (IH Hr a' b eq_refl) as
          [T [body [v1 [v2 [H1 [Hv1 [H2 [Hv2 [Heq Hbody]]]]]]]]].
      exists T, body, v1, v2. repeat split.
      * apply multi_step with a'. exact Haa. exact H1.
      * exact Hv1.
      * exact H2.
      * exact Hv2.
      * exact Heq.
      * exact Hbody.
    + injection H as Hp Hq. subst p. subst q.
      destruct (IH Hr a b' eq_refl) as
          [T [body [v1 [v2 [H1 [Hv1 [H2 [Hv2 [Heq Hbody]]]]]]]]].
      exists T, body, v1, v2. repeat split.
      * exact H1.
      * exact Hv1.
      * apply multi_step with b'. exact Hbb. exact H2.
      * exact Hv2.
      * exact Heq.
      * exact Hbody.
    + exfalso. congruence.
    + exfalso. congruence.
  }
  destruct (Haux _ _ Hpath Hv t1 t2 eq_refl) as
    [T [body [v1 [v2 [H1 [Hv1 [H2 [Hv2 [Heq Hbody]]]]]]]]].
  exists T, body, v1, v2.
  split; [exact H1 |].
  split; [exact Hv1 |].
  split; [exact H2 |].
  split; [exact Hv2 |].
  split; [exact Heq | exact Hbody].
Qed.

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v Hv. destruct Hv.
  - exact H.
  - unfold locally_closed. constructor.
  - unfold locally_closed. constructor.
Qed.

Lemma multi_value_refl : forall v r,
  value v -> v -->* r -> r = v.
Proof.
  intros v r Hv Hmulti.
  induction Hmulti as [v | v u r Hvu Hrest IH].
  - reflexivity.
  - exfalso. destruct Hv; inversion Hvu.
Qed.

Lemma lc_open_inv : forall k u t,
  lc_at k (open_rec k u t) -> lc_at (S k) t.
Proof.
  intros k u t. revert k.
  induction t as [i | x | t1 IH1 t2 IH2 | T t IH | | |
                   t1 IH1 t2 IH2]; intros k Hlc; simpl in Hlc.
  - destruct (Nat.eqb k i) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst i. constructor. lia.
    + constructor. inversion Hlc. lia.
  - constructor.
  - inversion Hlc. constructor.
    + apply IH1. assumption.
    + apply IH2. assumption.
  - inversion Hlc. constructor. apply IH. assumption.
  - constructor.
  - constructor.
  - inversion Hlc. constructor.
    + apply IH1. assumption.
    + apply IH2. assumption.
Qed.

Lemma typing_lc : forall Gamma t T,
  <{ Gamma |-- t \in T }> -> locally_closed t.
Proof.
  intros Gamma t T Hty.
  induction Hty as
      [Gamma x T Hget | L Gamma T1 T2 t1 Hbody IH |
       Gamma t1 t2 T1 T2 H1 IH1 H2 IH2 | Gamma | Gamma |
       Gamma t1 t2 T H1 IH1 H2 IH2].
  - unfold locally_closed. constructor.
  - unfold locally_closed. constructor.
    destruct (exists_fresh L) as [x Hx].
    apply (lc_open_inv 0 (tm_fvar x) t1).
    apply IH. exact Hx.
  - unfold locally_closed. constructor; assumption.
  - unfold locally_closed. constructor.
  - unfold locally_closed. constructor.
  - unfold locally_closed. constructor; assumption.
Qed.

Lemma choice_value_path : forall t1 t2 v,
  tm_choice t1 t2 -->* v -> value v ->
  t1 -->* v \/ t2 -->* v.
Proof.
  intros t1 t2 v Hpath Hv.
  assert (Haux : forall s r, multi step s r -> value r ->
    forall p q, s = tm_choice p q -> p -->* r \/ q -->* r).
  { apply (multi_ind tm step
      (fun s r => value r -> forall p q,
        s = tm_choice p q -> p -->* r \/ q -->* r)).
    - intros s Hs p q Hsrc. destruct Hs; inversion Hsrc.
    - intros s u r Hsu Hrest IH Hr p q Hsrc.
      inversion Hsu as
        [T body a Hlc Ha | a a' b Haa Hblc | a b b' Ha Hbb |
         a b Halc Hblc | a b Halc Hblc]; subst.
      + exfalso. congruence.
      + exfalso. congruence.
      + exfalso. congruence.
      + injection H as Hp Hq. subst p. subst q.
        left. exact Hrest.
      + injection H as Hp Hq. subst p. subst q.
        right. exact Hrest.
  }
  exact (Haux _ _ Hpath Hv t1 t2 eq_refl).
Qed.

Lemma strong_value_is_value : forall T v,
  strong_value_relation T v -> value v.
Proof.
  intros T v H. destruct T; simpl in H; exact (proj1 H).
Qed.

Fixpoint fvars (t : tm) : list atom :=
  match t with
  | tm_bvar _ => nil
  | tm_fvar x => x :: nil
  | tm_app t1 t2 => fvars t1 ++ fvars t2
  | tm_abs _ t1 => fvars t1
  | tm_true => nil
  | tm_false => nil
  | tm_choice t1 t2 => fvars t1 ++ fvars t2
  end.

Lemma msubst_update_notin : forall rho x v t,
  ~ In x (fvars t) ->
  msubst (subst_update rho x v) t = msubst rho t.
Proof.
  intros rho x v t Hnot.
  induction t as [i | y | t1 IH1 t2 IH2 | T t IH | | |
                   t1 IH1 t2 IH2]; simpl.
  - reflexivity.
  - destruct (Nat.eqb x y) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst y. exfalso. apply Hnot. simpl. auto.
    + unfold subst_update. rewrite Heq. reflexivity.
  - f_equal.
    + apply IH1. intro Hin. apply Hnot. apply in_or_app. left. exact Hin.
    + apply IH2. intro Hin. apply Hnot. apply in_or_app. right. exact Hin.
  - f_equal. apply IH. exact Hnot.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply IH1. intro Hin. apply Hnot. apply in_or_app. left. exact Hin.
    + apply IH2. intro Hin. apply Hnot. apply in_or_app. right. exact Hin.
Qed.

Lemma subst_update_same : forall rho x v,
  subst_update rho x v x = v.
Proof.
  intros. unfold subst_update. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma msubst_id : forall t, msubst id_substitution t = t.
Proof.
  induction t as [i | x | t1 IH1 t2 IH2 | T t IH | | |
                   t1 IH1 t2 IH2]; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH. reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IH1, IH2. reflexivity.
Qed.

Lemma strong_expr_value : forall T v,
  strong_value_relation T v -> strong_expression_relation T v.
Proof.
  intros T v Hrel. destruct T as [|T1 T2]; simpl in Hrel.
  - unfold strong_expression_relation.
    destruct Hrel as [Hv Hshape].
    split.
    + apply value_lc. exact Hv.
    + split.
      * apply value_sn. exact Hv.
      * intros r Hmulti Hr.
        rewrite (multi_value_refl v r Hv Hmulti).
        exact (conj Hv Hshape).
  - unfold strong_expression_relation.
    destruct Hrel as [Hv Hshape].
    split.
    + apply value_lc. exact Hv.
    + split.
      * apply value_sn. exact Hv.
      * intros r Hmulti Hr.
        rewrite (multi_value_refl v r Hv Hmulti).
        exact (conj Hv Hshape).
Qed.

Theorem fundamental : forall Gamma t T rho,
  <{ Gamma |-- t \in T }> ->
  proper_substitution rho ->
  strong_related_substitution Gamma rho ->
  strong_expression_relation T (msubst rho t).
Proof.
  intros Gamma t T rho Hty.
  revert rho.
  induction Hty as
      [Gamma x T Hget |
       L Gamma T1 T2 t1 Hbody IH |
       Gamma t1 t2 T1 T2 H1 IH1 H2 IH2 |
       Gamma |
       Gamma |
       Gamma t1 t2 T H1 IH1 H2 IH2].
  - intros rho Hproper Hrelated.
    apply strong_expr_value.
    apply Hrelated with (x := x) (T := T). exact Hget.
  - intros rho Hproper Hrelated.
    unfold strong_expression_relation.
    split.
    + apply lc_msubst.
      * apply typing_lc with (Gamma := Gamma) (T := Ty_Arrow T1 T2).
        apply T_Abs with (L := L) (T1 := T1) (T2 := T2) (t1 := t1). exact Hbody.
      * exact Hproper.
    + assert (Hval : value (msubst rho (tm_abs T1 t1))).
      { constructor.
        change (locally_closed (msubst rho (tm_abs T1 t1))).
        apply lc_msubst.
        apply typing_lc with (Gamma := Gamma) (T := Ty_Arrow T1 T2).
        apply T_Abs with (L := L) (T1 := T1) (T2 := T2) (t1 := t1). exact Hbody.
        exact Hproper. }
      split.
      * exact (value_sn _ Hval).
      * intros result Hpath Hresult.
        rewrite (multi_value_refl (msubst rho (tm_abs T1 t1)) result
          Hval Hpath).
        unfold strong_value_relation. simpl.
        split.
        -- constructor.
          change (locally_closed (msubst rho (tm_abs T1 t1))).
          apply lc_msubst.
          apply typing_lc with (Gamma := Gamma) (T := Ty_Arrow T1 T2).
          apply T_Abs with (L := L) (T1 := T1) (T2 := T2) (t1 := t1). exact Hbody.
          exact Hproper.
        -- exists (msubst rho t1). split; [reflexivity |].
          intros arg Harg.
        destruct (exists_fresh (L ++ fvars t1)) as [x Hx].
        assert (HxL : ~ In x L).
        { intro Hin. apply Hx. apply in_or_app. left. exact Hin. }
        assert (HxF : ~ In x (fvars t1)).
        { intro Hin. apply Hx. apply in_or_app. right. exact Hin. }
        specialize (Hbody x HxL).
        specialize (IH x HxL).
        set (rho' := subst_update rho x arg).
        assert (Hproper' : proper_substitution rho').
        { unfold rho'. apply proper_update; [exact Hproper | apply value_lc; apply strong_value_is_value with (T := T1); exact Harg]. }
        assert (Hrelated' :
          strong_related_substitution (update Gamma x T1) rho').
        { unfold rho'. apply strong_related_update; assumption. }
        destruct (IH rho' Hproper' Hrelated') as [Hlc [Hsn Hend]].
        assert (Hopen :
          msubst rho' (open t1 (tm_fvar x)) =
          open (msubst rho t1) arg).
        { unfold rho'.
          change (msubst (subst_update rho x arg)
                    (open_rec 0 (tm_fvar x) t1) =
                  open_rec 0 arg (msubst rho t1)).
          rewrite (msubst_open_fvar (subst_update rho x arg) 0 t1 x Hproper').
          rewrite (msubst_update_notin rho x arg t1 HxF).
          rewrite (subst_update_same rho x arg). reflexivity. }
        rewrite Hopen in Hlc, Hsn, Hend.
        split; [exact Hlc | split; [exact Hsn | exact Hend]].
  - intros rho Hproper Hrelated.
    destruct (IH1 rho Hproper Hrelated) as [Hlc1 [Hsn1 Hend1]].
    destruct (IH2 rho Hproper Hrelated) as [Hlc2 [Hsn2 Hend2]].
    unfold strong_expression_relation.
    split.
    + simpl. constructor; assumption.
    + split.
      * apply app_sn; try assumption.
        intros Ta body v1 v2 Hp Hv1 Hq Hv2 Heq.
        specialize (Hend1 v1 Hp Hv1).
        specialize (Hend2 v2 Hq Hv2).
        simpl in Hend1.
        destruct Hend1 as [Hv1' [body0 [Heq0 Hfun]]].
        subst v1. injection Heq as HT Hb. subst Ta. subst body.
        destruct (Hfun v2 Hend2) as [Hlc [Hsn Hend]].
        exact Hsn.
      * intros result Hpath Hresult.
        destruct (app_value_path (msubst rho t1) (msubst rho t2)
          result Hpath Hresult) as
          [Ta [body [v1 [v2 [Hp [Hv1 [Hq [Hv2 [Heq Hbody]]]]]]]]].
        specialize (Hend1 v1 Hp Hv1).
        specialize (Hend2 v2 Hq Hv2).
        simpl in Hend1.
        destruct Hend1 as [Hv1' [body0 [Heq0 Hfun]]].
        subst v1. injection Heq as HT Hb. subst Ta. subst body.
        apply Hfun with (arg := v2); assumption.
  - intros rho Hproper Hrelated.
    apply strong_expr_value.
    split.
    + constructor.
    + left. reflexivity.
  - intros rho Hproper Hrelated.
    apply strong_expr_value.
    split.
    + constructor.
    + right. reflexivity.
  - intros rho Hproper Hrelated.
    destruct (IH1 rho Hproper Hrelated) as [Hlc1 [Hsn1 Hend1]].
    destruct (IH2 rho Hproper Hrelated) as [Hlc2 [Hsn2 Hend2]].
    unfold strong_expression_relation.
    split.
    + simpl. constructor; assumption.
    + split.
      * constructor. intros result Hstep.
        inversion Hstep; subst; assumption.
      * intros result Hpath Hresult.
        destruct (choice_value_path (msubst rho t1) (msubst rho t2)
          result Hpath Hresult) as [Hp | Hq].
        -- apply Hend1; assumption.
        -- apply Hend2; assumption.
Qed.

Theorem strong_normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  assert (Hproper : proper_substitution id_substitution).
  { intros x. unfold id_substitution, locally_closed. constructor. }
  assert (Hrelated : strong_related_substitution empty id_substitution).
  { intros x U Hget. unfold empty in Hget. inversion Hget. }
  destruct (fundamental empty t T id_substitution Hty Hproper Hrelated)
    as [Hlc [Hsn Hend]].
  rewrite (msubst_id t) in Hsn.
  exact Hsn.
Qed.

End STLCNormalizationNondeterminismMediumTask.
