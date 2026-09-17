(** STLC call-by-value strong-normalization benchmark, Medium variant.
    System T-style natural-number recursion; no if-then-else or choice. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Relations.Relation_Definitions Lia.
Import ListNotations.

Module STLCNormalizationRecursionMediumTask.

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

  | tm_natrec : tm -> tm -> tm -> tm.

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
      lc_at k (tm_natrec n b s).

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
where "<{ Gamma '|--' t '\in' T }>" := (has_type Gamma t T)
  : stlc_scope.

Hint Constructors has_type : core.

Inductive strongly_normalizing : tm -> Prop :=
  | SN_intro : forall t,
      (forall t', t --> t' -> strongly_normalizing t') ->
      strongly_normalizing t.

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
  | tm_zero => tm_zero
  | tm_succ t => tm_succ (msubst rho t)
  | tm_natrec n b s => tm_natrec (msubst rho n) (msubst rho b) (msubst rho s)
  end.

Definition proper_substitution (rho : term_substitution) : Prop :=
  forall x, locally_closed (rho x).

Fixpoint value_relation (T : ty) (v : tm) : Prop :=
  value v /\
  match T with
  | Ty_Nat => numeric_value v
  | Ty_Bool =>
      v = tm_true \/ v = tm_false
  | Ty_Arrow T1 T2 =>
      exists body,
        v = tm_abs T1 body /\
        forall arg,
          value_relation T1 arg ->
          locally_closed (open body arg) /\
          exists v',
            open body arg -->* v' /\
            value_relation T2 v'
  end.

Definition expression_relation (T : ty) (t : tm) : Prop :=
  locally_closed t /\
  exists v,
    t -->* v /\
    value_relation T v.

Definition related_substitution
    (Gamma : context) (rho : term_substitution) : Prop :=
  forall x T, Gamma x = Some T -> value_relation T (rho x).

(** Elementary infrastructure for the logical-relations argument. *)

Lemma multi_transitive : forall t u v,
  t -->* u -> u -->* v -> t -->* v.
Proof.
  intros t u v Htu Huv. induction Htu; eauto using multi.
Qed.

Lemma multi_one : forall t u, t --> u -> t -->* u.
Proof. intros; eauto using multi. Qed.

Lemma lc_at_weaken : forall k t, lc_at k t ->
  forall j, k <= j -> lc_at j t.
Proof.
  intros k t H. induction H; intros j Hkj.
  - apply lc_bvar. lia.
  - apply lc_fvar.
  - apply lc_app; eauto.
  - apply lc_abs. eauto with arith.
  - apply lc_true.
  - apply lc_false.
  - apply lc_zero.
  - apply lc_succ. eauto.
  - apply lc_rec; eauto.
Qed.

Lemma numeric_value_lc : forall n, numeric_value n -> locally_closed n.
Proof. intros n H; induction H; unfold locally_closed in *; eauto. Qed.

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v H. destruct H as [T t Hlc | | | n Hnv].
  - exact Hlc.
  - constructor.
  - constructor.
  - apply numeric_value_lc. exact Hnv.
Qed.

Lemma numeric_value_no_step : forall n, numeric_value n ->
  forall n', ~ n --> n'.
Proof.
  intros n Hnv. induction Hnv as [|n Hnv IH]; intros n' Hs.
  - inversion Hs.
  - inversion Hs; subst. eapply IH; eauto.
Qed.

Lemma value_no_step : forall v, value v -> forall v', ~ v --> v'.
Proof.
  intros v Hv. destruct Hv as [T t Hlc | | | n Hnv]; intros v' Hs.
  - inversion Hs.
  - inversion Hs.
  - inversion Hs.
  - eapply numeric_value_no_step; eauto.
Qed.

Lemma step_deterministic : forall t u, t --> u ->
  forall v, t --> v -> u = v.
Proof.
  intros t u H. induction H; intros w Hw; inversion Hw; subst;
    try reflexivity;
    intros; subst; try reflexivity; try congruence;
    try match goal with
        | Hv : value ?q, Hq : ?q --> ?q' |- _ =>
            exfalso; exact (value_no_step q Hv q' Hq)
        | Hn : numeric_value ?q, Hq : ?q --> ?q' |- _ =>
            exfalso; exact (numeric_value_no_step q Hn q' Hq)
        | Hlc : locally_closed (tm_abs ?A ?body),
          Hq : tm_abs ?A ?body --> ?q' |- _ =>
            exfalso; exact (value_no_step _ (v_abs A body Hlc) q' Hq)
        | Hq : tm_zero --> ?q' |- _ =>
            exfalso; exact (numeric_value_no_step _ nv_zero q' Hq)
        | Hn : numeric_value ?q, Hs : tm_succ ?q --> ?q' |- _ =>
            exfalso; exact (numeric_value_no_step _ (nv_succ q Hn) q' Hs)
        end;
    try solve [f_equal; eauto].
Qed.

Lemma multi_to_normal_SN : forall t v,
  t -->* v -> (forall v', ~ v --> v') -> strongly_normalizing t.
Proof.
  intros t v Hmulti. induction Hmulti; intros Hnormal.
  - constructor. intros t' Hs. exfalso. exact (Hnormal t' Hs).
  - constructor. intros t' Hxt'.
    assert (t' = y) by (eapply step_deterministic; eauto).
    subst. apply IHHmulti. exact Hnormal.
Qed.

Lemma value_relation_lc : forall T v,
  value_relation T v -> locally_closed v.
Proof.
  intros T v H. apply value_lc. destruct T; exact (proj1 H).
Qed.

Lemma value_relation_value : forall T v,
  value_relation T v -> value v.
Proof. intros T v H; destruct T; exact (proj1 H). Qed.

Lemma expression_relation_SN : forall T t,
  expression_relation T t -> strongly_normalizing t.
Proof.
  intros T t [_ [v [Hred Hvr]]].
  eapply multi_to_normal_SN; eauto.
  intros v' Hs. eapply value_no_step; [|exact Hs].
  destruct T; exact (proj1 Hvr).
Qed.

Lemma multi_app1 : forall t t' u,
  t -->* t' -> locally_closed u -> tm_app t u -->* tm_app t' u.
Proof.
  intros t t' u H. induction H; intros Hu; eauto using multi, step.
Qed.

Lemma multi_app2 : forall v t t',
  value v -> t -->* t' -> tm_app v t -->* tm_app v t'.
Proof.
  intros v t t' Hv H. induction H; eauto using multi, step.
Qed.

Lemma multi_succ : forall t t',
  t -->* t' -> tm_succ t -->* tm_succ t'.
Proof.
  intros t t' H. induction H as [x|x y z Hxy Hyz IH].
  - constructor.
  - eapply multi_step; [apply ST_Succ; exact Hxy|exact IH].
Qed.

Lemma multi_rec_arg : forall n n' b s,
  n -->* n' -> locally_closed b -> locally_closed s ->
  tm_natrec n b s -->* tm_natrec n' b s.
Proof.
  intros n n' b s H. induction H; intros Hb Hs; eauto using multi, step.
Qed.

Lemma multi_rec_base : forall n b b' s,
  numeric_value n -> b -->* b' -> locally_closed s ->
  tm_natrec n b s -->* tm_natrec n b' s.
Proof.
  intros n b b' s Hn H. induction H; intros Hs; eauto using multi, step.
Qed.

Lemma multi_rec_step : forall n b s s',
  numeric_value n -> value b -> s -->* s' ->
  tm_natrec n b s -->* tm_natrec n b s'.
Proof.
  intros n b s s' Hn Hb H. induction H; eauto using multi, step.
Qed.

Lemma expression_app : forall A B f a,
  expression_relation (Ty_Arrow A B) f ->
  expression_relation A a ->
  expression_relation B (tm_app f a).
Proof.
  intros A B f a [Hflc [fv [Hf Hfvr]]] [Halc [av [Ha Havr]]].
  destruct Hfvr as [Hfv [body [Heq Hbody]]]. subst fv.
  destruct (Hbody av Havr) as [Hopen [r [Hr Hrvr]]].
  split; [constructor; assumption|].
  exists r. split; [|assumption].
  eapply multi_transitive.
  - apply multi_app1; [exact Hf|exact Halc].
  - eapply multi_transitive.
    + apply multi_app2; [exact Hfv|exact Ha].
    + eapply multi_step.
      * apply ST_AppAbs; [eauto using value_lc|eauto using value_relation_value].
      * exact Hr.
Qed.

Lemma expression_natrec_values : forall n T b s,
  numeric_value n -> value_relation T b ->
  value_relation (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  expression_relation T (tm_natrec n b s).
Proof.
  intros n T b s Hn. induction Hn as [|n Hn IH]; intros Hb Hs.
  - split.
    + apply lc_rec.
      * apply lc_zero.
      * eapply value_relation_lc; exact Hb.
      * eapply value_relation_lc; exact Hs.
    + exists b. split.
      * apply multi_one. apply ST_RecZero;
          eauto using value_relation_value.
      * exact Hb.
  - assert (Hnrel : value_relation Ty_Nat n).
    { split; eauto. }
    assert (Hen : expression_relation Ty_Nat n).
    { split; [eauto using numeric_value_lc|]. exists n; split; eauto using multi. }
    assert (Hes : expression_relation (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s).
    { split; [eauto using value_relation_lc|]. exists s; split; eauto using multi. }
    assert (Hsb : expression_relation (Ty_Arrow T T) (tm_app s n)).
    { eapply expression_app; eauto. }
    assert (Hrec : expression_relation T (tm_natrec n b s)) by (apply IH; assumption).
    assert (Hall : expression_relation T
      (tm_app (tm_app s n) (tm_natrec n b s))).
    { eapply expression_app; eauto. }
    destruct Hall as [Hlc [r [Hr Hrr]]].
    split.
    + apply lc_rec.
      * apply lc_succ. exact (numeric_value_lc n Hn).
      * eapply value_relation_lc; exact Hb.
      * eapply value_relation_lc; exact Hs.
    + exists r. split; [|exact Hrr].
      eapply multi_step.
      * apply ST_RecSucc; eauto using value_relation_value.
      * exact Hr.
Qed.

Lemma expression_natrec : forall T n b s,
  expression_relation Ty_Nat n -> expression_relation T b ->
  expression_relation (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  expression_relation T (tm_natrec n b s).
Proof.
  intros T n b s [Hnlc [nv [Hn Hnvr]]]
    [Hblc [bv [Hb Hbvr]]] [Hslc [sv [Hs Hsvr]]].
  destruct Hnvr as [Hnv Hnum].
  pose proof (value_relation_value T bv Hbvr) as Hbv.
  split; [constructor; assumption|].
  destruct (expression_natrec_values nv T bv sv Hnum Hbvr Hsvr) as
    [_ [r [Hrec Hrvr]]].
  exists r. split; [|assumption].
  eapply multi_transitive.
  - apply multi_rec_arg; [exact Hn|exact Hblc|exact Hslc].
  - eapply multi_transitive.
    + apply multi_rec_base; [exact Hnum|exact Hb|exact Hslc].
    + eapply multi_transitive.
      * apply multi_rec_step; [exact Hnum|exact Hbv|exact Hs].
      * exact Hrec.
Qed.

Fixpoint free_atoms (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_app t u => free_atoms t ++ free_atoms u
  | tm_abs _ t => free_atoms t
  | tm_true | tm_false | tm_zero => []
  | tm_succ t => free_atoms t
  | tm_natrec n b s => free_atoms n ++ free_atoms b ++ free_atoms s
  end.

Lemma fresh_atom : forall L : list atom, exists x, ~ In x L.
Proof.
  intro L.
  assert (Hbound : forall y, In y L -> y <= fold_right Nat.max 0 L).
  { intros y Hy. induction L as [|a L IH]; simpl in *; [contradiction|].
    destruct Hy as [->|Hy]; [apply Nat.le_max_l|].
    eapply Nat.le_trans; [apply IH; exact Hy|apply Nat.le_max_r]. }
  exists (S (fold_right Nat.max 0 L)). intros Hin.
  specialize (Hbound _ Hin). lia.
Qed.

Lemma lc_open_fvar_inv_gen : forall t k x,
  lc_at k (open_rec k (tm_fvar x) t) -> lc_at (S k) t.
Proof.
  induction t; intros k x Hlc; simpl in Hlc.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. apply lc_bvar. lia.
    + inversion Hlc; subst. apply lc_bvar. lia.
  - apply lc_fvar.
  - inversion Hlc; subst. apply lc_app; eauto.
  - inversion Hlc; subst. apply lc_abs. eauto.
  - apply lc_true.
  - apply lc_false.
  - apply lc_zero.
  - inversion Hlc; subst. apply lc_succ. eauto.
  - inversion Hlc; subst. apply lc_rec; eauto.
Qed.

Lemma lc_open_fvar_inv : forall t x,
  locally_closed (open t (tm_fvar x)) -> lc_at 1 t.
Proof. intros t x H; exact (lc_open_fvar_inv_gen t 0 x H). Qed.

Lemma typing_lc : forall Gamma t T,
  <{ Gamma |-- t \in T }> -> locally_closed t.
Proof.
  intros Gamma t T Hty. induction Hty as
    [Gamma x T Hlookup
    |L Gamma T1 T2 body Hbody IHbody
    |Gamma f a T1 T2 Hf IHf Ha IHa
    |Gamma|Gamma|Gamma
    |Gamma n Hn IHn
    |Gamma n b s T Hn IHn Hb IHb Hs IHs].
  - apply lc_fvar.
  - destruct (fresh_atom L) as [x Hfresh].
    apply lc_abs. eapply lc_open_fvar_inv. eauto.
  - apply lc_app; assumption.
  - apply lc_true.
  - apply lc_false.
  - apply lc_zero.
  - apply lc_succ. assumption.
  - apply lc_rec; assumption.
Qed.

Lemma msubst_lc_at : forall k t,
  lc_at k t -> forall rho, proper_substitution rho ->
  lc_at k (msubst rho t).
Proof.
  intros k t Hlc. induction Hlc; intros rho Hrho; simpl.
  - apply lc_bvar; assumption.
  - apply lc_at_weaken with (k := 0); [apply Hrho|lia].
  - apply lc_app; eauto.
  - apply lc_abs; eauto.
  - apply lc_true.
  - apply lc_false.
  - apply lc_zero.
  - apply lc_succ; eauto.
  - apply lc_rec; eauto.
Qed.

Lemma msubst_lc : forall t rho,
  locally_closed t -> proper_substitution rho -> locally_closed (msubst rho t).
Proof. intros; eapply msubst_lc_at; eauto. Qed.

Lemma proper_subst_update : forall rho x v,
  proper_substitution rho -> locally_closed v ->
  proper_substitution (subst_update rho x v).
Proof.
  unfold proper_substitution, subst_update. intros rho x v Hr Hv y.
  destruct (Nat.eqb x y); auto.
Qed.

Lemma related_subst_update : forall Gamma rho x A v,
  related_substitution Gamma rho -> value_relation A v ->
  related_substitution (update Gamma x A) (subst_update rho x v).
Proof.
  unfold related_substitution, update, subst_update.
  intros Gamma rho x A v Hr Hv y U Hlookup.
  destruct (Nat.eqb x y) eqn:E.
  - inversion Hlookup; subst. exact Hv.
  - eapply Hr; eauto.
Qed.

Lemma open_rec_lc_at : forall d t,
  lc_at d t -> forall k u, d <= k -> open_rec k u t = t.
Proof.
  intros d t Hlc. induction Hlc; intros j u Hdj; simpl.
  - destruct (Nat.eqb j i) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - reflexivity.
  - rewrite IHHlc1, IHHlc2; auto.
  - rewrite IHHlc by lia. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHHlc; auto.
  - rewrite IHHlc1, IHHlc2, IHHlc3; auto.
Qed.

Lemma open_rec_lc : forall t,
  locally_closed t -> forall k u, open_rec k u t = t.
Proof. intros t H k u. eapply open_rec_lc_at; [exact H|lia]. Qed.

Lemma msubst_open_fresh : forall t k rho x v,
  proper_substitution rho -> ~ In x (free_atoms t) ->
  msubst (subst_update rho x v) (open_rec k (tm_fvar x) t) =
  open_rec k v (msubst rho t).
Proof.
  induction t as [i|a|t1 IH1 t2 IH2|A body IH| | | |t IH
                 |n IHn b IHb s IHs];
    intros k rho x v Hproper Hfresh; simpl.
  - destruct (Nat.eqb k i).
    + change (subst_update rho x v x = v).
      unfold subst_update. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - unfold subst_update. destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E. exfalso. apply Hfresh. now left.
    + symmetry. apply open_rec_lc. apply Hproper.
  - assert (H1 : ~ In x (free_atoms t1)).
    { intro H. apply Hfresh. apply in_or_app. auto. }
    assert (H2 : ~ In x (free_atoms t2)).
    { intro H. apply Hfresh. apply in_or_app. auto. }
    rewrite IH1, IH2; auto.
  - rewrite IH; auto.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IH; auto.
  - assert (Hn : ~ In x (free_atoms n)).
    { intro H. apply Hfresh. apply in_or_app. auto. }
    assert (Hb : ~ In x (free_atoms b)).
    { intro H. apply Hfresh. apply in_or_app. right. apply in_or_app. auto. }
    assert (Hs : ~ In x (free_atoms s)).
    { intro H. apply Hfresh. apply in_or_app. right. apply in_or_app. auto. }
    rewrite IHn, IHb, IHs; auto.
Qed.

Theorem fundamental : forall Gamma t T,
  <{ Gamma |-- t \in T }> -> forall rho,
  proper_substitution rho -> related_substitution Gamma rho ->
  expression_relation T (msubst rho t).
Proof.
  intros Gamma t T Hty. induction Hty as
    [Gamma x T Hlookup
    |L Gamma T1 T2 body Hbody IHbody
    |Gamma f a T1 T2 Hf IHf Ha IHa
    |Gamma|Gamma|Gamma
    |Gamma n Hn IHn
    |Gamma n b s T Hn IHn Hb IHb Hs IHs];
    intros rho Hproper Hrelated; simpl.
  - split; [apply Hproper|]. exists (rho x). split; [constructor|].
    eapply Hrelated; eauto.
  - assert (Habs_lc : locally_closed (tm_abs T1 (msubst rho body))).
    { change (locally_closed (msubst rho (tm_abs T1 body))).
      apply msubst_lc; [eapply typing_lc; eauto using T_Abs|assumption]. }
    split; [exact Habs_lc|].
    exists (tm_abs T1 (msubst rho body)). split; [constructor|].
    split; [constructor; exact Habs_lc|].
    exists (msubst rho body). split; [reflexivity|].
    intros arg Harg.
    destruct (fresh_atom (L ++ free_atoms body)) as [x Hx].
    assert (HxL : ~ In x L).
    { intro H. apply Hx. apply in_or_app. auto. }
    assert (Hxfv : ~ In x (free_atoms body)).
    { intro H. apply Hx. apply in_or_app. auto. }
    specialize (IHbody x HxL (subst_update rho x arg)).
    assert (Hp : proper_substitution (subst_update rho x arg)).
    { apply proper_subst_update; [exact Hproper|].
      eapply value_relation_lc; exact Harg. }
    assert (Hr : related_substitution (update Gamma x T1)
      (subst_update rho x arg)).
    { apply related_subst_update; assumption. }
    specialize (IHbody Hp Hr).
    unfold open in IHbody |- *.
    rewrite msubst_open_fresh in IHbody by assumption.
    exact IHbody.
  - eapply expression_app; eauto.
  - split; [constructor|]. exists tm_true. split; [constructor|].
    split; eauto.
  - split; [constructor|]. exists tm_false. split; [constructor|].
    split; eauto.
  - split; [constructor|]. exists tm_zero. split; [constructor|].
    split; [apply v_nat; constructor|constructor].
  - destruct (IHn rho Hproper Hrelated) as [Hlc [v [Hred Hvr]]].
    split; [constructor; exact Hlc|]. exists (tm_succ v). split.
    + apply multi_succ. exact Hred.
    + destruct Hvr as [Hv Hnv]. split.
      * apply v_nat. constructor. exact Hnv.
      * constructor. exact Hnv.
  - eapply expression_natrec; eauto.
Qed.

Lemma msubst_id : forall t, msubst id_substitution t = t.
Proof.
  induction t; simpl; try reflexivity; f_equal; assumption.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> -> strongly_normalizing t.
Proof.
  intros t T Hty. apply expression_relation_SN with (T := T).
  assert (Hp : proper_substitution id_substitution).
  { intros x. apply lc_fvar. }
  assert (Hr : related_substitution empty id_substitution).
  { intros x U H. discriminate. }
  pose proof (fundamental empty t T Hty id_substitution Hp Hr) as Hfund.
  rewrite msubst_id in Hfund. exact Hfund.
Qed.

End STLCNormalizationRecursionMediumTask.
