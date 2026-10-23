(** STLC CBV strong-normalization benchmark, Medium variant.
    Features: if-nondeterminism-recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Relations.Relation_Definitions Lia.
From Stdlib Require Import Program.Equality.
Import ListNotations.

Module STLCNormalizationIfNondeterminismRecursionMediumTask.

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
  | tm_if : tm -> tm -> tm -> tm
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

Notation "'if' t1 'then' t2 'else' t3" := (tm_if t1 t2 t3)
  (in custom stlc_tm at level 200,
   t1 custom stlc_tm, t2 custom stlc_tm, t3 custom stlc_tm at level 200) : stlc_scope.
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
  | tm_if t1 t2 t3 => tm_if (open_rec k u t1) (open_rec k u t2) (open_rec k u t3)
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
  | lc_if : forall k t1 t2 t3,
      lc_at k t1 -> lc_at k t2 -> lc_at k t3 -> lc_at k (tm_if t1 t2 t3)
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
  | T_If : forall Gamma t1 t2 t3 T,
      <{ Gamma |-- $(t1) \in Bool }> ->
      <{ Gamma |-- $(t2) \in T }> ->
      <{ Gamma |-- $(t3) \in T }> ->
      <{ Gamma |-- $(tm_if t1 t2 t3) \in T }>
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
  | tm_if t1 t2 t3 => tm_if (msubst rho t1) (msubst rho t2) (msubst rho t3)
  | tm_choice t1 t2 => tm_choice (msubst rho t1) (msubst rho t2)
  end.

Definition proper_substitution (rho : term_substitution) : Prop :=
  forall x, locally_closed (rho x).

Fixpoint strong_value_relation (T : ty) (v : tm) : Prop :=
  value v /\
  match T with
  | Ty_Nat => numeric_value v
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

Definition strong_related_substitution
    (Gamma : context) (rho : term_substitution) : Prop :=
  forall x T,
    Gamma x = Some T ->
    strong_value_relation T (rho x).

Lemma multi_trans : forall (A : Type) (R : relation A) x y z,
  multi R x y -> multi R y z -> multi R x z.
Proof.
  intros A R x y z h.
  induction h; eauto using multi.
Qed.

Lemma multi_left : forall (A : Type) (R : relation A) x y z,
  R x y -> multi R y z -> multi R x z.
Proof. eauto using multi. Qed.

Lemma SN_inv : forall t t', strongly_normalizing t -> t --> t' ->
  strongly_normalizing t'.
Proof.
  intros t t' h.
  inversion h; eauto.
Qed.

Lemma numeric_no_step : forall n, numeric_value n ->
  forall n', ~ n --> n'.
Proof.
  intros n hn; induction hn as [| n hn IH].
  - intros n' hs. inversion hs.
  - intros n' hs. inversion hs; subst. exact (IH t' H0).
Qed.

Lemma value_no_step : forall v v', value v -> ~ v --> v'.
Proof.
  intros v v' hv.
  induction hv as [T t hlc | | | n hnv].
  - intros hs. inversion hs.
  - intros hs. inversion hs.
  - intros hs. inversion hs.
  - eauto using numeric_no_step.
Qed.

Lemma value_sn : forall v, value v -> strongly_normalizing v.
Proof.
  intros v hv. constructor. intros v' hs.
  exfalso. eapply value_no_step; eauto.
Qed.

Lemma lc_mono : forall k t, lc_at k t -> lc_at (S k) t.
Proof.
  intros k t h; induction h; eauto; constructor; lia.
Qed.

Lemma lc_open_rec : forall k u t,
  lc_at (S k) t -> lc_at k u -> lc_at k (open_rec k u t).
Proof.
  intros k u t.
  revert k u.
  induction t as [i | x | t1 IH1 t2 IH2 | T t IH |
                  | | | t IHs | n IHn b IHb s IHs0 |
                  t1 IHif1 t2 IHif2 t3 IHif3 |
                  t1 IHc1 t2 IHc2];
    intros k u h hu; inversion h; simpl.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E; subst; assumption.
    + constructor. apply Nat.eqb_neq in E. lia.
  - constructor.
  - constructor; eauto.
  - constructor. eapply IH; eauto using lc_mono.
  - constructor.
  - constructor.
  - constructor.
  - constructor; eauto using IHs.
  - constructor; eauto using IHn, IHb, IHs0.
  - constructor; eauto using IHif1, IHif2, IHif3.
  - constructor; eauto using IHc1, IHc2.
Qed.

Lemma lc_abs_body : forall k T t,
  lc_at k (tm_abs T t) -> lc_at (S k) t.
Proof. intros k T t h; inversion h; assumption. Qed.

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v hv; induction hv as [T t hlc | | | n hn].
  - exact hlc.
  - constructor.
  - constructor.
  - induction hn as [| n hn IH].
    + constructor.
    + constructor. exact IH.
Qed.

Lemma step_lc : forall t t', locally_closed t -> t --> t' -> locally_closed t'.
Proof.
  intros t t' hlt hs.
  induction hs as
    [T t v Habs Hv
    | t1 t1' t2 Hstep IHstep Ht2
    | v1 t2 t2' Hv1 Hstep IHstep
    | t t' Hstep IHstep
    | n n' b s Hstep IHstep Hb Hs
    | n b b' s Hn Hstep IHstep Hs
    | n b s s' Hn Hb Hstep IHstep
    | b s Hb Hs
    | n b s Hn Hb Hs
    | t1 t2 Ht1 Ht2
    | t1 t2 Ht1 Ht2
    | t1 t1' t2 t3 Hstep IHstep Ht2 Ht3
    | t1 t2 Ht1 Ht2
    | t1 t2 Ht1 Ht2]; simpl in *.
  - apply lc_open_rec with (k := 0).
    + eapply lc_abs_body; eauto.
    + eapply value_lc; eauto.
  - constructor.
    + apply IHstep. inversion hlt; assumption.
    + inversion hlt; assumption.
  - constructor.
    + eapply value_lc; eauto.
    + apply IHstep. inversion hlt; assumption.
  - constructor. apply IHstep. inversion hlt; assumption.
  - constructor.
    + apply IHstep. inversion hlt; assumption.
    + inversion hlt; assumption.
    + inversion hlt; assumption.
  - constructor.
    + inversion hlt; assumption.
    + apply IHstep. inversion hlt; assumption.
    + inversion hlt; assumption.
  - constructor.
    + inversion hlt; assumption.
    + inversion hlt; assumption.
    + apply IHstep. inversion hlt; assumption.
  - eauto using value_lc.
  - constructor.
    + constructor.
      * eapply value_lc; eauto.
      * eapply value_lc; eauto.
    + constructor.
      * exact (value_lc _ (v_nat n Hn)).
      * exact (value_lc _ Hb).
      * exact (value_lc _ Hs).
  - exact Ht1.
  - exact Ht2.
  - constructor.
    + apply IHstep. inversion hlt; assumption.
    + inversion hlt; assumption.
    + inversion hlt; assumption.
  - exact Ht1.
  - exact Ht2.
Qed.

Lemma multi_value_eq : forall v w,
  value v -> v -->* w -> w = v.
Proof.
  intros v w hv h.
  induction h; eauto.
  exfalso. eapply value_no_step; eauto.
Qed.

Lemma sv_sn : forall T v, strong_value_relation T v ->
  strongly_normalizing v.
Proof. intros T v h; destruct T; simpl in h; apply value_sn; exact (proj1 h). Qed.

Lemma sv_lc : forall T v, strong_value_relation T v -> locally_closed v.
Proof. intros T v h; destruct T; simpl in h; apply value_lc; exact (proj1 h). Qed.

Lemma expr_reduct : forall T t t',
  strong_expression_relation T t -> t --> t' ->
  strong_expression_relation T t'.
Proof.
  intros T t t' [hlt [hsn hterm]] hs.
  constructor.
  - apply step_lc with (t := t); assumption.
  - constructor.
    + apply (SN_inv t t' hsn hs).
    + intros v hm hv.
      apply hterm with (v := v).
      exact (@multi_step tm step t t' v hs hm).
  all: eauto.
Qed.

Lemma expr_value : forall T v,
  strong_expression_relation T v -> value v ->
  strong_value_relation T v.
Proof.
  intros T v [_ [_ h]] hv. exact (h v (@multi_refl tm step v) hv).
Qed.

Lemma expr_of_value : forall T v,
  strong_value_relation T v -> strong_expression_relation T v.
Proof.
  intros T v hv.
  assert (value v) as hvv.
  { destruct T; simpl in hv; exact (proj1 hv). }
  constructor.
  - exact (sv_lc T v hv).
  - constructor.
    + exact (sv_sn T v hv).
    + intros w hm hw.
      rewrite (multi_value_eq v w hvv hm) in *.
      exact hv.
Qed.

Lemma SN_ind : forall (P : tm -> Prop),
  (forall t, (forall t', t --> t' -> P t') -> P t) ->
  forall t, strongly_normalizing t -> P t.
Proof.
  intros P H t hs.
  induction hs. apply H. assumption.
Qed.

Lemma app_sn : forall T1 T2 f a,
  strong_expression_relation (Ty_Arrow T1 T2) f ->
  strong_expression_relation T1 a ->
  strongly_normalizing (tm_app f a).
Proof.
  intros T1 T2 f a ef ea.
  pose proof ef as ef0.
  destruct ef as [lcf0 [snf0 fterm0]].
  assert (Hall : forall a,
      strong_expression_relation T1 a -> strongly_normalizing (tm_app f a)).
  {
  refine ((SN_ind
    (fun f => strong_expression_relation (Ty_Arrow T1 T2) f ->
      forall a, strong_expression_relation T1 a ->
        strongly_normalizing (tm_app f a))
    _ f snf0) ef0).
  intros f' IHf ef a' ea'.
  pose proof ef as ef1.
  destruct ef as [lcf1 [snf1 fterm1]].
  refine ((SN_ind
    (fun a => strong_expression_relation T1 a ->
      strongly_normalizing (tm_app f' a)) _ a' (proj1 (proj2 ea'))) ea').
  intros a'' IHa ea''.
  pose proof ea'' as ea1.
  destruct ea'' as [lca [sna aterm]].
  constructor. intros r hs.
  inversion hs; subst.
  - destruct (@expr_value (Ty_Arrow T1 T2) (tm_abs T t) ef1
        (v_abs T t H1)) as [Hv [body [He Hbody]]].
    inversion He; subst.
    destruct (Hbody a'' (@expr_value T1 a'' ea1 H3)) as [_ [hsn _]].
    exact hsn.
  - apply IHf with (a := a'').
    + exact H1.
    + exact (expr_reduct (Ty_Arrow T1 T2) f' t1' ef1 H1).
    + exact ea1.
  - apply IHa.
    + exact H3.
    + exact (expr_reduct T1 a'' t2' ea1 H3).
  }
  exact (Hall a ea).
Qed.

Lemma no_value_app : forall f a, ~ value (tm_app f a).
Proof.
  intros f a H.
  inversion H; inversion H0.
Qed.

Lemma multi_cases : forall x y, x -->* y ->
  x = y \/ exists z, x --> z /\ z -->* y.
Proof.
  intros x y h; inversion h.
  - left; reflexivity.
  - right; eauto.
Qed.

Lemma app_term : forall T1 T2 f a,
  strong_expression_relation (Ty_Arrow T1 T2) f ->
  strong_expression_relation T1 a ->
  forall v, tm_app f a -->* v -> value v ->
    strong_value_relation T2 v.
Proof.
  intros T1 T2 f a ef ea.
  assert (Hall : forall a, strong_expression_relation T1 a ->
      forall v, tm_app f a -->* v -> value v -> strong_value_relation T2 v).
  {
  refine (SN_ind
    (fun f => strong_expression_relation (Ty_Arrow T1 T2) f ->
      forall a, strong_expression_relation T1 a ->
      forall v, tm_app f a -->* v -> value v -> strong_value_relation T2 v)
    _ f (proj1 (proj2 ef)) ef).
  intros f' IHf ef' a' ea' v hm hv.
  assert (Hall2 : forall v, tm_app f' a' -->* v -> value v ->
      strong_value_relation T2 v).
  {
  refine (SN_ind
    (fun a => strong_expression_relation T1 a ->
      forall v, tm_app f' a -->* v -> value v -> strong_value_relation T2 v)
    _ a' (proj1 (proj2 ea')) ea').
  intros a'' IHa ea'' vi hmi hvi.
  destruct (multi_cases (tm_app f' a'') vi hmi) as [Heq | [q' [hs hmulti]]].
  - subst. exact (False_rect _ ((no_value_app f' a'') hvi)).
  - inversion hs; subst.
    + destruct (@expr_value (Ty_Arrow T1 T2) (tm_abs T t) ef'
        (v_abs T t H1)) as [Hv [body [He Hbody]]].
      inversion He; subst.
      apply Hbody with (arg := a'') (result := vi).
      exact (@expr_value T1 a'' ea'' H3).
      exact hmulti.
      exact hvi.
    + eapply IHf.
      exact H1.
      exact (expr_reduct (Ty_Arrow T1 T2) f' _ ef' H1).
      exact ea''.
      exact hmulti.
      exact hvi.
    + eapply IHa.
      exact H3.
      exact (expr_reduct T1 a'' _ ea'' H3).
      exact hmulti.
      exact hvi.
  }
  exact (Hall2 v hm hv).
  }
  exact (Hall a ea).
Qed.

Lemma app_expr : forall T1 T2 f a,
  strong_expression_relation (Ty_Arrow T1 T2) f ->
  strong_expression_relation T1 a ->
  strong_expression_relation T2 (tm_app f a).
Proof.
  intros T1 T2 f a ef ea.
  pose proof ef as ef0.
  pose proof ea as ea0.
  destruct ef as [lcf [snf fterm]].
  destruct ea as [lca [sna aterm]].
  constructor.
  - constructor; assumption.
  - constructor.
    + exact (app_sn T1 T2 f a
        (conj lcf (conj snf fterm))
        (conj lca (conj sna aterm))).
    + intros v hm hv.
      apply (app_term T1 T2 f a ef0 ea0 v hm hv).
Qed.

Fixpoint fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ => [] | tm_fvar x => [x]
  | tm_app t1 t2 => fv t1 ++ fv t2
  | tm_abs _ t1 => fv t1
  | tm_true | tm_false | tm_zero => []
  | tm_succ t1 => fv t1
  | tm_natrec n b s => fv n ++ fv b ++ fv s
  | tm_if t1 t2 t3 => fv t1 ++ fv t2 ++ fv t3
  | tm_choice t1 t2 => fv t1 ++ fv t2
  end.

Lemma typing_lc : forall G t T, <{ G |-- t \in T }> -> locally_closed t.
Proof.
  intros G t T h; induction h; simpl; eauto.
  all: try constructor; eauto.
Qed.

Lemma msubst_lc : forall k rho t,
  (forall x, locally_closed (rho x)) -> lc_at k t -> lc_at k (msubst rho t).
Proof.
  intros k rho t hp h; induction h; simpl; eauto using hp.
Qed.

Lemma msubst_open_fresh : forall rho x k t,
  ~ In x (fv t) ->
  msubst rho (open_rec k (tm_fvar x) t) =
  open_rec k (rho x) (msubst rho t).
Proof.
  intros rho x k t; revert k.
  induction t; simpl; intros k hf; try reflexivity.
  - destruct (Nat.eqb k n); reflexivity.
  - destruct (Nat.eqb x a); simpl in hf; contradiction.
  - f_equal; eauto using IHt1, IHt2.
  - f_equal; apply IHt; assumption.
  - f_equal; eauto using IHt.
  - f_equal; eauto using IHt1, IHt2, IHt3.
  - f_equal; eauto using IHt1, IHt2.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  (* Complete the proof of normalization. *)
Qed.

End STLCNormalizationIfNondeterminismRecursionMediumTask.
