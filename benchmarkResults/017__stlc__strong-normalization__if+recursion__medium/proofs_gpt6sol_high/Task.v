(** STLC CBV strong-normalization benchmark, Medium variant.
    Features: if-recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Relations.Relation_Definitions Lia.
Import ListNotations.

Module STLCNormalizationIfRecursionMediumTask.

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
  .

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

Lemma lc_at_weaken : forall k j t, k <= j -> lc_at k t -> lc_at j t.
Proof.
  intros k j t Hkj H; revert j Hkj.
  induction H; intros j Hkj; eauto using lc_at with arith.
Qed.

Lemma lc_open_inv : forall k x t,
  lc_at k (open_rec k (tm_fvar x) t) -> lc_at (S k) t.
Proof.
  intros k x t; revert k x; induction t; intros k x H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E; inversion H; subst; constructor.
    + apply Nat.eqb_eq in E. lia.
    + lia.
  - inversion H; subst; constructor.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor.
  - inversion H; subst; constructor.
  - inversion H; subst; constructor.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
Qed.

Lemma fresh_list : forall L, ~ In (S (fold_right max 0 L)) L.
Proof.
  assert (forall L y, In y L -> y <= fold_right max 0 L) as Hbound.
  { intros L; induction L as [|a L IH]; simpl; intros y Hy.
    - contradiction.
    - destruct Hy as [Hy|Hy]; subst; [lia|].
      specialize (IH y Hy). lia. }
  intros L Hin. specialize (Hbound L _ Hin). lia.
Qed.

Lemma typing_lc : forall Gamma t T, has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T H; induction H; unfold locally_closed in *; eauto using lc_at.
  - constructor. apply lc_open_inv with (x := S (fold_right max 0 L)).
    apply H0. apply fresh_list.
Qed.

Lemma numeric_lc : forall n, numeric_value n -> locally_closed n.
Proof. intros n H; induction H; unfold locally_closed in *; eauto using lc_at. Qed.

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v H; inversion H; subst; eauto using numeric_lc.
  all: unfold locally_closed; constructor.
Qed.

Lemma numeric_no_step : forall n n', numeric_value n -> ~ step n n'.
Proof.
  intros n n' H; revert n'. induction H; intros n' K; inversion K; subst; eauto.
  eapply IHnumeric_value; eauto.
Qed.

Lemma value_no_step : forall v v', value v -> ~ step v v'.
Proof.
  intros v v' H; inversion H; subst.
  - intro K; inversion K.
  - intro K; inversion K.
  - intro K; inversion K.
  - eapply numeric_no_step; eauto.
Qed.

Lemma lc_open : forall k t u,
  lc_at (S k) t -> locally_closed u -> lc_at k (open_rec k u t).
Proof.
  intros k t; revert k; induction t; intros k u H Hu; simpl;
    inversion H; subst; eauto using lc_at.
  - destruct (Nat.eqb k n) eqn:E.
    + apply lc_at_weaken with (k := 0); [lia|exact Hu].
    + constructor. apply Nat.eqb_neq in E. lia.
Qed.

Lemma step_lc : forall t t', locally_closed t -> step t t' -> locally_closed t'.
Proof.
  intros t t' Hlc Hstep; revert Hlc.
  induction Hstep; intro Hlc; unfold locally_closed in *;
    inversion Hlc; subst; eauto using lc_at.
  - inversion H4; subst. eapply lc_open; eauto using value_lc.
  - repeat constructor; eauto using lc_at.
  all: apply numeric_lc; assumption.
Qed.

Lemma ser_step : forall T t t',
  strong_expression_relation T t -> step t t' -> strong_expression_relation T t'.
Proof.
  intros T t t' [Hlc [Hsn Hval]] Hstep.
  split.
  - eapply step_lc; eauto.
  - split.
    + inversion Hsn; subst; eauto.
    + intros v Hmulti Hv. apply Hval; auto.
      eapply multi_step; eauto.
Qed.

Lemma ser_value : forall T v,
  strong_value_relation T v -> strong_expression_relation T v.
Proof.
  intros T v H.
  assert (value v) as Hv by (destruct T; exact (proj1 H)).
  split; [eauto using value_lc|].
  split.
  - constructor. intros v' Hstep. exfalso. eapply value_no_step; eauto.
  - intros w Hmulti Hw. inversion Hmulti; subst; auto.
    exfalso. exact (value_no_step _ _ Hv H0).
Qed.

Lemma ser_value_inv : forall T v,
  strong_expression_relation T v -> value v -> strong_value_relation T v.
Proof.
  intros T v [_ [_ H]] Hv. apply H; auto. constructor.
Qed.

Lemma ser_intro : forall T t,
  locally_closed t ->
  (forall t', step t t' -> strong_expression_relation T t') ->
  (value t -> strong_value_relation T t) ->
  strong_expression_relation T t.
Proof.
  intros T t Hlc Hstep Hvalue. split; [exact Hlc|]. split.
  - constructor. intros t' H. exact (proj1 (proj2 (Hstep _ H))).
  - intros v Hmulti Hv. inversion Hmulti; subst.
    + apply Hvalue; auto.
    + apply (proj2 (proj2 (Hstep _ H))); auto.
Qed.

Lemma app_compat : forall A B f a,
  strong_expression_relation (Ty_Arrow A B) f ->
  strong_expression_relation A a ->
  strong_expression_relation B (tm_app f a).
Proof.
  intros A B f a Hf Ha.
  destruct Hf as [Flc [Fsn Fval]].
  revert Flc Fval a Ha.
  induction Fsn as [f Fstep IHf]; intros Flc Fval a Ha.
  destruct Ha as [Alc [Asn Aval]].
  revert Alc Aval.
  induction Asn as [a Astep IHa]; intros Alc Aval.
  apply ser_intro.
  - unfold locally_closed; constructor; assumption.
  - intros u Hu. inversion Hu; subst.
    + assert (strong_value_relation (Ty_Arrow A B) (tm_abs T t)) as HF.
      { apply Fval; auto. constructor. }
      simpl in HF. destruct HF as [_ [body [Heq Hbody]]].
      inversion Heq; subst body T.
      assert (strong_value_relation A a) as HA by (apply Aval; auto; constructor).
      destruct (Hbody a HA) as [Hlc [Hsn Hres]].
      exact (conj Hlc (conj Hsn Hres)).
    + eapply IHf.
      * exact H1.
      * eapply step_lc; [exact Flc|exact H1].
      * intros v Hv Hvalue. apply Fval; [eapply multi_step; [eassumption|exact Hv]|exact Hvalue].
      * exact (conj Alc (conj (SN_intro _ Astep) Aval)).
    + eapply IHa.
      * exact H3.
      * eapply step_lc; [exact Alc|eassumption].
      * intros v Hv Hvalue. apply Aval; [eapply multi_step; [eassumption|exact Hv]|exact Hvalue].
  - intro H; inversion H; subst; inversion H0.
Qed.

Lemma succ_compat : forall n,
  strong_expression_relation Ty_Nat n ->
  strong_expression_relation Ty_Nat (tm_succ n).
Proof.
  intros n [Nlc [Nsn Nval]]. revert Nlc Nval.
  induction Nsn as [n Nstep IH]; intros Nlc Nval.
  apply ser_intro.
  - unfold locally_closed; constructor; exact Nlc.
  - intros u Hu. inversion Hu; subst. apply IH.
    + exact H0.
    + eapply step_lc; [exact Nlc|exact H0].
    + intros v Hmulti Hv. apply Nval; [eapply multi_step; [exact H0|exact Hmulti]|exact Hv].
  - intro Hv. simpl. split; [exact Hv|]. inversion Hv; subst; assumption.
Qed.

Lemma if_compat : forall T c t e,
  strong_expression_relation Ty_Bool c ->
  strong_expression_relation T t ->
  strong_expression_relation T e ->
  strong_expression_relation T (tm_if c t e).
Proof.
  intros T c t e [Clc [Csn Cval]] Ht He.
  revert Clc Cval. induction Csn as [c Cstep IH]; intros Clc Cval.
  apply ser_intro.
  - unfold locally_closed; constructor; [exact Clc|exact (proj1 Ht)|exact (proj1 He)].
  - intros u Hu. inversion Hu; subst.
    + exact Ht.
    + exact He.
    + apply IH.
      * exact H2.
      * eapply step_lc; [exact Clc|exact H2].
      * intros v Hmulti Hv. apply Cval; [eapply multi_step; [exact H2|exact Hmulti]|exact Hv].
  - intro Hv. inversion Hv; subst; inversion H.
Qed.

Lemma numeric_svr : forall n,
  numeric_value n -> strong_value_relation Ty_Nat n.
Proof. intros n H. simpl. split; [constructor; exact H|exact H]. Qed.

Lemma svr_value : forall T v, strong_value_relation T v -> value v.
Proof. intros T v H; destruct T; exact (proj1 H). Qed.

Lemma rec_values : forall T n b s,
  numeric_value n ->
  strong_value_relation T b ->
  strong_value_relation (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  strong_expression_relation T (tm_natrec n b s).
Proof.
  intros T n b s Hn Hb Hs. revert b s Hb Hs.
  induction Hn as [|n Hn IH]; intros b s Hb Hs.
  - apply ser_intro.
    + unfold locally_closed. constructor.
      * constructor.
      * change (locally_closed b). apply value_lc. eapply svr_value; eauto.
      * change (locally_closed s). apply value_lc. eapply svr_value; eauto.
    + intros u Hu. inversion Hu; subst.
      * exfalso. eapply numeric_no_step; [constructor|eassumption].
      * exfalso. eapply value_no_step; [eapply svr_value; exact Hb|eassumption].
      * exfalso. eapply value_no_step; [eapply svr_value; exact Hs|eassumption].
      * apply ser_value; exact Hb.
    + intro Hv. inversion Hv; subst; inversion H.
  - apply ser_intro.
    + unfold locally_closed. constructor.
      * change (locally_closed (tm_succ n)). apply numeric_lc. constructor; exact Hn.
      * change (locally_closed b). apply value_lc. eapply svr_value; eauto.
      * change (locally_closed s). apply value_lc. eapply svr_value; eauto.
    + intros u Hu. inversion Hu; subst.
      * exfalso. eapply numeric_no_step; [constructor; exact Hn|eassumption].
      * exfalso. eapply value_no_step; [eapply svr_value; exact Hb|eassumption].
      * exfalso. eapply value_no_step; [eapply svr_value; exact Hs|eassumption].
      * apply app_compat with (A := T).
        -- apply app_compat with (A := Ty_Nat).
           ++ apply ser_value; exact Hs.
           ++ apply ser_value. apply numeric_svr. exact Hn.
        -- apply IH; assumption.
    + intro Hv. inversion Hv; subst; inversion H.
Qed.

Lemma rec_compat : forall T n b s,
  strong_expression_relation Ty_Nat n ->
  strong_expression_relation T b ->
  strong_expression_relation (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  strong_expression_relation T (tm_natrec n b s).
Proof.
  intros T n b s [Nlc [Nsn Nval]] Hb Hs.
  revert Nlc Nval b Hb s Hs.
  induction Nsn as [n Nstep IHn]; intros Nlc Nval b Hb s Hs.
  destruct Hb as [Blc [Bsn Bval]].
  revert Blc Bval s Hs.
  induction Bsn as [b Bstep IHb]; intros Blc Bval s Hs.
  destruct Hs as [Slc [Ssn Sval]].
  revert Slc Sval.
  induction Ssn as [s Sstep IHs]; intros Slc Sval.
  apply ser_intro.
  - unfold locally_closed; constructor; assumption.
  - intros u Hu. inversion Hu; subst.
    + apply IHn.
      * exact H2.
      * eapply step_lc; [exact Nlc|exact H2].
      * intros v Hmulti Hv. apply Nval; [eapply multi_step; [exact H2|exact Hmulti]|exact Hv].
      * exact (conj Blc (conj (SN_intro _ Bstep) Bval)).
      * exact (conj Slc (conj (SN_intro _ Sstep) Sval)).
    + apply IHb.
      * exact H4.
      * eapply step_lc; [exact Blc|exact H4].
      * intros v Hmulti Hv. apply Bval; [eapply multi_step; [exact H4|exact Hmulti]|exact Hv].
      * exact (conj Slc (conj (SN_intro _ Sstep) Sval)).
    + apply IHs.
      * exact H5.
      * eapply step_lc; [exact Slc|exact H5].
      * intros v Hmulti Hv. apply Sval; [eapply multi_step; [exact H5|exact Hmulti]|exact Hv].
    + exact (conj Blc (conj (SN_intro _ Bstep) Bval)).
    + eapply ser_step; [apply rec_values; [constructor; exact H2|..]|exact Hu].
      * apply Bval; [constructor|exact H4].
      * apply Sval; [constructor|exact H5].
  - intro Hv. inversion Hv; subst; inversion H.
Qed.

Fixpoint free_atoms (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_app t1 t2 => free_atoms t1 ++ free_atoms t2
  | tm_abs _ t1 => free_atoms t1
  | tm_true | tm_false | tm_zero => []
  | tm_succ t1 => free_atoms t1
  | tm_natrec n b s => free_atoms n ++ free_atoms b ++ free_atoms s
  | tm_if c t e => free_atoms c ++ free_atoms t ++ free_atoms e
  end.

Lemma msubst_fresh : forall t x rho v,
  ~ In x (free_atoms t) ->
  msubst (subst_update rho x v) t = msubst rho t.
Proof.
  induction t; intros x rho v Hfresh; simpl in *; try reflexivity.
  - unfold subst_update. destruct (Nat.eqb x a) eqn:E; [|reflexivity].
    apply Nat.eqb_eq in E. subst. exfalso. apply Hfresh. simpl; auto.
  - rewrite IHt1, IHt2; auto; intro Hin; apply Hfresh; apply in_or_app; auto.
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - rewrite !in_app_iff in Hfresh.
    rewrite IHt1, IHt2, IHt3; tauto.
  - rewrite !in_app_iff in Hfresh.
    rewrite IHt1, IHt2, IHt3; tauto.
Qed.

Lemma open_rec_outside : forall k t j u,
  lc_at k t -> k <= j -> open_rec j u t = t.
Proof.
  intros k t j u Hlc; revert j u.
  induction Hlc; intros j u Hle; simpl; f_equal; eauto with arith.
  - destruct (Nat.eqb j i) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
Qed.

Lemma open_rec_closed : forall k u t,
  locally_closed t -> open_rec k u t = t.
Proof.
  intros k u t Hlc. eapply open_rec_outside; [exact Hlc|lia].
Qed.

Lemma msubst_open_rec : forall t k u rho,
  proper_substitution rho ->
  msubst rho (open_rec k u t) = open_rec k (msubst rho u) (msubst rho t).
Proof.
  induction t; intros k u rho Hproper; simpl; try reflexivity.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. apply open_rec_closed. apply Hproper.
  - rewrite IHt1, IHt2; auto.
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - rewrite IHt1, IHt2, IHt3; auto.
  - rewrite IHt1, IHt2, IHt3; auto.
Qed.

Lemma msubst_open_fresh : forall t x rho v,
  proper_substitution rho ->
  locally_closed v ->
  ~ In x (free_atoms t) ->
  msubst (subst_update rho x v) (open t (tm_fvar x)) =
  open (msubst rho t) v.
Proof.
  intros t x rho v Hproper Hlc Hfresh.
  unfold open. rewrite msubst_open_rec.
  - simpl. replace (subst_update rho x v x) with v by
      (unfold subst_update; rewrite Nat.eqb_refl; reflexivity).
    rewrite msubst_fresh by exact Hfresh. reflexivity.
  - unfold proper_substitution, subst_update.
    intros y. destruct (Nat.eqb x y); auto.
Qed.

Lemma msubst_lc : forall k t rho,
  lc_at k t -> proper_substitution rho -> lc_at k (msubst rho t).
Proof.
  intros k t rho Hlc; revert rho.
  induction Hlc; intros rho Hproper; simpl; eauto using lc_at.
  - apply lc_at_weaken with (k := 0); [lia|apply Hproper].
Qed.

Lemma subst_update_proper : forall rho x v,
  proper_substitution rho -> locally_closed v ->
  proper_substitution (subst_update rho x v).
Proof.
  intros rho x v Hproper Hv y. unfold subst_update.
  destruct (Nat.eqb x y); auto.
Qed.

Lemma related_update : forall Gamma rho x T v,
  strong_related_substitution Gamma rho ->
  strong_value_relation T v ->
  strong_related_substitution (update Gamma x T) (subst_update rho x v).
Proof.
  intros Gamma rho x T v Hrel Hv y U Hlookup.
  unfold update in Hlookup. unfold subst_update.
  destruct (Nat.eqb x y) eqn:E.
  - inversion Hlookup; subst. exact Hv.
  - apply Hrel. exact Hlookup.
Qed.

Theorem fundamental : forall Gamma t T,
  has_type Gamma t T ->
  forall rho,
    proper_substitution rho ->
    strong_related_substitution Gamma rho ->
    strong_expression_relation T (msubst rho t).
Proof.
  intros Gamma t T Htyping. induction Htyping; intros rho Hproper Hrelated; simpl.
  - apply ser_value. apply Hrelated. exact H.
  - apply ser_value. simpl. split.
    + apply v_abs. change (lc_at 0 (msubst rho (tm_abs T1 t1))).
      eapply msubst_lc; [eapply typing_lc; eapply T_Abs; exact H|exact Hproper].
    + exists (msubst rho t1). split; [reflexivity|].
      intros arg Harg.
      set (x := S (fold_right max 0 (L ++ free_atoms t1))).
      assert (~ In x (L ++ free_atoms t1)) as Hfresh by (unfold x; apply fresh_list).
      rewrite in_app_iff in Hfresh.
      assert (~ In x L) as HfreshL by tauto.
      assert (~ In x (free_atoms t1)) as HfreshT by tauto.
      pose proof (value_lc arg (svr_value _ _ Harg)) as Harglc.
      pose proof (H0 x HfreshL (subst_update rho x arg)
                    (subst_update_proper _ _ _ Hproper Harglc)
                    (related_update _ _ _ _ _ Hrelated Harg)) as Hbody.
      rewrite (msubst_open_fresh t1 x rho arg Hproper Harglc HfreshT) in Hbody.
      exact Hbody.
  - eapply app_compat; eauto.
  - apply ser_value. simpl. split; [constructor|left; reflexivity].
  - apply ser_value. simpl. split; [constructor|right; reflexivity].
  - apply ser_value. apply numeric_svr. constructor.
  - apply succ_compat. exact (IHHtyping rho Hproper Hrelated).
  - eapply rec_compat; eauto.
  - eapply if_compat; eauto.
Qed.

Lemma free_atoms_open : forall t k u x,
  In x (free_atoms t) -> In x (free_atoms (open_rec k u t)).
Proof.
  induction t; intros k u x Hin; simpl in *; try contradiction; auto;
    repeat rewrite in_app_iff in *; intuition eauto.
Qed.

Lemma typing_support : forall Gamma t T,
  has_type Gamma t T ->
  forall z, In z (free_atoms t) -> exists U, Gamma z = Some U.
Proof.
  intros Gamma t T Htyping; induction Htyping; intros z Hin; simpl in Hin;
    try contradiction.
  - exists T. destruct Hin as [Heq|[]]. subst; exact H.
  - set (x := S (fold_right max 0 (z :: L))).
    assert (~ In x (z :: L)) as Hfresh by (unfold x; apply fresh_list).
    assert (~ In x L) as HfreshL by (intro Hx; apply Hfresh; right; exact Hx).
    assert (x <> z) as Hneq by (intro Heq; apply Hfresh; left; symmetry; exact Heq).
    destruct (H0 x HfreshL z (free_atoms_open _ _ _ _ Hin)) as [U HU].
    exists U. unfold update in HU.
    apply Nat.eqb_neq in Hneq. rewrite Hneq in HU. exact HU.
  - rewrite in_app_iff in Hin. destruct Hin as [Hin|Hin]; eauto.
  - eapply IHHtyping; exact Hin.
  - repeat rewrite in_app_iff in Hin. destruct Hin as [Hin|[Hin|Hin]]; eauto.
  - repeat rewrite in_app_iff in Hin. destruct Hin as [Hin|[Hin|Hin]]; eauto.
Qed.

Lemma msubst_no_free : forall t rho,
  (forall x, ~ In x (free_atoms t)) -> msubst rho t = t.
Proof.
  induction t; intros rho Hfree; simpl in *; try reflexivity.
  - exfalso. apply (Hfree a). simpl; auto.
  - f_equal; [apply IHt1|apply IHt2]; intros x Hin;
      apply (Hfree x); rewrite in_app_iff; auto.
  - f_equal. apply IHt. exact Hfree.
  - f_equal. apply IHt. exact Hfree.
  - f_equal; [apply IHt1|apply IHt2|apply IHt3]; intros x Hin;
      apply (Hfree x); repeat rewrite in_app_iff; tauto.
  - f_equal; [apply IHt1|apply IHt2|apply IHt3]; intros x Hin;
      apply (Hfree x); repeat rewrite in_app_iff; tauto.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Htyping.
  set (rho := fun _ : atom => tm_true).
  assert (proper_substitution rho) as Hproper.
  { intros x. unfold rho, locally_closed. constructor. }
  assert (strong_related_substitution empty rho) as Hrelated.
  { intros x U Hlookup. discriminate Hlookup. }
  pose proof (fundamental empty t T Htyping rho Hproper Hrelated) as Hfund.
  assert (msubst rho t = t) as Hclosed.
  { apply msubst_no_free. intros x Hin.
    destruct (typing_support empty t T Htyping x Hin) as [U HU].
    discriminate HU. }
  rewrite Hclosed in Hfund. exact (proj1 (proj2 Hfund)).
Qed.

End STLCNormalizationIfRecursionMediumTask.
