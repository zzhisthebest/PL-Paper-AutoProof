(** STLC CBV strong-normalization benchmark, Easy variant.
    Features: if-nondeterminism-recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Relations.Relation_Definitions Lia.
Import ListNotations.

Module STLCNormalizationIfNondeterminismRecursionEasyTask.

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

Fixpoint free_vars (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_app t1 t2 => free_vars t1 ++ free_vars t2
  | tm_abs _ t1 => free_vars t1
  | tm_true => []
  | tm_false => []
  | tm_zero => []
  | tm_succ t1 => free_vars t1
  | tm_natrec n b s => free_vars n ++ free_vars b ++ free_vars s
  | tm_if t1 t2 t3 => free_vars t1 ++ free_vars t2 ++ free_vars t3
  | tm_choice t1 t2 => free_vars t1 ++ free_vars t2
  end.

Fixpoint numeral (n : nat) : tm :=
  match n with
  | O => tm_zero
  | S m => tm_succ (numeral m)
  end.

Lemma update_eq : forall Gamma x T,
  update Gamma x T x = Some T.
Proof.
  intros. unfold update. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma update_neq : forall Gamma x y T,
  x <> y ->
  update Gamma x T y = Gamma y.
Proof.
  intros. unfold update.
  destruct (Nat.eqb x y) eqn:Heq.
  - apply Nat.eqb_eq in Heq. contradiction.
  - reflexivity.
Qed.

Fixpoint max_atom (L : list atom) : atom :=
  match L with
  | [] => 0
  | x :: L' => Nat.max x (max_atom L')
  end.

Definition fresh (L : list atom) : atom := S (max_atom L).

Lemma in_le_max_atom : forall x L,
  In x L -> x <= max_atom L.
Proof.
  induction L; simpl; intros.
  - contradiction.
  - destruct H as [H | H].
    + subst. lia.
    + specialize (IHL H). lia.
Qed.

Lemma fresh_notin : forall L,
  ~ In (fresh L) L.
Proof.
  unfold fresh. intros L H.
  pose proof (in_le_max_atom _ _ H). lia.
Qed.

Lemma lc_at_weaken : forall k j t,
  lc_at k t ->
  k <= j ->
  lc_at j t.
Proof.
  intros k j t H.
  generalize dependent j.
  induction H; intros j Hle; eauto using lc_at.
  - apply lc_bvar. lia.
  - apply lc_abs. apply IHlc_at. lia.
Qed.

Lemma term_lc_at : forall k t,
  locally_closed t ->
  lc_at k t.
Proof.
  unfold locally_closed. intros. eapply lc_at_weaken; eauto. lia.
Qed.

Lemma numeric_value_lc : forall n,
  numeric_value n -> locally_closed n.
Proof.
  intros n H. induction H; constructor; assumption.
Qed.

Lemma value_regular : forall v,
  value v -> locally_closed v.
Proof.
  intros v H. destruct H.
  - assumption.
  - apply lc_true.
  - apply lc_false.
  - apply numeric_value_lc. assumption.
Qed.

Lemma numeral_numeric : forall n, numeric_value (numeral n).
Proof.
  induction n; simpl; constructor; assumption.
Qed.

Lemma numeric_numeral : forall t,
  numeric_value t -> exists n : nat, t = numeral n.
Proof.
  intros t H. induction H.
  - exists 0. reflexivity.
  - destruct IHnumeric_value as [m ->]. exists (S m). reflexivity.
Qed.

Lemma open_rec_preserves_lc_at : forall t k u,
  lc_at (S k) t ->
  locally_closed u ->
  lc_at k (open_rec k u t).
Proof.
  induction t; intros k u Hlc Hu; simpl in *; inversion Hlc; subst; eauto using lc_at.
  - destruct (Nat.eqb k n) eqn:Heq.
    + apply term_lc_at. exact Hu.
    + apply Nat.eqb_neq in Heq. apply lc_bvar. lia.
Qed.

Lemma open_preserves_term : forall t u,
  lc_at 1 t ->
  locally_closed u ->
  locally_closed (open t u).
Proof.
  unfold open, locally_closed. intros.
  apply open_rec_preserves_lc_at; assumption.
Qed.

Lemma lc_at_open_inv : forall t k u,
  lc_at k (open_rec k u t) ->
  lc_at (S k) t.
Proof.
  induction t; intros k u Hlc; simpl in *.
  - destruct (Nat.eqb k n) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst. apply lc_bvar. lia.
    + inversion Hlc; subst. apply lc_bvar. lia.
  - apply lc_fvar.
  - inversion Hlc; subst. eauto using lc_at.
  - inversion Hlc; subst. apply lc_abs. apply (IHt (S k) u). assumption.
  - apply lc_true.
  - apply lc_false.
  - apply lc_zero.
  - inversion Hlc; subst. eauto using lc_at.
  - inversion Hlc; subst. eauto using lc_at.
  - inversion Hlc; subst. eauto using lc_at.
  - inversion Hlc; subst. eauto using lc_at.
Qed.

Lemma typing_regular : forall Gamma t T,
  <{ Gamma |-- t \in T }> ->
  locally_closed t.
Proof.
  intros Gamma t T Ht.
  induction Ht.
  - unfold locally_closed. apply lc_fvar.
  - unfold locally_closed. apply lc_abs.
    pose (x := fresh L).
    assert (Hfresh : ~ In x L) by (unfold x; apply fresh_notin).
    specialize (H0 x Hfresh).
    apply lc_at_open_inv with (u := tm_fvar x).
    exact H0.
  - unfold locally_closed. apply lc_app; assumption.
  - unfold locally_closed. apply lc_true.
  - unfold locally_closed. apply lc_false.
  - apply lc_zero.
  - apply lc_succ. assumption.
  - apply lc_rec; assumption.
  - apply lc_if; assumption.
  - apply lc_choice; assumption.
Qed.

Lemma numeric_no_step : forall n,
  numeric_value n -> forall t, ~ (n --> t).
Proof.
  intros n Hn. induction Hn; intros u Hs; inversion Hs; subst.
  eapply IHHn. eassumption.
Qed.

Lemma value_no_step : forall v,
  value v -> forall t, ~ (v --> t).
Proof.
  intros v Hv t Hs. destruct Hv; try solve [inversion Hs].
  eapply numeric_no_step; eauto.
Qed.

Lemma open_rec_lc_at : forall k t j u,
  lc_at k t ->
  k <= j ->
  open_rec j u t = t.
Proof.
  intros k t j u Hlc.
  generalize dependent j.
  induction Hlc; intros j Hle; simpl.
  - destruct (Nat.eqb j i) eqn:Heq.
    + apply Nat.eqb_eq in Heq. lia.
    + reflexivity.
  - reflexivity.
  - rewrite IHHlc1 by assumption.
    rewrite IHHlc2 by assumption.
    reflexivity.
  - rewrite IHHlc by lia. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHHlc by assumption. reflexivity.
  - rewrite IHHlc1 by assumption.
    rewrite IHHlc2 by assumption.
    rewrite IHHlc3 by assumption. reflexivity.
  - rewrite IHHlc1, IHHlc2, IHHlc3 by assumption. reflexivity.
  - rewrite IHHlc1, IHHlc2 by assumption. reflexivity.
Qed.

Lemma open_rec_term : forall t j u,
  locally_closed t ->
  open_rec j u t = t.
Proof.
  unfold locally_closed. intros.
  eapply open_rec_lc_at; eauto. lia.
Qed.

Lemma msubst_preserves_lc_at : forall rho k t,
  proper_substitution rho ->
  lc_at k t ->
  lc_at k (msubst rho t).
Proof.
  intros rho k t Hproper Hlc.
  induction Hlc; simpl; eauto using lc_at.
  - apply term_lc_at. apply Hproper.
Qed.

Lemma msubst_preserves_term : forall rho t,
  proper_substitution rho ->
  locally_closed t ->
  locally_closed (msubst rho t).
Proof.
  unfold locally_closed. intros.
  eapply msubst_preserves_lc_at; eauto.
Qed.

Lemma proper_update : forall rho x v,
  proper_substitution rho ->
  locally_closed v ->
  proper_substitution (subst_update rho x v).
Proof.
  unfold proper_substitution, subst_update.
  intros rho x v Hproper Hv y.
  destruct (Nat.eqb x y); auto.
Qed.

Lemma notin_app_split : forall (x : atom) L1 L2,
  ~ In x (L1 ++ L2) ->
  ~ In x L1 /\ ~ In x L2.
Proof.
  intros x L1 L2 H.
  split; intro Hin; apply H; apply in_app_iff; auto.
Qed.

Lemma msubst_open_update_rec : forall t rho x v k,
  ~ In x (free_vars t) ->
  proper_substitution rho ->
  locally_closed v ->
  msubst (subst_update rho x v) (open_rec k (tm_fvar x) t) =
  open_rec k v (msubst rho t).
Proof.
  induction t; intros rho x v k Hfresh Hproper Hv; simpl in *.
  - destruct (Nat.eqb k n) eqn:Heq.
    + unfold subst_update. simpl.
      destruct (Nat.eqb x x) eqn:Hxx.
      * reflexivity.
      * apply Nat.eqb_neq in Hxx. contradiction.
    + reflexivity.
  - destruct (Nat.eqb x a) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst a. contradiction Hfresh. simpl. auto.
    + unfold subst_update. rewrite Heq.
      symmetry. apply open_rec_term. apply Hproper.
  - apply notin_app_split in Hfresh as [Hfresh1 Hfresh2].
    rewrite IHt1 by assumption.
    rewrite IHt2 by assumption.
    reflexivity.
  - rewrite IHt by assumption. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHt by assumption. reflexivity.
  - apply notin_app_split in Hfresh as [Hfresh1 Hfresh23].
    apply notin_app_split in Hfresh23 as [Hfresh2 Hfresh3].
    rewrite IHt1 by assumption.
    rewrite IHt2 by assumption.
    rewrite IHt3 by assumption. reflexivity.
  - apply notin_app_split in Hfresh as [Hfresh1 Hfresh23].
    apply notin_app_split in Hfresh23 as [Hfresh2 Hfresh3].
    rewrite IHt1, IHt2, IHt3 by assumption. reflexivity.
  - apply notin_app_split in Hfresh as [Hfresh1 Hfresh2].
    rewrite IHt1, IHt2 by assumption. reflexivity.
Qed.

Lemma msubst_open_update : forall t rho x v,
  ~ In x (free_vars t) ->
  proper_substitution rho ->
  locally_closed v ->
  msubst (subst_update rho x v) (open t (tm_fvar x)) =
  open (msubst rho t) v.
Proof.
  unfold open. intros.
  apply msubst_open_update_rec; assumption.
Qed.

Lemma msubst_id : forall t,
  msubst id_substitution t = t.
Proof.
  induction t; simpl; try rewrite IHt; try rewrite IHt1; try rewrite IHt2; try rewrite IHt3;
    reflexivity.
Qed.

Lemma id_substitution_proper :
  proper_substitution id_substitution.
Proof.
  unfold proper_substitution, id_substitution, locally_closed.
  intros. apply lc_fvar.
Qed.

Lemma step_preserves_lc : forall t t',
  t --> t' -> locally_closed t -> locally_closed t'.
Proof.
  intros t t' Hstep Hlc.
  unfold locally_closed in *.
  induction Hstep; inversion Hlc; subst; eauto 8 using lc_at, value_regular, numeric_value_lc.
  apply open_preserves_term.
  - unfold locally_closed in H. inversion H. assumption.
  - apply value_regular. exact H0.
  - apply lc_app.
    + apply lc_app.
      * exact H8.
      * apply numeric_value_lc. exact H.
    + apply lc_rec.
      * apply numeric_value_lc. exact H.
      * exact H7.
      * exact H8.
Qed.

Lemma sn_step : forall t t',
  strongly_normalizing t ->
  t --> t' ->
  strongly_normalizing t'.
Proof.
  intros t t' Hsn Hstep.
  inversion Hsn as [t0 Hnext].
  apply Hnext. exact Hstep.
Qed.

Lemma value_multi_eq : forall v t,
  value v ->
  v -->* t ->
  t = v.
Proof.
  intros v t Hv Hmulti.
  inversion Hmulti; subst.
  - reflexivity.
  - exfalso. eapply value_no_step; eauto.
Qed.

Lemma value_sn : forall v,
  value v ->
  strongly_normalizing v.
Proof.
  intros v Hv.
  apply SN_intro. intros t Hstep.
  exfalso. eapply value_no_step; eauto.
Qed.

Lemma strong_value_relation_value : forall T v,
  strong_value_relation T v -> value v.
Proof.
  intros T v H. destruct T; simpl in H; tauto.
Qed.

Lemma strong_value_relation_lc : forall T v,
  strong_value_relation T v -> locally_closed v.
Proof.
  intros T v H.
  apply value_regular.
  eapply strong_value_relation_value. exact H.
Qed.

Lemma strong_value_is_expression : forall T v,
  strong_value_relation T v ->
  strong_expression_relation T v.
Proof.
  intros T v Hv.
  split.
  - eapply strong_value_relation_lc. exact Hv.
  - split.
    + apply value_sn. eapply strong_value_relation_value. exact Hv.
    + intros v' Hmulti Hvalue.
      assert (v' = v).
      {
        eapply value_multi_eq.
        - eapply strong_value_relation_value. exact Hv.
        - exact Hmulti.
      }
      subst v'. exact Hv.
Qed.

Lemma strong_expression_step : forall T t t',
  strong_expression_relation T t ->
  t --> t' ->
  strong_expression_relation T t'.
Proof.
  intros T t t' [Hlc [Hsn Hall]] Hstep.
  split.
  - eapply step_preserves_lc; eauto.
  - split.
    + eapply sn_step; eauto.
    + intros v Hmulti Hv.
      apply Hall with (v := v); auto.
      eapply multi_step; eauto.
Qed.

Lemma strong_expression_of_reducts : forall T t,
  locally_closed t ->
  ~ value t ->
  (forall t', t --> t' -> strong_expression_relation T t') ->
  strong_expression_relation T t.
Proof.
  intros T t Hlc Hnotvalue Hnext.
  split. exact Hlc.
  split.
  - apply SN_intro. intros t' Hstep.
    destruct (Hnext t' Hstep) as [_ [Hsn _]]. exact Hsn.
  - intros v Hmulti Hv.
    inversion Hmulti; subst.
    + contradiction.
    + destruct (Hnext y H) as [_ [_ Hall]].
      eapply Hall; eauto.
Qed.

Lemma strong_related_update : forall Gamma rho x T v,
  strong_related_substitution Gamma rho ->
  strong_value_relation T v ->
  strong_related_substitution
    (update Gamma x T) (subst_update rho x v).
Proof.
  unfold strong_related_substitution, subst_update, update.
  intros Gamma rho x T v Hrel HV y U Hy.
  destruct (Nat.eqb x y) eqn:Heq.
  - apply Nat.eqb_eq in Heq. subst y.
    injection Hy as ->. exact HV.
  - apply Hrel. exact Hy.
Qed.

Lemma strong_empty_related :
  strong_related_substitution empty id_substitution.
Proof.
  unfold strong_related_substitution, empty.
  intros. discriminate H.
Qed.

Lemma strong_expression_intro : forall T t,
  locally_closed t ->
  (value t -> strong_value_relation T t) ->
  (forall u, t --> u -> strong_expression_relation T u) ->
  strong_expression_relation T t.
Proof.
  intros T t Hlc HV Hnext. split. exact Hlc.
  split.
  - apply SN_intro. intros u Hstep.
    destruct (Hnext u Hstep) as [_ [Hsn _]]. exact Hsn.
  - intros v Hsteps Hv. inversion Hsteps; subst.
    + apply HV. exact Hv.
    + destruct (Hnext y H) as [_ [_ Hall]]. eapply Hall; eauto.
Qed.

Lemma multi_succ_inv : forall t v,
  tm_succ t -->* v -> exists u, t -->* u /\ v = tm_succ u.
Proof.
  intros t v Hm. remember (tm_succ t) as z eqn:Ez. generalize dependent t.
  induction Hm; intros t Ez.
  - inversion Ez; subst. exists t. split; [apply multi_refl|reflexivity].
  - inversion Ez; subst. inversion H; subst. destruct (IHHm _ eq_refl) as [u [Hu Heq]].
    exists u. split; [eapply multi_step; eauto|exact Heq].
Qed.

Lemma sn_succ : forall t,
  strongly_normalizing t -> strongly_normalizing (tm_succ t).
Proof.
  intros t Hsn. induction Hsn as [t Hnext IH].
  apply SN_intro. intros u Hu. inversion Hu; subst.
  apply IH. assumption.
Qed.

Lemma strong_succ : forall t,
  strong_expression_relation Ty_Nat t ->
  strong_expression_relation Ty_Nat (tm_succ t).
Proof.
  intros t [Hlc [Hsn Hall]].
  assert (Hsn' : strongly_normalizing (tm_succ t)) by (apply sn_succ; exact Hsn).
  split.
  - unfold locally_closed. apply lc_succ. exact Hlc.
  - split; [exact Hsn'|].
    intros v Hmulti Hv. destruct (multi_succ_inv _ _ Hmulti) as [u [Hu ->]].
    assert (Hvu : value u).
    { inversion Hv; subst. match goal with
      | Hn : numeric_value (tm_succ u) |- _ => inversion Hn; subst; constructor; assumption
      end. }
    pose proof (Hall u Hu Hvu) as Hrel. destruct Hrel as [_ Hnum].
    simpl. split.
    + apply v_nat. constructor. exact Hnum.
    + constructor. exact Hnum.
Qed.

Lemma strong_choice : forall T t1 t2,
  strong_expression_relation T t1 ->
  strong_expression_relation T t2 ->
  strong_expression_relation T (tm_choice t1 t2).
Proof.
  intros T t1 t2 [Hlc1 [Hsn1 Hrel1]] [Hlc2 [Hsn2 Hrel2]].
  split.
  - apply lc_choice; assumption.
  - split.
    + apply SN_intro. intros u Hu. inversion Hu; subst; [exact Hsn1|exact Hsn2].
    + intros v Hm Hv. inversion Hm; subst.
      * exfalso. inversion Hv; subst; try discriminate.
        match goal with Hn : numeric_value (tm_choice _ _) |- _ => inversion Hn end.
      * inversion H; subst; [eapply Hrel1|eapply Hrel2]; eauto using multi_refl.
Qed.

Lemma strong_if : forall T c t1 t2,
  strong_expression_relation Ty_Bool c ->
  strong_expression_relation T t1 ->
  strong_expression_relation T t2 ->
  strong_expression_relation T (tm_if c t1 t2).
Proof.
  intros T c t1 t2 Ec E1 E2. unfold strong_expression_relation in Ec.
  pose proof (proj1 Ec) as Hlc.
  pose proof (proj1 (proj2 Ec)) as Hsn.
  pose proof (proj2 (proj2 Ec)) as Hrel. revert Hlc Hrel.
  induction Hsn as [c Hnext IH]. intros Hlc Hrel.
  apply strong_expression_intro.
  - apply lc_if; [exact Hlc|exact (proj1 E1)|exact (proj1 E2)].
  - intros Hv. inversion Hv; subst; try congruence.
    match goal with Hn : numeric_value (tm_if _ _ _) |- _ => inversion Hn end.
  - intros u Hu. inversion Hu; subst.
    + exact E1.
    + exact E2.
    + pose proof (strong_expression_step Ty_Bool c t1' Ec H2) as Er.
      exact (IH t1' H2 Er (proj1 Er) (proj2 (proj2 Er))).
Qed.

Lemma not_value_app : forall t1 t2, ~ value (tm_app t1 t2).
Proof.
  intros t1 t2 Hv. inversion Hv; subst; try congruence.
  match goal with Hn : numeric_value (tm_app _ _) |- _ => inversion Hn end.
Qed.

Lemma strong_app : forall T1 T2 t1 t2,
  strong_expression_relation (Ty_Arrow T1 T2) t1 ->
  strong_expression_relation T1 t2 ->
  strong_expression_relation T2 (tm_app t1 t2).
Proof.
  intros T1 T2 t1 t2 E1. unfold strong_expression_relation in E1.
  pose proof (proj1 E1) as Hlc1.
  pose proof (proj1 (proj2 E1)) as Hsn1.
  pose proof (proj2 (proj2 E1)) as Hrel1.
  clear E1. revert t2.
  induction Hsn1 as [t1 Hnext1 IH1]. intros t2 E2.
  unfold strong_expression_relation in E2.
  pose proof (proj1 E2) as Hlc2.
  pose proof (proj1 (proj2 E2)) as Hsn2.
  pose proof (proj2 (proj2 E2)) as Hrel2.
  clear E2. revert Hlc2 Hrel2.
  induction Hsn2 as [t2 Hnext2 IH2]. intros Hlc2 Hrel2.
  apply strong_expression_intro.
  - apply lc_app; assumption.
  - intros Hv. exfalso. eapply not_value_app; exact Hv.
  - intros u Hu. inversion Hu; subst.
    + pose proof (Hrel1 (tm_abs T t) (multi_refl step (tm_abs T t)) (v_abs T t H1)) as Rfun.
      destruct Rfun as [_ [body [Heq Happ]]].
      injection Heq as HT Hb. subst.
      pose proof (Hrel2 t2 (multi_refl step t2) H3) as Rarg.
      destruct (Happ t2 Rarg) as [Hlc [Hsn Hresults]].
      split; [exact Hlc|]. split; [exact Hsn|exact Hresults].
    + pose proof (strong_expression_step (Ty_Arrow T1 T2) t1 t1' 
        (conj Hlc1 (conj (SN_intro t1 Hnext1) Hrel1)) H1) as Efun.
      exact (IH1 t1' H1 (proj1 Efun) (proj2 (proj2 Efun)) t2
        (conj Hlc2 (conj (SN_intro t2 Hnext2) Hrel2))).
    + pose proof (Hrel1 t1 (multi_refl step t1) H1) as Rfun.
      pose proof (strong_expression_step T1 t2 t2'
        (conj Hlc2 (conj (SN_intro t2 Hnext2) Hrel2)) H3) as Earg.
      exact (IH2 t2' H3 (proj1 Earg) (proj2 (proj2 Earg))).
Qed.

Lemma not_value_rec : forall n b s, ~ value (tm_natrec n b s).
Proof.
  intros n b s Hv. inversion Hv; subst; try congruence.
  match goal with Hn : numeric_value (tm_natrec _ _ _) |- _ => inversion Hn end.
Qed.

Lemma strong_rec_num : forall T n,
  numeric_value n ->
  forall b s,
    strong_expression_relation T b ->
    strong_expression_relation (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
    strong_expression_relation T (tm_natrec n b s).
Proof.
  intros T n Hnum. induction Hnum as [|n Hnum IH]; intros b s Eb Es.
  - unfold strong_expression_relation in Eb.
    pose proof (proj1 Eb) as HlcB. pose proof (proj1 (proj2 Eb)) as HsnB.
    pose proof (proj2 (proj2 Eb)) as HrelB. clear Eb. revert s Es.
    induction HsnB as [b HnextB IHB]. intros s Es.
    unfold strong_expression_relation in Es.
    pose proof (proj1 Es) as HlcS. pose proof (proj1 (proj2 Es)) as HsnS.
    pose proof (proj2 (proj2 Es)) as HrelS. clear Es. revert HlcS HrelS.
    induction HsnS as [s HnextS IHS]. intros HlcS HrelS.
    apply strong_expression_intro.
    + apply lc_rec; [apply lc_zero|exact HlcB|exact HlcS].
    + intros Hv. exfalso. eapply not_value_rec; exact Hv.
    + intros u Hu. inversion Hu; subst.
      * exfalso. eapply numeric_no_step; [constructor|eassumption].
      * match goal with
        | Hstep : b --> ?bp |- _ =>
          let E := fresh "Eb" in
          pose proof (strong_expression_step T b bp
            (conj HlcB (conj (SN_intro b HnextB) HrelB)) Hstep) as E;
          exact (IHB bp Hstep (proj1 E) (proj2 (proj2 E)) s
            (conj HlcS (conj (SN_intro s HnextS) HrelS)))
        end.
      * match goal with
        | Hstep : s --> ?sp |- _ =>
          let E := fresh "Es" in
          pose proof (strong_expression_step (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s sp
            (conj HlcS (conj (SN_intro s HnextS) HrelS)) Hstep) as E;
          exact (IHS sp Hstep (proj1 E) (proj2 (proj2 E)))
        end.
      * pose proof (HrelB u (multi_refl step u) H1) as Rb.
        exact (strong_value_is_expression T u Rb).
  - unfold strong_expression_relation in Eb.
    pose proof (proj1 Eb) as HlcB. pose proof (proj1 (proj2 Eb)) as HsnB.
    pose proof (proj2 (proj2 Eb)) as HrelB. clear Eb. revert s Es.
    induction HsnB as [b HnextB IHB]. intros s Es.
    unfold strong_expression_relation in Es.
    pose proof (proj1 Es) as HlcS. pose proof (proj1 (proj2 Es)) as HsnS.
    pose proof (proj2 (proj2 Es)) as HrelS. clear Es. revert HlcS HrelS.
    induction HsnS as [s HnextS IHS]. intros HlcS HrelS.
    apply strong_expression_intro.
    + apply lc_rec; [apply lc_succ; apply numeric_value_lc; exact Hnum|exact HlcB|exact HlcS].
    + intros Hv. exfalso. eapply not_value_rec; exact Hv.
    + intros u Hu. inversion Hu; subst.
      * exfalso. eapply numeric_no_step; [apply nv_succ; exact Hnum|eassumption].
      * match goal with
        | Hstep : b --> ?bp |- _ =>
          let E := fresh "Eb" in
          pose proof (strong_expression_step T b bp
            (conj HlcB (conj (SN_intro b HnextB) HrelB)) Hstep) as E;
          exact (IHB bp Hstep (proj1 E) (proj2 (proj2 E)) s
            (conj HlcS (conj (SN_intro s HnextS) HrelS)))
        end.
      * match goal with
        | Hstep : s --> ?sp |- _ =>
          let E := fresh "Es" in
          pose proof (strong_expression_step (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s sp
            (conj HlcS (conj (SN_intro s HnextS) HrelS)) Hstep) as E;
          exact (IHS sp Hstep (proj1 E) (proj2 (proj2 E)))
        end.
      * match goal with
        | HvS : value s |- _ =>
          pose proof (HrelS s (multi_refl step s) HvS) as Rs
        end.
        pose proof (strong_value_is_expression Ty_Nat n (conj (v_nat n Hnum) Hnum)) as En.
        pose proof (strong_app Ty_Nat (Ty_Arrow T T) s n
          (conj HlcS (conj (SN_intro s HnextS) HrelS)) En) as Efirst.
        pose proof (IH b s
          (conj HlcB (conj (SN_intro b HnextB) HrelB))
          (conj HlcS (conj (SN_intro s HnextS) HrelS))) as Erec.
        exact (strong_app T T (tm_app s n) (tm_natrec n b s) Efirst Erec).
Qed.

Lemma strong_rec : forall T n b s,
  strong_expression_relation Ty_Nat n ->
  strong_expression_relation T b ->
  strong_expression_relation (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  strong_expression_relation T (tm_natrec n b s).
Proof.
  intros T n b s En Eb Es. unfold strong_expression_relation in En.
  pose proof (proj1 En) as HlcN. pose proof (proj1 (proj2 En)) as HsnN.
  pose proof (proj2 (proj2 En)) as HrelN. clear En. revert b s Eb Es.
  induction HsnN as [n HnextN IHN]. intros b s Eb Es.
  apply strong_expression_intro.
  - apply lc_rec; [exact HlcN|exact (proj1 Eb)|exact (proj1 Es)].
  - intros Hv. exfalso. eapply not_value_rec; exact Hv.
  - intros u Hu. inversion Hu; subst.
    + match goal with
      | Hstep : n --> ?np |- _ =>
        let E := fresh "En" in
        pose proof (strong_expression_step Ty_Nat n np
          (conj HlcN (conj (SN_intro n HnextN) HrelN)) Hstep) as E;
        exact (IHN np Hstep (proj1 E) (proj2 (proj2 E)) b s Eb Es)
      end.
    + pose proof (strong_expression_step T b b' Eb H4) as Eb'.
      exact (strong_rec_num T n H2 b' s Eb' Es).
    + pose proof (strong_expression_step (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s s' Es H5) as Es'.
      exact (strong_rec_num T n H2 b s' Eb Es').
    + match goal with
      | Hv : value ?bv |- _ =>
        let Rb := fresh "Rb" in
        pose proof (proj2 (proj2 Eb) bv (multi_refl step bv) Hv) as Rb;
        exact (strong_value_is_expression T bv Rb)
      end.
    + pose proof (strong_value_is_expression Ty_Nat n0
        (conj (v_nat n0 H2) H2)) as Enp.
      pose proof (strong_rec_num T n0 H2 b s Eb Es) as Erec.
      pose proof (strong_app Ty_Nat (Ty_Arrow T T) s n0 Es Enp) as Efirst.
      exact (strong_app T T (tm_app s n0) (tm_natrec n0 b s) Efirst Erec).
Qed.


Theorem strong_fundamental : forall Gamma t T,
  <{ Gamma |-- t \in T }> ->
  forall rho,
    proper_substitution rho ->
    strong_related_substitution Gamma rho ->
    strong_expression_relation T (msubst rho t).
Proof.
  intros Gamma t T Hty. induction Hty; intros rho Hproper Hrel.
  - specialize (Hrel x T H). exact (strong_value_is_expression T (rho x) Hrel).
  - pose (x := fresh (L ++ free_vars t1)).
    assert (HfreshL : ~ In x L).
    { unfold x. intro Hin. apply fresh_notin with (L := L ++ free_vars t1).
      apply in_or_app. left. exact Hin. }
    assert (HfreshFV : ~ In x (free_vars t1)).
    { unfold x. intro Hin. apply fresh_notin with (L := L ++ free_vars t1).
      apply in_or_app. right. exact Hin. }
    assert (Hsv : strong_value_relation (Ty_Arrow T1 T2)
        (tm_abs T1 (msubst rho t1))).
    { simpl. split.
      - apply v_abs.
      change (locally_closed (msubst rho (tm_abs T1 t1))).
      eapply msubst_preserves_term; [exact Hproper|].
      unfold locally_closed. apply lc_abs.
      apply lc_at_open_inv with (u := tm_fvar x).
      pose proof (typing_regular _ _ _ (H x HfreshL)) as Hopenlc.
      exact Hopenlc.
      - exists (msubst rho t1). split; [reflexivity|].
      intros arg Harg.
      pose proof (H0 x HfreshL (subst_update rho x arg)
        (proper_update rho x arg Hproper (strong_value_relation_lc T1 arg Harg))
        (strong_related_update Gamma rho x T1 arg Hrel Harg)) as Ebody.
      assert (Eopen : msubst (subst_update rho x arg)
          (open t1 (tm_fvar x)) = open (msubst rho t1) arg).
      { apply msubst_open_update.
        - exact HfreshFV.
        - exact Hproper.
        - exact (strong_value_relation_lc T1 arg Harg). }
      rewrite Eopen in Ebody. unfold strong_expression_relation in Ebody.
      split.
      * exact (proj1 Ebody).
      * split.
        -- exact (proj1 (proj2 Ebody)).
        -- exact (proj2 (proj2 Ebody)).
    }
    apply strong_value_is_expression. exact Hsv.
  - eapply strong_app; eauto.
  - apply strong_value_is_expression. simpl. split; [constructor|left; reflexivity].
  - apply strong_value_is_expression. simpl. split; [constructor|right; reflexivity].
  - apply strong_value_is_expression. simpl. split; [apply v_nat; constructor|constructor].
  - change (strong_expression_relation Ty_Nat (tm_succ (msubst rho n))).
    exact (strong_succ (msubst rho n) (IHHty rho Hproper Hrel)).
  - change (strong_expression_relation T
      (tm_natrec (msubst rho n) (msubst rho b) (msubst rho s))).
    exact (strong_rec T (msubst rho n) (msubst rho b) (msubst rho s)
      (IHHty1 rho Hproper Hrel) (IHHty2 rho Hproper Hrel) (IHHty3 rho Hproper Hrel)).
  - eapply strong_if; eauto.
  - eapply strong_choice; eauto.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  pose proof (strong_fundamental empty t T Hty id_substitution
    id_substitution_proper strong_empty_related) as Hsem.
  rewrite msubst_id in Hsem.
  exact (proj1 (proj2 Hsem)).
Qed.

End STLCNormalizationIfNondeterminismRecursionEasyTask.
