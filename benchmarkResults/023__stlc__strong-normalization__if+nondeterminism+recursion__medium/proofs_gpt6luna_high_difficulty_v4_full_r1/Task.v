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

Lemma id_substitution_proper :
  proper_substitution id_substitution.
Proof.
  unfold proper_substitution, id_substitution, locally_closed.
  intros. apply lc_fvar.
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

Fixpoint reducible (T : ty) (t : tm) : Prop :=
  match T with
  | Ty_Bool => locally_closed t /\ strongly_normalizing t
  | Ty_Nat => locally_closed t /\ strongly_normalizing t
  | Ty_Arrow A B => locally_closed t /\ strongly_normalizing t /\
      (forall v, reducible A v -> reducible B (tm_app t v))
  end.

Lemma sn_step_inv : forall t,
  strongly_normalizing t -> forall t', t --> t' -> strongly_normalizing t'.
Proof. intros t H; inversion H; eauto. Qed.

Lemma reducible_sn : forall T t, reducible T t -> strongly_normalizing t.
Proof. destruct T; simpl; intuition. Qed.

Lemma reducible_lc : forall T t, reducible T t -> locally_closed t.
Proof. destruct T; simpl; intuition. Qed.

Lemma step_preserves_lc : forall t t',
  locally_closed t -> t --> t' -> locally_closed t'.
Proof.
  intros t t' Hlc Hs. unfold locally_closed in *. revert Hlc.
  induction Hs; intros Hlc; inversion Hlc; subst.
  - inversion H4; subst. eapply open_rec_preserves_lc_at.
    + assumption.
    + eapply value_regular; eassumption.
  - eapply lc_app; [eapply IHHs; eassumption | assumption].
  - eapply lc_app; [eapply value_regular; eassumption | eapply IHHs; eassumption].
  - eapply lc_succ; eapply IHHs; eassumption.
  - eapply lc_rec; [eapply IHHs; eassumption | assumption | assumption].
  - eapply lc_rec; [assumption | eapply IHHs; eassumption | assumption].
  - eapply lc_rec; [assumption | assumption | eapply IHHs; eassumption].
  - assumption.
  - eapply lc_app; [eapply lc_app; [assumption | eapply numeric_value_lc; eassumption]
                    | eapply lc_rec; [eapply numeric_value_lc; eassumption | assumption | assumption]].
  - assumption.
  - assumption.
  - eapply lc_if; [eapply IHHs; eassumption | assumption | assumption].
  - assumption.
  - assumption.
Qed.

Lemma reducible_step : forall T t t',
  t --> t' -> reducible T t -> reducible T t'.
Proof.
  induction T; simpl; intros t t' Hstep Hred.
  - destruct Hred as [Hlc Hsn]. split.
    + eapply step_preserves_lc; eauto.
    + eapply sn_step_inv; eauto.
  - destruct Hred as [Hlc Hsn]. split.
    + eapply step_preserves_lc; eauto.
    + eapply sn_step_inv; eauto.
  - destruct Hred as [Hlc [Hsn Happ]]. split.
    + eapply step_preserves_lc; eauto.
    + split.
      * eapply sn_step_inv; eauto.
      * intros v Hv. apply IHT2 with (t := tm_app t v).
        -- apply ST_App1; [assumption | apply reducible_lc with (T := T1); assumption].
        -- apply Happ; assumption.
Qed.

Lemma reducible_from_steps_nonvalue : forall T t,
  locally_closed t ->
  (forall t', t --> t' -> reducible T t') ->
  ~ value t -> reducible T t.
Proof.
  induction T as [| |A IHA B IHB]; simpl; intros t Hlc Hsteps Hnv.
  - split; [assumption|]. constructor. intros t' Hs.
    destruct (Hsteps t' Hs) as [_ Hsn]. exact Hsn.
  - split; [assumption|]. constructor. intros t' Hs.
    destruct (Hsteps t' Hs) as [_ Hsn]. exact Hsn.
  - split; [assumption|]. split.
    + constructor. intros t' Hs. destruct (Hsteps t' Hs) as [_ [Hsn _]]. exact Hsn.
    + intros v Hv.
      apply IHB.
      * apply lc_app; [assumption|apply reducible_lc with (T:=A); assumption].
      * intros q Hq. inversion Hq; subst.
        -- exfalso. apply Hnv. constructor. assumption.
        -- match goal with Hred : ?head --> ?next |- _ =>
             destruct (Hsteps next Hred) as [_ [_ Hfun]]; apply Hfun; assumption
           end.
        -- exfalso. apply Hnv. assumption.
      * intro Hval. inversion Hval; subst; inversion H.
Qed.

Lemma reducible_abs_app : forall A B body,
  locally_closed (tm_abs A body) ->
  (forall v, reducible A v -> reducible B (open body v)) ->
  forall v, reducible A v -> reducible B (tm_app (tm_abs A body) v).
Proof.
  intros A B body Habs Hbody v Hv.
  assert (Haux : forall v, strongly_normalizing v -> reducible A v ->
      reducible B (tm_app (tm_abs A body) v)).
  { intros v0 Hsn. induction Hsn as [v0 Hnext IH]. intros Hv0.
    apply reducible_from_steps_nonvalue.
    - apply lc_app; [exact Habs|apply reducible_lc with (T:=A); assumption].
    - intros q Hq. inversion Hq; subst.
      + apply Hbody. assumption.
      + exfalso. eapply (value_no_step (tm_abs A body)).
        * constructor. exact Habs.
        * exact H1.
      + match goal with Hred : v0 --> ?vp |- _ =>
          eapply IH; [exact Hred|eapply reducible_step; eassumption]
        end.
    - intro Hval. inversion Hval; subst; inversion H.
  }
  eapply Haux; [eapply reducible_sn; eassumption|assumption].
Qed.

Lemma reducible_succ : forall n,
  reducible Ty_Nat n -> reducible Ty_Nat (tm_succ n).
Proof.
  intros n [Hlc Hsn]. split.
  - apply lc_succ. exact Hlc.
  - induction Hsn as [n Hnext IH]. constructor. intros q Hq.
    inversion Hq; subst. apply IH with (t':=t'); [assumption|].
    eapply step_preserves_lc; eassumption.
Qed.

Lemma reducible_choice : forall T a b,
  reducible T a -> reducible T b -> reducible T (tm_choice a b).
Proof.
  intros T a b Ha Hb. apply reducible_from_steps_nonvalue.
  - apply lc_choice; [apply reducible_lc with (T:=T)|apply reducible_lc with (T:=T)]; assumption.
  - intros q Hq. inversion Hq; subst; assumption.
  - intro Hval. inversion Hval; subst; inversion H.
Qed.

Lemma reducible_if : forall T c a b,
  reducible Ty_Bool c -> reducible T a -> reducible T b ->
  reducible T (tm_if c a b).
Proof.
  intros T c a b Hc Ha Hb.
  assert (Haux : forall c, strongly_normalizing c -> reducible Ty_Bool c ->
      reducible T (tm_if c a b)).
  { intros c0 Hsn. induction Hsn as [c0 Hnext IH]. intros Hc0.
    apply reducible_from_steps_nonvalue.
    - apply lc_if; [apply reducible_lc with (T:=Ty_Bool)|
                    apply reducible_lc with (T:=T)|apply reducible_lc with (T:=T)]; assumption.
    - intros q Hq. inversion Hq; subst.
      + exact Ha.
      + exact Hb.
      + apply IH with (t':=t1'); [assumption|eapply reducible_step; eassumption].
    - intro Hval. inversion Hval; subst; inversion H.
  }
  eapply Haux; [eapply reducible_sn; eassumption|assumption].
Qed.

Lemma msubst_open_rec : forall rho, proper_substitution rho -> forall k t u,
  msubst rho (open_rec k u t) = open_rec k (msubst rho u) (msubst rho t).
Proof.
  intros rho Hproper k t. revert k. induction t; intros k u; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. apply open_rec_term. apply Hproper.
  - rewrite IHt1, IHt2; reflexivity.
  - rewrite IHt; reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHt; reflexivity.
  - rewrite IHt1, IHt2, IHt3; reflexivity.
  - rewrite IHt1, IHt2, IHt3; reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
Qed.

Lemma msubst_open : forall rho, proper_substitution rho -> forall t u,
  msubst rho (open t u) = open (msubst rho t) (msubst rho u).
Proof. intros; apply msubst_open_rec; assumption. Qed.

Lemma msubst_update_fresh : forall rho x v t,
  ~ In x (free_vars t) ->
  msubst (subst_update rho x v) t = msubst rho t.
Proof.
  intros rho x v t. induction t; simpl; intros Hfresh; try reflexivity.
  - destruct (Nat.eqb x a) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst. exfalso. apply Hfresh. simpl; auto.
    + unfold subst_update. rewrite Heq. reflexivity.
  - destruct (notin_app_split x (free_vars t1) (free_vars t2) Hfresh) as [H1 H2].
    rewrite IHt1 by exact H1. rewrite IHt2 by exact H2. reflexivity.
  - rewrite IHt by exact Hfresh. reflexivity.
  - rewrite IHt by exact Hfresh. reflexivity.
  - destruct (notin_app_split x (free_vars t1) (free_vars t2 ++ free_vars t3) Hfresh) as [H1 H23].
    destruct (notin_app_split x (free_vars t2) (free_vars t3) H23) as [H2 H3].
    rewrite IHt1 by exact H1. rewrite IHt2 by exact H2. rewrite IHt3 by exact H3. reflexivity.
  - destruct (notin_app_split x (free_vars t1) (free_vars t2 ++ free_vars t3) Hfresh) as [H1 H23].
    destruct (notin_app_split x (free_vars t2) (free_vars t3) H23) as [H2 H3].
    rewrite IHt1 by exact H1. rewrite IHt2 by exact H2. rewrite IHt3 by exact H3. reflexivity.
  - destruct (notin_app_split x (free_vars t1) (free_vars t2) Hfresh) as [H1 H2].
    rewrite IHt1 by exact H1. rewrite IHt2 by exact H2. reflexivity.
Qed.

Lemma typing_lc : forall Gamma t T,
  has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T Hty. induction Hty.
  - unfold locally_closed. constructor.
  - unfold locally_closed. apply lc_abs.
    specialize (H0 (fresh L) (fresh_notin L)).
    unfold locally_closed in H0. eapply lc_at_open_inv; eassumption.
  - unfold locally_closed. apply lc_app; assumption.
  - unfold locally_closed. constructor.
  - unfold locally_closed. constructor.
  - unfold locally_closed. constructor.
  - unfold locally_closed. apply lc_succ. exact IHHty.
  - unfold locally_closed. apply lc_rec; assumption.
  - unfold locally_closed. apply lc_if; assumption.
  - unfold locally_closed. apply lc_choice; assumption.
Qed.

Lemma msubst_preserves_lc : forall t rho,
  locally_closed t -> proper_substitution rho -> locally_closed (msubst rho t).
Proof.
  intros t rho Hlc. unfold locally_closed in *. induction Hlc; intros Hproper; simpl.
  - apply lc_bvar. lia.
  - apply term_lc_at. apply Hproper.
  - apply lc_app; eauto.
  - apply lc_abs. eauto.
  - constructor.
  - constructor.
  - constructor.
  - apply lc_succ. eauto.
  - apply lc_rec; eauto.
  - apply lc_if; eauto.
  - apply lc_choice; eauto.
Qed.

Definition substitution_satisfies (Gamma : context) (rho : term_substitution) : Prop :=
  forall x T, Gamma x = Some T -> reducible T (rho x).

Lemma reducible_apply : forall A B f v,
  reducible (Ty_Arrow A B) f -> reducible A v -> reducible B (tm_app f v).
Proof. intros A B f v [_ [_ Happ]] Hv. apply Happ. exact Hv. Qed.

Lemma red_numeric : forall n, numeric_value n -> reducible Ty_Nat n.
Proof.
  intros n Hn. split.
  - apply numeric_value_lc; assumption.
  - constructor. intros t Hs. exfalso. eapply numeric_no_step; eauto.
Qed.

Lemma reducible_rec_numeric : forall T n,
  numeric_value n -> forall b s,
  reducible T b -> reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  reducible T (tm_natrec n b s).
Proof.
  intros T n Hn. induction Hn as [|n Hn IHn]; intros b s Hb Hs.
  -
    assert (Haux : forall b, strongly_normalizing b -> reducible T b ->
        forall s, strongly_normalizing s -> reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
        reducible T (tm_natrec tm_zero b s)).
    { intros b0 Hbn. induction Hbn as [b0 Hbnext IHb]. intros Hb0 s0 Hsn.
      induction Hsn as [s0 Hsnext IHs]. intros Hs0.
      apply reducible_from_steps_nonvalue.
      - apply lc_rec; [constructor|apply reducible_lc with (T:=T); assumption|apply reducible_lc with (T:=Ty_Arrow Ty_Nat (Ty_Arrow T T)); assumption].
      - intros q Hq. inversion Hq; subst.
        + exfalso. eapply (numeric_no_step tm_zero nv_zero n'); exact H2.
        + eapply IHb; [eassumption|eapply reducible_step; eassumption|
                       eapply reducible_sn; eassumption|eassumption].
        + eapply IHs; [eassumption|eapply reducible_step; eassumption].
        + assumption.
      - intro Hval. inversion Hval; subst; inversion H.
    }
    eapply Haux; eauto using reducible_sn.
  -
    assert (Haux : forall b, strongly_normalizing b -> reducible T b ->
        forall s, strongly_normalizing s -> reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
        reducible T (tm_natrec (tm_succ n) b s)).
    { intros b0 Hbn. induction Hbn as [b0 Hbnext IHb]. intros Hb0 s0 Hsn.
      induction Hsn as [s0 Hsnext IHs]. intros Hs0.
      apply reducible_from_steps_nonvalue.
      - apply lc_rec; [apply lc_succ; apply numeric_value_lc; assumption|apply reducible_lc with (T:=T); assumption|apply reducible_lc with (T:=Ty_Arrow Ty_Nat (Ty_Arrow T T)); assumption].
      - intros q Hq. inversion Hq; subst.
        + exfalso. eapply (numeric_no_step (tm_succ n) (nv_succ n Hn)); eassumption.
        + eapply IHb; [eassumption|eapply reducible_step; eassumption|
                       eapply reducible_sn; eassumption|eassumption].
        + eapply IHs; [eassumption|eapply reducible_step; eassumption].
        + (* the successor case uses the induction hypothesis for the predecessor *)
          assert (Hpred : reducible T (tm_natrec n b0 s0)).
          { apply IHn; assumption. }
          eapply reducible_apply.
          * eapply reducible_apply; [exact Hs0|apply red_numeric; assumption].
          * exact Hpred.
      - intro Hval. inversion Hval; subst; inversion H.
    }
    eapply Haux; eauto using reducible_sn.
Qed.

Lemma reducible_rec : forall T n b s,
  reducible Ty_Nat n -> reducible T b ->
  reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  reducible T (tm_natrec n b s).
Proof.
  intros T. assert (Haux : forall n, strongly_normalizing n -> reducible Ty_Nat n ->
      forall b, strongly_normalizing b -> reducible T b ->
      forall s, strongly_normalizing s -> reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
      reducible T (tm_natrec n b s)).
  { intros n Hn. induction Hn as [n Hnnext IHn]. intros Hnr b Hb.
    induction Hb as [b Hbnext IHb]. intros Hbr s Hs.
    induction Hs as [s Hsnext IHs]. intros Hsr.
    apply reducible_from_steps_nonvalue.
    - apply lc_rec; [apply reducible_lc with (T:=Ty_Nat)|
                     apply reducible_lc with (T:=T)|
                     apply reducible_lc with (T:=Ty_Arrow Ty_Nat (Ty_Arrow T T))]; assumption.
    - intros q Hq. inversion Hq; subst.
      + eapply IHn; [eassumption|eapply reducible_step; eassumption|
                      eapply reducible_sn; eassumption|eassumption|
                      eapply reducible_sn; eassumption|eassumption].
      + eapply IHb; [eassumption|eapply reducible_step; eassumption|
                      eapply reducible_sn; eassumption|eassumption].
      + eapply IHs; [eassumption|eapply reducible_step; eassumption].
      + assumption.
      + assert (Hpred : reducible T (tm_natrec n0 b s)).
        { eapply reducible_rec_numeric; eassumption. }
        eapply reducible_apply.
        * eapply reducible_apply; [exact Hsr|eapply red_numeric; eassumption].
        * exact Hpred.
    - intro Hval. inversion Hval; subst; inversion H.
  }
  intros n b s Hnr Hbr Hsr.
  eapply Haux; [eapply reducible_sn; eassumption|exact Hnr|
                 eapply reducible_sn; eassumption|exact Hbr|
                 eapply reducible_sn; eassumption|exact Hsr].
Qed.

Theorem fundamental : forall Gamma t T,
  has_type Gamma t T -> forall rho,
  proper_substitution rho -> substitution_satisfies Gamma rho ->
  reducible T (msubst rho t).
Proof.
  intros Gamma t T Hty. induction Hty; intros rho Hproper Hsat; simpl.
  - unfold substitution_satisfies in Hsat. specialize (Hsat x T H). exact Hsat.
  - assert (Habs : locally_closed (tm_abs T1 t1)).
    { eapply typing_lc. econstructor; eauto. }
    split.
    + change (locally_closed (msubst rho (tm_abs T1 t1))).
      eapply msubst_preserves_lc with (t:=tm_abs T1 t1); eauto.
    + split.
    * constructor. intros q Hq. inversion Hq.
    * intros v Hv.
      set (x := fresh (L ++ free_vars t1)).
      assert (Hfresh : ~ In x (L ++ free_vars t1)).
      { unfold x. apply fresh_notin. }
      apply notin_app_split in Hfresh. destruct Hfresh as [HxL HxFV].
      assert (Hsat' : substitution_satisfies (update Gamma x T1)
                  (subst_update rho x v)).
      { intros y U Hy. unfold update in Hy. destruct (Nat.eqb x y) eqn:E.
        - apply Nat.eqb_eq in E. subst y. inversion Hy; subst U.
          unfold subst_update. rewrite Nat.eqb_refl. exact Hv.
        - unfold subst_update. rewrite E. apply Hsat with (x:=y) (T:=U). exact Hy.
      }
      assert (Hbodyall : forall w, reducible T1 w ->
          reducible T2 (open (msubst rho t1) w)).
      { intros w Hw.
        assert (Hsatw : substitution_satisfies (update Gamma x T1)
                    (subst_update rho x w)).
        { intros y U Hy. unfold update in Hy. destruct (Nat.eqb x y) eqn:E.
          - apply Nat.eqb_eq in E. subst y. inversion Hy; subst U.
            unfold subst_update. rewrite Nat.eqb_refl. exact Hw.
          - unfold subst_update. rewrite E. apply Hsat with (x:=y) (T:=U). exact Hy.
        }
        pose proof (H0 x HxL (subst_update rho x w)
          (proper_update rho x w Hproper (reducible_lc T1 w Hw)) Hsatw) as Hbw.
        rewrite (msubst_open (subst_update rho x w)
          (proper_update rho x w Hproper (reducible_lc T1 w Hw)) t1 (tm_fvar x)) in Hbw.
        rewrite (msubst_update_fresh rho x w t1 HxFV) in Hbw.
        assert (Hvar : msubst (subst_update rho x w) (tm_fvar x) = w).
        { simpl. unfold subst_update. rewrite Nat.eqb_refl. reflexivity. }
        rewrite Hvar in Hbw. exact Hbw.
      }
      eapply reducible_abs_app; [eapply msubst_preserves_lc with (t:=tm_abs T1 t1); eauto| |exact Hv].
      exact Hbodyall.
  - pose proof (IHHty1 rho Hproper Hsat) as Hfun.
    pose proof (IHHty2 rho Hproper Hsat) as Harg.
    destruct Hfun as [_ [_ Happ]]. apply Happ. exact Harg.
  - split; [unfold locally_closed; constructor|]. constructor. intros q Hq. inversion Hq.
  - split; [unfold locally_closed; constructor|]. constructor. intros q Hq. inversion Hq.
  - split; [unfold locally_closed; constructor|]. constructor. intros q Hq. inversion Hq.
  - apply reducible_succ. exact (IHHty rho Hproper Hsat).
  - eapply reducible_rec.
    + exact (IHHty1 rho Hproper Hsat).
    + exact (IHHty2 rho Hproper Hsat).
    + exact (IHHty3 rho Hproper Hsat).
  - eapply reducible_if.
    + exact (IHHty1 rho Hproper Hsat).
    + exact (IHHty2 rho Hproper Hsat).
    + exact (IHHty3 rho Hproper Hsat).
  - eapply reducible_choice.
    + exact (IHHty1 rho Hproper Hsat).
    + exact (IHHty2 rho Hproper Hsat).
Qed.

Lemma msubst_id : forall t, msubst id_substitution t = t.
Proof. induction t; simpl; try rewrite IHt; try rewrite IHt1; try rewrite IHt2; try rewrite IHt3; reflexivity. Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  assert (Hsat : substitution_satisfies empty id_substitution).
  { intros x U Hx. unfold empty in Hx. discriminate. }
  pose proof (fundamental empty t T Hty id_substitution id_substitution_proper Hsat) as Hred.
  rewrite msubst_id in Hred. eapply reducible_sn; eassumption.
Qed.

End STLCNormalizationIfNondeterminismRecursionEasyTask.
