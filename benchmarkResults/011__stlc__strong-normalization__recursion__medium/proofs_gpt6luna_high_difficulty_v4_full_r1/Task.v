(** STLC call-by-value strong-normalization benchmark, Easy variant.
    System T-style natural-number recursion; no if-then-else or choice. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Relations.Relation_Definitions Lia.
Import ListNotations.

Module STLCNormalizationRecursionEasyTask.

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

(* The reducibility predicate records termination at every type, and at
   function types also records termination after applying a computable
   argument. *)
Fixpoint reducible_core (T : ty) (t : tm) : Prop :=
  match T with
  | Ty_Arrow A B => forall u, locally_closed u ->
       strongly_normalizing u -> reducible_core A u ->
       strongly_normalizing (tm_app t u) /\ reducible_core B (tm_app t u)
  | _ => True
  end.

Definition reducible (T : ty) (t : tm) : Prop :=
  strongly_normalizing t /\ reducible_core T t.


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

Lemma step_preserves_lc : forall t t',
  locally_closed t -> t --> t' -> locally_closed t'.
Proof.
  intros t t' Hlc Hst. revert Hlc. induction Hst; intros Hlc.
  - apply open_preserves_term.
    + inversion H; assumption.
    + eapply value_regular; eassumption.
  - inversion Hlc; subst. apply lc_app.
    + eapply IHHst; eassumption.
    + assumption.
  - inversion Hlc; subst. apply lc_app.
    + assumption.
    + eapply IHHst; eassumption.
  - inversion Hlc; subst. apply lc_succ. eapply IHHst; eassumption.
  - inversion Hlc; subst. apply lc_rec.
    + eapply IHHst; eassumption.
    + assumption.
    + assumption.
  - inversion Hlc; subst. apply lc_rec.
    + assumption.
    + eapply IHHst; eassumption.
    + assumption.
  - inversion Hlc; subst. apply lc_rec.
    + assumption.
    + assumption.
    + eapply IHHst; eassumption.
  - eapply value_regular; eauto.
  - apply lc_app.
    + apply lc_app.
      * eapply value_regular; eassumption.
      * eapply numeric_value_lc; eassumption.
    + apply lc_rec.
      * eapply numeric_value_lc; eassumption.
      * eapply value_regular; eassumption.
      * eapply value_regular; eassumption.
Qed.

Lemma reducible_step : forall T t t',
  reducible T t -> t --> t' -> reducible T t'.
Proof.
  induction T; intros t t' Hr Hstep; simpl in *.
  - destruct Hr as [Hsn _].
    split; [inversion Hsn; subst; eauto|exact I].
  - destruct Hr as [Hsn _].
    split; [inversion Hsn; subst; eauto|exact I].
  - destruct Hr as [Hsn Happ].
    split.
    + inversion Hsn; subst; eauto.
    + intros u Hulc Husn Hucore.
      eapply IHT2.
      * eapply Happ; eassumption.
      * apply ST_App1; assumption.
Qed.

Definition neutral (t : tm) : Prop :=
  (forall t', ~ (t --> t')) /\ (forall v : tm, value t -> False).

Lemma neutral_app : forall t u,
  neutral t -> neutral (tm_app t u).
Proof.
  intros t u [Hstep Hnv]. split.
  - intros q Hq. inversion Hq; subst.
    + exfalso. apply (Hnv (tm_abs T t0)). constructor; eauto.
    + exfalso. eapply Hstep; eassumption.
    + exfalso. apply (Hnv t). assumption.
  - intros v Hv. inversion Hv; subst; try discriminate.
    inversion H.
Qed.

Lemma neutral_reducible : forall T t,
  neutral t -> reducible T t.
Proof.
  induction T; intros t Hneu; simpl.
  - split; [constructor; intros q Hq; exfalso; eapply (proj1 Hneu); eassumption|exact I].
  - split; [constructor; intros q Hq; exfalso; eapply (proj1 Hneu); eassumption|exact I].
  - split.
    + constructor; intros q Hq; exfalso; eapply (proj1 Hneu); eassumption.
    + intros u Hulc Husn Hucore. apply IHT2. apply neutral_app. exact Hneu.
Qed.

Lemma fvar_neutral : forall x, neutral (tm_fvar x).
Proof.
  intros x. split.
  - intros q Hq. inversion Hq.
  - intros v Hv. inversion Hv; subst; try discriminate. inversion H.
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
Qed.

Lemma numeric_no_step : forall n,
  numeric_value n -> forall t, ~ (n --> t).
Proof.
  intros n Hn. induction Hn; intros u Hs; inversion Hs; subst.
  eapply IHHn. eassumption.
Qed.

Lemma numeric_reducible : forall n,
  numeric_value n -> reducible Ty_Nat n.
Proof.
  intros n Hn. simpl. split.
  - constructor. intros q Hq. exfalso. eapply numeric_no_step; eauto.
  - exact I.
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
Qed.

Lemma open_rec_term : forall t j u,
  locally_closed t ->
  open_rec j u t = t.
Proof.
  unfold locally_closed. intros.
  eapply open_rec_lc_at; eauto. lia.
Qed.

Lemma msubst_open_rec : forall rho t k u,
  proper_substitution rho ->
  msubst rho (open_rec k u t) =
  open_rec k (msubst rho u) (msubst rho t).
Proof.
  intros rho t. induction t; intros k u Hp; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. apply open_rec_term. apply Hp.
  - rewrite IHt1, IHt2; auto.
  - rewrite IHt; auto.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHt; auto.
  - rewrite IHt1, IHt2, IHt3; auto.
Qed.

Lemma msubst_lc_at : forall t k rho,
  lc_at k t -> proper_substitution rho -> lc_at k (msubst rho t).
Proof.
  intros t k rho Hlc. revert rho.
  induction Hlc; intros rho Hp; simpl.
  - constructor. assumption.
  - apply term_lc_at. apply Hp.
  - constructor; eauto.
  - constructor; eauto.
  - constructor.
  - constructor.
  - constructor.
  - constructor; eauto.
  - constructor; eauto.
Qed.

Lemma notin_app_split : forall (x : atom) L1 L2,
  ~ In x (L1 ++ L2) ->
  ~ In x L1 /\ ~ In x L2.
Proof.
  intros x L1 L2 H.
  split; intro Hin; apply H; apply in_app_iff; auto.
Qed.

Lemma msubst_update_fresh : forall t rho x u,
  ~ In x (free_vars t) ->
  msubst (subst_update rho x u) t = msubst rho t.
Proof.
  induction t; intros rho x u Hfresh; simpl in *.
  - reflexivity.
  - unfold subst_update. destruct (Nat.eqb x a) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst. exfalso. apply Hfresh. simpl. auto.
    + reflexivity.
  - apply notin_app_split in Hfresh as [H1 H2]. rewrite IHt1, IHt2; auto.
  - rewrite IHt; auto.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHt; auto.
  - apply notin_app_split in Hfresh as [H1 H23].
    apply notin_app_split in H23 as [H2 H3].
    rewrite IHt1, IHt2, IHt3; auto.
Qed.

Lemma msubst_subst_open_rec : forall t rho k x u,
  proper_substitution rho ->
  ~ In x (free_vars t) ->
  msubst (subst_update rho x u) (open_rec k (tm_fvar x) t) =
  open_rec k u (msubst rho t).
Proof.
  induction t; intros rho k x u Hp Hfresh; simpl in *.
  - destruct (Nat.eqb k n) eqn:Heq; simpl.
    + unfold subst_update. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - assert (Hax : a <> x) by (intro E; subst; apply Hfresh; simpl; auto).
    unfold subst_update. destruct (Nat.eqb x a) eqn:Heq.
    + apply Nat.eqb_eq in Heq. exfalso. apply Hax. symmetry. exact Heq.
    + rewrite open_rec_term; auto.
  - apply notin_app_split in Hfresh as [H1 H2].
    rewrite IHt1, IHt2; auto.
  - rewrite IHt; auto.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHt; auto.
  - apply notin_app_split in Hfresh as [H1 H23].
    apply notin_app_split in H23 as [H2 H3].
    rewrite IHt1, IHt2, IHt3; auto.
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

Lemma id_substitution_proper :
  proper_substitution id_substitution.
Proof.
  unfold proper_substitution, id_substitution, locally_closed.
  intros. apply lc_fvar.
Qed.

Definition env_related (Gamma : context) (rho : term_substitution) : Prop :=
  proper_substitution rho /\
  forall x T, Gamma x = Some T -> reducible T (rho x).

Lemma reducible_multi : forall T t u,
  reducible T t -> multistep t u -> reducible T u.
Proof.
  intros T t u Hr Hm. induction Hm.
  - exact Hr.
  - apply IHHm. eapply reducible_step; eauto.
Qed.

Lemma typing_lc : forall Gamma t T,
  has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T Hty. induction Hty.
  - apply lc_fvar.
  - apply lc_abs. apply lc_at_open_inv with (u := tm_fvar (fresh L)).
    apply H0. apply fresh_notin.
  - apply lc_app; assumption.
  - apply lc_true.
  - apply lc_false.
  - apply lc_zero.
  - apply lc_succ; assumption.
  - apply lc_rec; assumption.
Qed.

Lemma multi_preserves_lc : forall t u,
  locally_closed t -> multistep t u -> locally_closed u.
Proof.
  intros t u Hlc Hm. induction Hm; auto.
  apply IHHm. eapply step_preserves_lc; eauto.
Qed.

Lemma env_related_update : forall Gamma rho x T u,
  env_related Gamma rho -> locally_closed u -> reducible T u ->
  env_related (update Gamma x T) (subst_update rho x u).
Proof.
  intros Gamma rho x T u [Hp Hrel] Hulc Hu. split.
  - eapply proper_update; eauto.
  - intros y U Hy. unfold update in Hy. unfold subst_update.
    destruct (Nat.eqb x y) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst y. inversion Hy; subst. exact Hu.
    + apply Hrel. exact Hy.
Qed.

Definition halts (t : tm) : Prop :=
  exists v, t -->* v /\ value v.

Lemma multi_trans : forall t u v,
  t -->* u ->
  u -->* v ->
  t -->* v.
Proof.
  intros t u v Htu Huv.
  induction Htu.
  - exact Huv.
  - eapply multi_step; eauto.
Qed.

Lemma multi_app1 : forall t1 t1' t2,
  t1 -->* t1' ->
  locally_closed t2 ->
  tm_app t1 t2 -->* tm_app t1' t2.
Proof.
  intros t1 t1' t2 Hs Ht2.
  induction Hs.
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_App1; eauto.
    + exact IHHs.
Qed.

Lemma multi_app2 : forall v1 t2 t2',
  value v1 ->
  t2 -->* t2' ->
  tm_app v1 t2 -->* tm_app v1 t2'.
Proof.
  intros v1 t2 t2' Hv Hs.
  induction Hs.
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_App2; eauto.
    + exact IHHs.
Qed.

Lemma multi_succ : forall t u,
  t -->* u -> tm_succ t -->* tm_succ u.
Proof.
  intros t u H. induction H.
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_Succ. exact H.
    + exact IHmulti.
Qed.

Lemma multi_rec_arg : forall n n' b s,
  n -->* n' -> locally_closed b -> locally_closed s ->
  tm_natrec n b s -->* tm_natrec n' b s.
Proof.
  intros n n' b s H Hb Hs. induction H.
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_RecArg; eassumption.
    + exact IHmulti.
Qed.

Lemma multi_rec_base : forall n b b' s,
  numeric_value n -> b -->* b' -> locally_closed s ->
  tm_natrec n b s -->* tm_natrec n b' s.
Proof.
  intros n b b' s Hn H Hs. induction H.
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_RecBase; eassumption.
    + exact IHmulti.
Qed.

Lemma multi_rec_step : forall n b s s',
  numeric_value n -> value b -> s -->* s' ->
  tm_natrec n b s -->* tm_natrec n b s'.
Proof.
  intros n b s s' Hn Hb H. induction H.
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_RecStep; eassumption.
    + exact IHmulti.
Qed.

Lemma reducible_expand : forall T t,
  (forall v : tm, value t -> False) ->
  (forall t', t --> t' -> reducible T t') ->
  reducible T t.
Proof.
  induction T; intros t Hnv Hred; simpl.
  - split.
    + constructor. intros t' Hstep. apply (proj1 (Hred t' Hstep)).
    + exact I.
  - split.
    + constructor. intros t' Hstep. apply (proj1 (Hred t' Hstep)).
    + exact I.
  - split.
    + constructor. intros t' Hstep. apply (proj1 (Hred t' Hstep)).
    + intros u Hulc Husn Hucore.
      apply IHT2.
      * intros v Hv. inversion Hv; subst; try discriminate. inversion H.
      * intros q Hq. inversion Hq; subst.
        -- exfalso. apply (Hnv tm_true). constructor; eauto.
        -- eapply (proj2 (Hred _ H1)); eauto.
        -- exfalso. apply (Hnv tm_true). eassumption.
Qed.

Lemma reducible_beta : forall A B body u,
  locally_closed (tm_abs A body) ->
  strongly_normalizing u ->
  (forall u', multistep u u' -> reducible B (open body u')) ->
  reducible B (tm_app (tm_abs A body) u).
Proof.
  intros A B body.
  fix IH 3. intros u Habs Hsn Hbody.
  destruct Hsn as [u Hsteps].
  apply reducible_expand.
  - intros v Hv. inversion Hv; subst; try discriminate. inversion H.
  - intros q Hq. inversion Hq; subst.
    + apply Hbody. apply multi_refl.
    + exfalso. eapply value_no_step.
      * constructor. exact Habs.
      * eassumption.
    + eapply IH.
      * exact Habs.
      * eapply Hsteps; eassumption.
      * intros u' Hmulti. apply Hbody.
        eapply multi_step; eassumption.
Qed.

Lemma sn_succ : forall t,
  strongly_normalizing t -> strongly_normalizing (tm_succ t).
Proof.
  fix IH 2. intros t Hsn.
  inversion Hsn as [t0 Hred]; subst.
  constructor. intros q Hq. inversion Hq; subst.
  apply IH. eapply Hred; eassumption.
Qed.

Lemma reducible_rec_numeric : forall n,
  numeric_value n -> forall b, strongly_normalizing b ->
  forall s, strongly_normalizing s -> forall T,
  locally_closed b -> locally_closed s ->
  reducible T b -> reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  reducible T (tm_natrec n b s).
Proof.
  intros n Hnum. induction Hnum as [|n Hnum IHnum].
  - intros b Hb s Hs. revert s Hs.
    induction Hb as [b Hbstep IHb]; intros s Hs.
    induction Hs as [s Hsstep IHs]; intros T Hblc Hslc Hrb Hrs.
    apply reducible_expand.
    + intros v Hv. inversion Hv; subst; try discriminate. inversion H.
    + intros q Hq. inversion Hq; subst.
      * exfalso. eapply (numeric_no_step tm_zero nv_zero); eassumption.
      * eapply IHb.
        -- exact H4.
        -- constructor. exact Hsstep.
        -- eapply step_preserves_lc; [exact Hblc|exact H4].
        -- exact Hslc.
        -- eapply reducible_step; eassumption.
        -- exact Hrs.
      * eapply IHs.
        -- exact H5.
        -- exact Hblc.
        -- eapply step_preserves_lc; [exact Hslc|exact H5].
        -- exact Hrb.
        -- eapply reducible_step; eassumption.
      * exact Hrb.
  - intros b Hb s Hs. revert s Hs.
    induction Hb as [b Hbstep IHb]; intros s Hs.
    induction Hs as [s Hsstep IHs]; intros T Hblc Hslc Hrb Hrs.
    apply reducible_expand.
    + intros v Hv. inversion Hv; subst; try discriminate. inversion H.
    + intros q Hq. inversion Hq; subst.
      * exfalso. eapply (numeric_no_step (tm_succ n) (nv_succ n Hnum)); eassumption.
      * eapply IHb.
        -- exact H4.
        -- constructor. exact Hsstep.
        -- eapply step_preserves_lc; [exact Hblc|exact H4].
        -- exact Hslc.
        -- eapply reducible_step; eassumption.
        -- exact Hrs.
      * eapply IHs.
        -- exact H5.
        -- exact Hblc.
        -- eapply step_preserves_lc; [exact Hslc|exact H5].
        -- exact Hrb.
        -- eapply reducible_step; eassumption.
      * pose proof (IHnum b (@SN_intro b Hbstep) s (@SN_intro s Hsstep)
          T Hblc Hslc Hrb Hrs) as Hrec.
        destruct Hrs as [Hss Hscore]. simpl in Hscore.
        destruct Hrb as [Hbs Hbcore].
        assert (Hnlc : locally_closed n) by (eapply numeric_value_lc; eassumption).
        destruct (numeric_reducible n Hnum) as [Hns Hncore].
        destruct (Hscore n Hnlc Hns Hncore) as [Hsapp Hsappcore].
        simpl in Hsappcore.
        destruct (Hsappcore (tm_natrec n b s)
          (lc_rec 0 n b s Hnlc Hblc Hslc) (proj1 Hrec) (proj2 Hrec))
          as [HoutSN HoutCore].
        split; assumption.
Qed.

Lemma numeric_value_dec : forall t,
  { numeric_value t } + { ~ numeric_value t }.
Proof.
  intro t. induction t.
  - right. intro H. inversion H.
  - right. intro H. inversion H.
  - right. intro H. inversion H.
  - right. intro H. inversion H.
  - right. intro H. inversion H.
  - right. intro H. inversion H.
  - left. constructor.
  - destruct IHt as [Hn|Hn].
    + left. constructor. exact Hn.
    + right. intro H. inversion H. contradiction.
  - right. intro H. inversion H.
Defined.

Lemma reducible_rec : forall n,
  strongly_normalizing n -> forall b, strongly_normalizing b ->
  forall s, strongly_normalizing s -> forall T,
  locally_closed n -> locally_closed b -> locally_closed s ->
  reducible Ty_Nat n -> reducible T b ->
  reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  reducible T (tm_natrec n b s).
Proof.
  intros n Hn. induction Hn as [n Hnstep IHn].
  intros b Hb s Hs T Hnlc Hblc Hslc Hrn Hrb Hrs.
  destruct (numeric_value_dec n) as [Hnum|Hnonnumeric].
  - eapply reducible_rec_numeric; eauto.
  - revert s Hs Hslc Hrs.
    induction Hb as [b Hbstep IHb]; intros s Hs Hslc Hrs.
    revert Hslc Hrs.
    induction Hs as [s Hsstep IHs]; intros Hslc Hrs.
    apply reducible_expand.
    + intros v Hv. inversion Hv; subst; try discriminate. inversion H.
    + intros q Hq. inversion Hq; subst.
      * eapply IHn.
        -- exact H2.
        -- constructor. exact Hbstep.
        -- constructor. exact Hsstep.
        -- eapply step_preserves_lc; [exact Hnlc|exact H2].
        -- exact Hblc.
        -- exact Hslc.
        -- eapply reducible_step; eassumption.
        -- exact Hrb.
        -- exact Hrs.
      * eapply IHb.
        -- exact H4.
        -- eapply step_preserves_lc; [exact Hblc|exact H4].
        -- eapply reducible_step; eassumption.
        -- constructor. exact Hsstep.
        -- exact Hslc.
        -- exact Hrs.
      * eapply IHs.
        -- exact H5.
        -- eapply step_preserves_lc; [exact Hslc|exact H5].
        -- eapply reducible_step; eassumption.
      * exfalso. apply Hnonnumeric. constructor.
      * exfalso. apply Hnonnumeric. constructor; eassumption.
Qed.

Lemma fundamental : forall Gamma t T,
  has_type Gamma t T ->
  forall rho, env_related Gamma rho -> reducible T (msubst rho t).
Proof.
  intros Gamma t T Hty. induction Hty; intros rho Henv; simpl.
  - destruct Henv as [_ Hrel]. eapply Hrel; eauto.
  - destruct Henv as [Hp Hrel].
    assert (Hbodylc : lc_at 1 t1).
    { apply lc_at_open_inv with (u := tm_fvar (fresh L)).
      eapply typing_lc. apply H. apply fresh_notin. }
    split.
    + constructor. intros q Hq. inversion Hq.
    + intros u Hulc Husn Hucore.
      assert (Hu : reducible T1 u) by (split; assumption).
      apply reducible_beta.
      * apply lc_abs. eapply msubst_lc_at; eauto.
      * exact Husn.
      * intros u' Hmulti.
        set (x := fresh (L ++ free_vars t1)).
        assert (HxL : ~ In x L).
        { unfold x. intro Hin. apply fresh_notin with (L := L ++ free_vars t1).
          apply in_or_app. left. exact Hin. }
        assert (HxF : ~ In x (free_vars t1)).
        { unfold x. intro Hin. apply fresh_notin with (L := L ++ free_vars t1).
          apply in_or_app. right. exact Hin. }
        assert (Hulc' : locally_closed u') by (eapply multi_preserves_lc; eauto).
        assert (Hu' : reducible T1 u') by (eapply reducible_multi; eauto).
        assert (Henv' : env_related (update Gamma x T1) (subst_update rho x u')).
        { eapply env_related_update; [exact (conj Hp Hrel)|exact Hulc'|exact Hu']. }
        specialize (H0 x HxL (subst_update rho x u') Henv').
        unfold open in H0.
        rewrite msubst_subst_open_rec in H0; auto.
  - pose proof (IHHty1 rho Henv) as Hfun.
    pose proof (IHHty2 rho Henv) as Harg.
    pose proof (typing_lc _ _ _ Hty2) as Hlc2.
    destruct Henv as [Hp _].
    assert (Harglc : locally_closed (msubst rho t2)).
    { unfold locally_closed in *. eapply msubst_lc_at; eauto. }
    simpl in Hfun. destruct Hfun as [_ Happly].
    destruct Harg as [HargSN HargCore].
    eapply Happly; eauto.
  - simpl. split; [constructor; intros q Hq; inversion Hq|exact I].
  - simpl. split; [constructor; intros q Hq; inversion Hq|exact I].
  - simpl. split; [constructor; intros q Hq; inversion Hq|exact I].
  - pose proof (IHHty rho Henv) as Hn. simpl in Hn. destruct Hn as [Hsn _].
    simpl. split; [apply sn_succ; exact Hsn|exact I].
  - pose proof (IHHty1 rho Henv) as Hn.
    pose proof (IHHty2 rho Henv) as Hb.
    pose proof (IHHty3 rho Henv) as Hs.
    destruct Henv as [Hp _].
    pose proof (typing_lc _ _ _ Hty1) as Hnlc0.
    pose proof (typing_lc _ _ _ Hty2) as Hblc0.
    pose proof (typing_lc _ _ _ Hty3) as Hslc0.
    assert (Hnlc : locally_closed (msubst rho n)).
    { unfold locally_closed in *. eapply msubst_lc_at; eauto. }
    assert (Hblc : locally_closed (msubst rho b)).
    { unfold locally_closed in *. eapply msubst_lc_at; eauto. }
    assert (Hslc : locally_closed (msubst rho s)).
    { unfold locally_closed in *. eapply msubst_lc_at; eauto. }
    pose proof Hn as Hrn. pose proof Hb as Hrb. pose proof Hs as Hrs.
    destruct Hn as [HnSN _]. destruct Hb as [HbSN _]. destruct Hs as [HsSN _].
    eapply reducible_rec; eauto.
Qed.

Lemma sn_abs_app : forall T body u,
  locally_closed (tm_abs T body) ->
  strongly_normalizing u ->
  (forall u', multistep u u' -> strongly_normalizing (open body u')) ->
  strongly_normalizing (tm_app (tm_abs T body) u).
Proof.
  intros T body.
  fix IH 3. intros u Habs Hsn Hbody.
  destruct Hsn as [u Hsteps].
  constructor. intros q Hq. inversion Hq; subst.
  - apply Hbody. apply multi_refl.
  - exfalso.
    eapply (value_no_step (tm_abs T body)).
    + constructor. exact Habs.
    + eassumption.
  - eapply (IH t2' Habs (Hsteps t2' H3)).
    intros u' Hmulti. apply Hbody.
    eapply multi_step; eassumption.
Qed.

Lemma msubst_id : forall t, msubst id_substitution t = t.
Proof.
  induction t; simpl; try rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3; reflexivity.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> -> strongly_normalizing t.
Proof.
  intros t T Hty.
  assert (E : env_related empty id_substitution).
  { split.
    - apply id_substitution_proper.
    - intros x U Hlookup. unfold empty in Hlookup. discriminate. }
  pose proof (fundamental empty t T Hty id_substitution E) as Hred.
  pose proof (proj1 Hred) as Hsn.
  rewrite msubst_id in Hsn. exact Hsn.
Qed.

End STLCNormalizationRecursionEasyTask.
