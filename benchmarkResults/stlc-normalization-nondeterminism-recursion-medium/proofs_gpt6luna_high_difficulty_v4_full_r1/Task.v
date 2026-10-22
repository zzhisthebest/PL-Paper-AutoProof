(** STLC CBV strong-normalization benchmark, Easy variant.
    Features: nondeterminism-recursion. *)

From Stdlib Require Import Arith.PeanoNat Arith.Wf_nat Lists.List Relations.Relation_Definitions Lia.
Import ListNotations.

Module STLCNormalizationNondeterminismRecursionEasyTask.

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

Fixpoint reducible (T : ty) (t : tm) : Prop :=
  locally_closed t /\ strongly_normalizing t /\
  match T with
  | Ty_Bool => True
  | Ty_Nat => True
  | Ty_Arrow A B => forall u, reducible A u -> reducible B (tm_app t u)
  end.

Lemma reducible_lc : forall T t, reducible T t -> locally_closed t.
Proof. destruct T; simpl; intros t H; tauto. Qed.

Lemma reducible_sn : forall T t, reducible T t -> strongly_normalizing t.
Proof. destruct T; simpl; intros t H; tauto. Qed.

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

Lemma numeric_value_dec : forall t, {numeric_value t} + {~ numeric_value t}.
Proof.
  induction t.
  - right; intro H; inversion H.
  - right; intro H; inversion H.
  - right; intro H; inversion H.
  - right; intro H; inversion H.
  - right; intro H; inversion H.
  - right; intro H; inversion H.
  - left; constructor.
  - destruct IHt as [Hn|Hn].
    + left; constructor; exact Hn.
    + right; intro H; inversion H; contradiction.
  - right; intro H; inversion H.
  - right; intro H; inversion H.
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

Lemma step_lc : forall t t', t --> t' -> locally_closed t -> locally_closed t'.
Proof.
  intros t t' H. induction H; intros Hlc; inversion Hlc; subst.
  - eapply open_preserves_term; [inversion H4; assumption|eapply value_regular; eassumption].
  - apply lc_app. + apply IHstep. assumption. + assumption.
  - apply lc_app. + assumption. + apply IHstep. assumption.
  - apply lc_succ. apply IHstep. assumption.
  - apply lc_rec; [apply IHstep; assumption|assumption|assumption].
  - apply lc_rec; [assumption|apply IHstep; assumption|assumption].
  - apply lc_rec; [assumption|assumption|apply IHstep; assumption].
  - assumption.
  - apply lc_app.
    + apply lc_app; [eapply value_regular; eassumption|eapply numeric_value_lc; eassumption].
    + apply lc_rec; [inversion H6; assumption|assumption|assumption].
  - assumption.
  - assumption.
Qed.

Lemma sn_step : forall t t',
  strongly_normalizing t -> t --> t' -> strongly_normalizing t'.
Proof.
  intros t t' Hsn Hs. inversion Hsn; eauto.
Qed.

Lemma reducible_step : forall T t t',
  reducible T t -> t --> t' -> reducible T t'.
Proof.
  induction T as [| |A IHA B IHB]; simpl; intros t t' Hred Hs.
  - destruct Hred as [Hlc [Hsn _]].
    split; [eapply step_lc; eassumption|].
    split; [eapply sn_step; eassumption|exact I].
  - destruct Hred as [Hlc [Hsn _]].
    split; [eapply step_lc; eassumption|].
    split; [eapply sn_step; eassumption|exact I].
  - destruct Hred as [Hlc [Hsn Happ]].
    split; [eapply step_lc; eassumption|].
    split; [eapply sn_step; eassumption|].
    intros u Hu.
    pose proof Hu as Hu0.
    pose proof (reducible_lc A u Hu) as Hulc.
    apply IHB with (t:=tm_app t u).
    + apply Happ; exact Hu0.
    + apply ST_App1; assumption.
Qed.

Lemma reducible_expand_nonvalue : forall T t,
  locally_closed t ->
  ~ value t ->
  (forall t', t --> t' -> reducible T t') ->
  reducible T t.
Proof.
  induction T as [| |A IHA B IHB]; simpl; intros t Hlc Hnv Hsteps.
  - split; [exact Hlc|]. split.
    + apply SN_intro. intros t' Hs. specialize (Hsteps t' Hs) as [_ [Hsn _]]. exact Hsn.
    + exact I.
  - split; [exact Hlc|]. split.
    + apply SN_intro. intros t' Hs. specialize (Hsteps t' Hs) as [_ [Hsn _]]. exact Hsn.
    + exact I.
  - split; [exact Hlc|]. split.
    + apply SN_intro. intros t' Hs. specialize (Hsteps t' Hs) as [_ [Hsn _]]. exact Hsn.
    + intros u Hu.
      apply IHB.
      * apply lc_app; [exact Hlc|apply reducible_lc with (T:=A); exact Hu].
      * intros Hv. inversion Hv; subst; try discriminate; inversion H.
      * intros z Hz. inversion Hz; subst.
        -- exfalso. apply Hnv. eapply v_abs; eassumption.
        -- specialize (Hsteps t1' H1) as [_ [_ Happ]]. apply Happ; exact Hu.
        -- exfalso. apply Hnv. eassumption.
Qed.

Lemma SN_induction : forall (P : tm -> Prop),
  (forall t, (forall t', t --> t' -> P t') -> P t) ->
  forall t, strongly_normalizing t -> P t.
Proof.
  intros P Hstep t Hsn. induction Hsn. apply Hstep. intros t' Ht. eauto.
Qed.

Lemma reducible_arrow_app : forall A B f u,
  reducible (Ty_Arrow A B) f -> reducible A u ->
  reducible B (tm_app f u).
Proof.
  intros A B f u Hf Hu. simpl in Hf. destruct Hf as [_ [_ Happ]]. apply Happ. exact Hu.
Qed.

Lemma red_numeric : forall n, numeric_value n -> reducible Ty_Nat n.
Proof.
  intros n Hn. unfold reducible. split; [apply numeric_value_lc; exact Hn|].
  split.
  - apply SN_intro. intros t Hs. exfalso. eapply numeric_no_step; eauto.
  - exact I.
Qed.

Lemma reducible_natrec_numeric : forall T n,
  numeric_value n -> forall b s,
  reducible T b ->
  reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  reducible T (tm_natrec n b s).
Proof.
  intros T n Hnum. induction Hnum as [|n Hnum IHnum]; intros b s Hb Hs.
  - refine (SN_induction
      (fun b0 => forall s0, reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s0 ->
        reducible T b0 -> reducible T (tm_natrec tm_zero b0 s0))
      _ b (reducible_sn T b Hb) s Hs Hb).
    intros b0 IHb s0 Hs0 Hb0.
    refine (SN_induction
      (fun s1 => reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s1 ->
        reducible T (tm_natrec tm_zero b0 s1))
      _ s0 (reducible_sn (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s0 Hs0) Hs0).
    intros s1 IHs Hs1.
    eapply reducible_expand_nonvalue.
    + apply lc_rec; [apply lc_zero|apply reducible_lc with (T:=T); exact Hb0|
        apply reducible_lc with (T:=Ty_Arrow Ty_Nat (Ty_Arrow T T)); exact Hs1].
    + intro Hval. inversion Hval; subst; try discriminate; inversion H.
    + intros z Hz. inversion Hz; subst.
      * exfalso. eapply (numeric_no_step tm_zero nv_zero n'); exact H2.
      * apply (IHb b' H4 s1 Hs1). eapply reducible_step; eassumption.
      * apply (IHs s' H5). eapply reducible_step; eassumption.
      * exact Hb0.
  - refine (SN_induction
      (fun b0 => forall s0, reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s0 ->
        reducible T b0 -> reducible T (tm_natrec (tm_succ n) b0 s0))
      _ b (reducible_sn T b Hb) s Hs Hb).
    intros b0 IHb s0 Hs0 Hb0.
    refine (SN_induction
      (fun s1 => reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s1 ->
        reducible T (tm_natrec (tm_succ n) b0 s1))
      _ s0 (reducible_sn (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s0 Hs0) Hs0).
    intros s1 IHs Hs1.
    eapply reducible_expand_nonvalue.
    + apply lc_rec; [apply lc_succ; apply numeric_value_lc; exact Hnum|
        apply reducible_lc with (T:=T); exact Hb0|
        apply reducible_lc with (T:=Ty_Arrow Ty_Nat (Ty_Arrow T T)); exact Hs1].
    + intro Hval. inversion Hval; subst; try discriminate; inversion H.
    + intros z Hz. inversion Hz; subst.
      * exfalso. eapply (numeric_no_step (tm_succ n) (nv_succ n Hnum) n'); exact H2.
      * apply (IHb b' H4 s1 Hs1). eapply reducible_step; eassumption.
      * apply (IHs s' H5). eapply reducible_step; eassumption.
      * apply reducible_arrow_app with (A:=T) (B:=T).
        -- exact (@reducible_arrow_app Ty_Nat (Ty_Arrow T T) s1 n
             Hs1 (red_numeric n Hnum)).
        -- apply IHnum; assumption.
Qed.

Lemma reducible_natrec : forall T n b s,
  reducible Ty_Nat n -> reducible T b ->
  reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  reducible T (tm_natrec n b s).
Proof.
  intros T n b s Hn Hb Hs.
  refine (SN_induction
    (fun n0 => reducible Ty_Nat n0 -> forall b0 s0,
      reducible T b0 -> reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s0 ->
      reducible T (tm_natrec n0 b0 s0))
    _ n (reducible_sn Ty_Nat n Hn) Hn b s Hb Hs).
  intros n0 IHn Hn0 b0 s0 Hb0 Hs0.
  destruct (numeric_value_dec n0) as [Hnum|Hnum].
  - eapply reducible_natrec_numeric; eassumption.
  - refine (SN_induction
      (fun b1 => reducible T b1 -> forall s1,
        reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s1 ->
        reducible T (tm_natrec n0 b1 s1))
      _ b0 (reducible_sn T b0 Hb0) Hb0 s0 Hs0).
    intros b1 IHb Hb1 s1 Hs1.
    refine (SN_induction
      (fun s2 => reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s2 ->
        reducible T (tm_natrec n0 b1 s2))
      _ s1 (reducible_sn (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s1 Hs1) Hs1).
    intros s2 IHs Hs2.
    eapply reducible_expand_nonvalue.
    + apply lc_rec; [apply reducible_lc with (T:=Ty_Nat); exact Hn0|
        apply reducible_lc with (T:=T); exact Hb1|
        apply reducible_lc with (T:=Ty_Arrow Ty_Nat (Ty_Arrow T T)); exact Hs2].
    + intro Hv. inversion Hv; subst; try discriminate; inversion H.
    + intros z Hz. inversion Hz; subst.
      * apply (IHn n' H2 (@reducible_step Ty_Nat n0 n' Hn0 H2) b1 s2 Hb1 Hs2).
      * apply (IHb b' H4 (@reducible_step T b1 b' Hb1 H4) s2 Hs2).
      * apply (IHs s' H5 (@reducible_step (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s2 s' Hs2 H5)).
      * exfalso. apply Hnum. constructor.
      * exfalso. apply Hnum. constructor. exact H2.
Qed.

Lemma reducible_beta : forall A B body,
  (forall u, reducible A u -> reducible B (open body u)) ->
  locally_closed (tm_abs A body) ->
  forall u, reducible A u -> reducible B (tm_app (tm_abs A body) u).
Proof.
  intros A B body Hbody Habs u Hu.
  refine (SN_induction
    (fun u0 => reducible A u0 -> reducible B (tm_app (tm_abs A body) u0))
    _ u (reducible_sn A u Hu) Hu).
  intros u0 IH Hu0.
  eapply reducible_expand_nonvalue.
  - apply lc_app; [exact Habs|apply reducible_lc with (T:=A); exact Hu0].
  - intro Hv. inversion Hv; subst; try discriminate; inversion H.
  - intros z Hz. inversion Hz; subst.
    + apply Hbody; exact Hu0.
    + exfalso. eapply value_no_step; [apply v_abs; exact Habs|eassumption].
    + apply (IH t2' H3 (@reducible_step A u0 t2' Hu0 H3)).
Qed.

Lemma msubst_lc_at : forall k t rho,
  lc_at k t -> proper_substitution rho -> lc_at k (msubst rho t).
Proof.
  intros k t rho Hlc. induction Hlc; intros Hrho; simpl.
  - constructor. assumption.
  - apply term_lc_at. unfold proper_substitution in Hrho. apply Hrho.
  - constructor; [apply IHHlc1|apply IHHlc2]; assumption.
  - constructor. apply IHHlc. assumption.
  - constructor.
  - constructor.
  - constructor.
  - constructor. apply IHHlc. assumption.
  - constructor; [apply IHHlc1|apply IHHlc2|apply IHHlc3]; assumption.
  - constructor; [apply IHHlc1|apply IHHlc2]; assumption.
Qed.

Lemma msubst_open_rec : forall rho k t u,
  proper_substitution rho ->
  msubst rho (open_rec k u t) = open_rec k (msubst rho u) (msubst rho t).
Proof.
  intros rho k t. revert k. induction t; intros k u Hrho; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - rewrite open_rec_term by (apply Hrho).
    reflexivity.
  - rewrite IHt1, IHt2; try assumption. reflexivity.
  - rewrite IHt; try assumption. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHt; try assumption. reflexivity.
  - rewrite IHt1, IHt2, IHt3; try assumption. reflexivity.
  - rewrite IHt1, IHt2; try assumption. reflexivity.
Qed.

Lemma msubst_open : forall rho t x,
  proper_substitution rho ->
  msubst rho (open t (tm_fvar x)) = open (msubst rho t) (rho x).
Proof.
  intros rho t x Hrho. unfold open. rewrite msubst_open_rec by assumption.
  reflexivity.
Qed.

Lemma msubst_update_fresh : forall t rho x u,
  ~ In x (free_vars t) ->
  msubst (subst_update rho x u) t = msubst rho t.
Proof.
  induction t; simpl; intros rho x u Hfresh; try reflexivity.
  - destruct (Nat.eqb x a) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst. exfalso. apply Hfresh. simpl; auto.
    + unfold subst_update. rewrite Heq. reflexivity.
  - f_equal; [apply IHt1|apply IHt2]; intro Hin; apply Hfresh; simpl; apply in_or_app; auto.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal; [apply IHt1|apply IHt2|apply IHt3]; intro Hin; apply Hfresh; simpl; repeat rewrite in_app_iff; auto.
  - f_equal; [apply IHt1|apply IHt2]; intro Hin; apply Hfresh; simpl; apply in_or_app; auto.
Qed.

Lemma msubst_open_update : forall rho t x u,
  proper_substitution rho ->
  locally_closed u ->
  ~ In x (free_vars t) ->
  msubst (subst_update rho x u) (open t (tm_fvar x)) =
  open (msubst rho t) u.
Proof.
  intros rho t x u Hrho Huloc Hfresh.
  rewrite msubst_open by (apply proper_update; assumption).
  rewrite msubst_update_fresh by exact Hfresh.
  unfold subst_update. rewrite Nat.eqb_refl. reflexivity.
Qed.

Definition env_reducible (Gamma : context) (rho : term_substitution) : Prop :=
  forall x T, Gamma x = Some T -> reducible T (rho x).

Lemma env_reducible_update : forall Gamma rho x T u,
  env_reducible Gamma rho -> reducible T u ->
  env_reducible (update Gamma x T) (subst_update rho x u).
Proof.
  unfold env_reducible. intros Gamma rho x T u Henv Hu y U Hlookup.
  unfold update in Hlookup. unfold subst_update.
  destruct (Nat.eqb x y) eqn:E; simpl in *.
  - inversion Hlookup; subst. exact Hu.
  - apply Henv with (x:=y) (T:=U). exact Hlookup.
Qed.

Lemma msubst_id : forall t, msubst id_substitution t = t.
Proof.
  induction t; simpl; try reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2, IHt3. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Fixpoint tm_size (t : tm) : nat :=
  match t with
  | tm_bvar _ | tm_fvar _ | tm_true | tm_false | tm_zero => 1
  | tm_app a b | tm_choice a b => S (tm_size a + tm_size b)
  | tm_abs _ a | tm_succ a => S (tm_size a)
  | tm_natrec n b s => S (tm_size n + tm_size b + tm_size s)
  end.

Lemma open_rec_size_fvar : forall t k x,
  tm_size (open_rec k (tm_fvar x) t) = tm_size t.
Proof.
  induction t; intros k x; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2, IHt3. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma typing_lc : forall t Gamma T,
  has_type Gamma t T -> locally_closed t.
Proof.
  assert (Hreg : forall n, forall t, tm_size t < n ->
    forall Gamma T, has_type Gamma t T -> locally_closed t).
  { induction n using lt_wf_ind.
    intros t Hsize Gamma T Hty. destruct t; simpl in Hsize; inversion Hty; subst.
    - unfold locally_closed. apply lc_fvar.
    - unfold locally_closed. apply lc_app.
      + eapply H with (m:=tm_size (tm_app t1 t2)); [exact Hsize|simpl; lia|eassumption].
      + eapply H with (m:=tm_size (tm_app t1 t2)); [exact Hsize|simpl; lia|eassumption].
    - unfold locally_closed. apply lc_abs.
      pose proof (fresh_notin L) as Hfresh.
      pose proof (H4 (fresh L) Hfresh) as Hbody.
      assert (Hlt : tm_size (open t0 (tm_fvar (fresh L))) < tm_size (tm_abs t t0)).
      { unfold open. rewrite open_rec_size_fvar. simpl. lia. }
      pose proof (H (tm_size (tm_abs t t0)) Hsize
        (open t0 (tm_fvar (fresh L))) Hlt (update Gamma (fresh L) t) T2 Hbody) as Hopened.
      unfold locally_closed in Hopened. eapply lc_at_open_inv; exact Hopened.
    - unfold locally_closed. apply lc_true.
    - unfold locally_closed. apply lc_false.
    - unfold locally_closed. apply lc_zero.
    - unfold locally_closed. apply lc_succ.
      eapply H with (m:=tm_size (tm_succ t)); [exact Hsize|simpl; lia|eassumption].
    - unfold locally_closed. apply lc_rec.
      + eapply H with (m:=tm_size (tm_natrec t1 t2 t3)); [exact Hsize|simpl; lia|eassumption].
      + eapply H with (m:=tm_size (tm_natrec t1 t2 t3)); [exact Hsize|simpl; lia|eassumption].
      + eapply H with (m:=tm_size (tm_natrec t1 t2 t3)); [exact Hsize|simpl; lia|eassumption].
    - unfold locally_closed. apply lc_choice.
      + eapply H with (m:=tm_size (tm_choice t1 t2)); [exact Hsize|simpl; lia|eassumption].
      + eapply H with (m:=tm_size (tm_choice t1 t2)); [exact Hsize|simpl; lia|eassumption].
  }
  intros t Gamma T Hty. eapply Hreg with (n:=S (tm_size t)); eauto; lia.
Qed.

Lemma sn_value : forall v, value v -> strongly_normalizing v.
Proof.
  intros v Hv. apply SN_intro. intros t Hs. exfalso. eapply value_no_step; eauto.
Qed.

Lemma red_true : reducible Ty_Bool tm_true.
Proof.
  unfold reducible. split; [apply lc_true|]. split; [apply sn_value; apply v_true|exact I].
Qed.

Lemma red_false : reducible Ty_Bool tm_false.
Proof.
  unfold reducible. split; [apply lc_false|]. split; [apply sn_value; apply v_false|exact I].
Qed.

Lemma red_numeral : forall n, reducible Ty_Nat (numeral n).
Proof. intros; apply red_numeric, numeral_numeric. Qed.

Lemma sn_choice : forall a b,
  strongly_normalizing a -> strongly_normalizing b ->
  strongly_normalizing (tm_choice a b).
Proof.
  intros a b Hsa Hsb. apply SN_intro. intros t Hs. inversion Hs; subst; assumption.
Qed.

Lemma red_choice_base : forall T a b,
  (T = Ty_Bool \/ T = Ty_Nat) -> reducible T a -> reducible T b ->
  reducible T (tm_choice a b).
Proof.
  intros T a b HT Hra Hrb.
  pose proof (reducible_lc T a Hra) as Hla.
  pose proof (reducible_lc T b Hrb) as Hlb.
  pose proof (reducible_sn T a Hra) as Hsa.
  pose proof (reducible_sn T b Hrb) as Hsb.
  destruct HT as [HT|HT]; subst T; simpl in *.
  - split; [constructor; assumption|]. split; [apply sn_choice; assumption|exact I].
  - split; [constructor; assumption|]. split; [apply sn_choice; assumption|exact I].
Qed.

Lemma red_choice : forall T a b,
  reducible T a -> reducible T b -> reducible T (tm_choice a b).
Proof.
  intros T a b Ha Hb.
  eapply reducible_expand_nonvalue.
  - apply lc_choice; [apply reducible_lc with (T:=T)|apply reducible_lc with (T:=T)]; assumption.
  - intro Hv. inversion Hv; subst; try discriminate; inversion H.
  - intros t Hs. inversion Hs; subst; assumption.
Qed.

Lemma red_succ : forall t,
  reducible Ty_Nat t -> reducible Ty_Nat (tm_succ t).
Proof.
  intros t Ht.
  refine (SN_induction (fun x => reducible Ty_Nat x -> reducible Ty_Nat (tm_succ x))
    _ t (reducible_sn Ty_Nat t Ht) Ht).
  intros x IH Hx. destruct (numeric_value_dec x) as [Hnum|Hnum].
  - apply red_numeric. constructor. exact Hnum.
  - eapply reducible_expand_nonvalue.
    + apply lc_succ. apply reducible_lc with (T:=Ty_Nat). exact Hx.
    + intro Hv. inversion Hv; subst; try discriminate.
      exfalso. apply Hnum. inversion H; assumption.
    + intros t' Hs. inversion Hs; subst.
      apply (IH t'0 H0). eapply reducible_step; eassumption.
Qed.


Lemma fundamental : forall t Gamma T,
  has_type Gamma t T ->
  forall rho, proper_substitution rho -> env_reducible Gamma rho ->
  reducible T (msubst rho t).
Proof.
  assert (Hfund : forall n, forall t, tm_size t < n ->
    forall Gamma T, has_type Gamma t T -> forall rho,
    proper_substitution rho -> env_reducible Gamma rho ->
    reducible T (msubst rho t)).
  { induction n using lt_wf_ind.
    intros t Hsize Gamma T Hty rho Hrho Henv.
    destruct t; simpl in Hsize; inversion Hty; subst.
    - simpl. apply Henv with (x:=a) (T:=T). exact H2.
    - eapply reducible_arrow_app.
      + eapply H with (m:=tm_size (tm_app t1 t2)); [exact Hsize|simpl; lia|exact H3|exact Hrho|exact Henv].
      + eapply H with (m:=tm_size (tm_app t1 t2)); [exact Hsize|simpl; lia|exact H5|exact Hrho|exact Henv].
    - simpl.
      change (locally_closed (tm_abs t (msubst rho t0)) /\
        strongly_normalizing (tm_abs t (msubst rho t0)) /\
        (forall u, reducible t u -> reducible T2 (tm_app (tm_abs t (msubst rho t0)) u))).
      assert (Hlcabs : locally_closed (tm_abs t t0)) by (eapply typing_lc; eassumption).
      assert (Hlcsub : locally_closed (tm_abs t (msubst rho t0))).
      { unfold locally_closed in Hlcabs. inversion Hlcabs; subst.
        apply lc_abs. eapply msubst_lc_at; eauto. }
      split; [exact Hlcsub|]. split.
      + apply sn_value. apply v_abs. exact Hlcsub.
      + intros u Hu.
        eapply reducible_beta.
        --
        intros u0 Hu0.
        set (x := fresh (L ++ free_vars t0)).
        assert (Hxall : ~ In x (L ++ free_vars t0)).
        { unfold x. apply fresh_notin. }
        apply notin_app_split in Hxall as [HxL Hxfv].
        pose proof (H4 x HxL) as Hopened_ty.
        assert (Hlt : tm_size (open t0 (tm_fvar x)) < tm_size (tm_abs t t0)).
        { unfold open. rewrite open_rec_size_fvar. simpl. lia. }
        set (rho' := subst_update rho x u0).
        assert (Hrho' : proper_substitution rho').
        { unfold rho'. apply proper_update; [exact Hrho|apply reducible_lc with (T:=t); exact Hu0]. }
        assert (Henv' : env_reducible (update Gamma x t) rho').
        { unfold rho'. eapply env_reducible_update; eauto. }
        pose proof (H (tm_size (tm_abs t t0)) Hsize
          (open t0 (tm_fvar x)) Hlt (update Gamma x t) T2 Hopened_ty rho' Hrho' Henv') as Hsem.
        change (reducible T2 (msubst rho' (open t0 (tm_fvar x)))) in Hsem.
        unfold rho' in Hsem.
        rewrite (msubst_open_update rho t0 x u0 Hrho
          (reducible_lc t u0 Hu0) Hxfv) in Hsem.
        exact Hsem.
        -- exact Hlcsub.
        -- exact Hu.
    - exact red_true.
    - exact red_false.
    - apply red_numeric. constructor.
    - apply red_succ.
      eapply H with (m:=tm_size (tm_succ t)); [exact Hsize|simpl; lia|eassumption|exact Hrho|exact Henv].
    - eapply reducible_natrec.
      + eapply H with (m:=tm_size (tm_natrec t1 t2 t3)); [exact Hsize|simpl; lia|eassumption|exact Hrho|exact Henv].
      + eapply H with (m:=tm_size (tm_natrec t1 t2 t3)); [exact Hsize|simpl; lia|eassumption|exact Hrho|exact Henv].
      + eapply H with (m:=tm_size (tm_natrec t1 t2 t3)); [exact Hsize|simpl; lia|eassumption|exact Hrho|exact Henv].
    - eapply red_choice.
      + eapply H with (m:=tm_size (tm_choice t1 t2)); [exact Hsize|simpl; lia|eassumption|exact Hrho|exact Henv].
      + eapply H with (m:=tm_size (tm_choice t1 t2)); [exact Hsize|simpl; lia|eassumption|exact Hrho|exact Henv].
  }
  intros t Gamma T Hty rho Hrho Henv.
  eapply Hfund with (n:=S (tm_size t)); eauto; lia.
Qed.


Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  pose proof (fundamental t empty T Hty id_substitution id_substitution_proper) as Hred.
  assert (Henv : env_reducible empty id_substitution).
  { unfold env_reducible. intros x U Hlookup. unfold empty in Hlookup. discriminate. }
  specialize (Hred Henv).
  rewrite msubst_id in Hred.
  eapply reducible_sn. exact Hred.
Qed.

End STLCNormalizationNondeterminismRecursionEasyTask.
