(** STLC CBV strong-normalization benchmark, Easy variant.
    Features: if-recursion. *)

From Stdlib Require Import Arith.PeanoNat Arith.Wf_nat Lists.List Relations.Relation_Definitions Lia.
Import ListNotations.

Module STLCNormalizationIfRecursionEasyTask.

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
  | Ty_Bool => strongly_normalizing t
  | Ty_Nat => strongly_normalizing t
  | Ty_Arrow A B =>
      strongly_normalizing t /\
      (forall v, value v -> reducible A v -> reducible B (tm_app t v))
  end.

Lemma reducible_step : forall T t t',
  reducible T t -> t --> t' -> reducible T t'.
Proof.
  induction T; intros t t' Hr Hs; simpl in *.
  - inversion Hr as [x Hnext]. subst. eauto.
  - inversion Hr as [x Hnext]. subst. eauto.
  - destruct Hr as [Hsn Hfun]. split.
    + inversion Hsn as [x Hnext]. subst. eauto.
    + intros v Hv Hrv.
      specialize (Hfun v Hv Hrv).
      eapply IHT2; [exact Hfun|].
      eapply ST_App1; eauto using value_regular.
Qed.

Lemma reducible_of_steps : forall T t,
  (forall t', t --> t' -> reducible T t') ->
  (forall v, value v -> ~ (t = v)) ->
  reducible T t.
Proof.
  induction T; intros t Hnext Hnot; simpl.
  - constructor. intros t' Hs. eapply Hnext; eauto.
  - constructor. intros t' Hs. eapply Hnext; eauto.
  - split.
    + constructor. intros t' Hs. eapply Hnext; eauto.
    + intros v Hv Hrv.
      apply IHT2.
      * intros u Hu. inversion Hu; subst.
        -- exfalso. apply (Hnot (tm_abs T t0)).
           ++ apply v_abs. exact H1.
           ++ reflexivity.
        -- specialize (Hnext _ H1). destruct Hnext as [_ Hfun'].
           eapply Hfun'; eauto.
        -- exfalso. match goal with
           | Hst : v --> ?z |- _ => exact (value_no_step v Hv z Hst)
           end.
      * intros w Hw Heq. subst w. inversion Hw; subst; inversion H.
Qed.

Lemma reducible_sn : forall T t, reducible T t -> strongly_normalizing t.
Proof.
  induction T; intros t Hr; simpl in Hr; tauto.
Qed.

Lemma reducible_app : forall A B f u,
  reducible (Ty_Arrow A B) f -> reducible A u ->
  reducible B (tm_app f u).
Proof.
  intros A B f u Hf Hu.
  destruct Hf as [Hfs Hfun].
  revert u Hu Hfun.
  induction Hfs as [f0 Hfnext IHf].
  intros u Hu Hfun.
  pose proof (reducible_sn _ _ Hu) as Hus.
  induction Hus as [u Hunext IHu].
  eapply reducible_of_steps.
  - intros t Hs. inversion Hs; subst.
    + eapply reducible_step.
      * eapply Hfun; eauto.
      * exact Hs.
    + pose proof (@reducible_step (Ty_Arrow A B) f0 t1'
        ltac:(simpl; split; [constructor; exact Hfnext|exact Hfun]) H1)
        as Hr'.
      destruct Hr' as [_ Hfun'].
      eapply IHf; eauto.
    + eapply IHu; eauto using reducible_step.
  - intros v Hv Heq. subst v. inversion Hv; subst; inversion H.
Qed.

Lemma msubst_open_rec : forall rho t k u,
  proper_substitution rho ->
  msubst rho (open_rec k u t) =
  open_rec k (msubst rho u) (msubst rho t).
Proof.
  intros rho t. induction t; intros k u Hp; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. apply open_rec_term. apply Hp.
  - rewrite IHt1 by exact Hp. rewrite IHt2 by exact Hp. reflexivity.
  - rewrite IHt by exact Hp. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHt by exact Hp. reflexivity.
  - rewrite IHt1 by exact Hp. rewrite IHt2 by exact Hp. rewrite IHt3 by exact Hp. reflexivity.
  - rewrite IHt1 by exact Hp. rewrite IHt2 by exact Hp. rewrite IHt3 by exact Hp. reflexivity.
Qed.

Lemma msubst_update_away : forall rho x v t,
  ~ In x (free_vars t) ->
  msubst (subst_update rho x v) t = msubst rho t.
Proof.
  intros rho x v t. induction t; simpl; intros Haway.
  - reflexivity.
  - unfold subst_update. destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply Haway. auto.
    + reflexivity.
  - apply notin_app_split in Haway as [H1 H2].
    rewrite IHt1 by exact H1. rewrite IHt2 by exact H2. reflexivity.
  - rewrite IHt by exact Haway. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHt by exact Haway. reflexivity.
  - apply notin_app_split in Haway as [H1 H2].
    apply notin_app_split in H2 as [H2a H2b].
    rewrite IHt1 by exact H1. rewrite IHt2 by exact H2a.
    rewrite IHt3 by exact H2b. reflexivity.
  - apply notin_app_split in Haway as [H1 H2].
    apply notin_app_split in H2 as [H2a H2b].
    rewrite IHt1 by exact H1. rewrite IHt2 by exact H2a.
    rewrite IHt3 by exact H2b. reflexivity.
Qed.

Lemma msubst_open_update : forall rho x v t,
  proper_substitution (subst_update rho x v) ->
  ~ In x (free_vars t) ->
  msubst (subst_update rho x v) (open t (tm_fvar x)) =
  open (msubst rho t) v.
Proof.
  intros rho x v t Hp Haway. unfold open.
  rewrite msubst_open_rec by exact Hp.
  simpl. rewrite msubst_update_away by exact Haway.
  unfold subst_update. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma lc_at_msubst : forall k t,
  lc_at k t -> forall rho, proper_substitution rho ->
  lc_at k (msubst rho t).
Proof.
  intros k t Hlc. induction Hlc; intros rho Hp; simpl.
  - apply lc_bvar. assumption.
  - unfold proper_substitution in Hp. specialize (Hp x).
    eapply term_lc_at. exact Hp.
  - apply lc_app; eauto.
  - apply lc_abs; eauto.
  - apply lc_true.
  - apply lc_false.
  - apply lc_zero.
  - apply lc_succ; eauto.
  - apply lc_rec; eauto.
  - apply lc_if; eauto.
Qed.

Fixpoint tm_size (t : tm) : nat :=
  match t with
  | tm_bvar _ | tm_fvar _ | tm_true | tm_false | tm_zero => 1
  | tm_app a b => S (tm_size a + tm_size b)
  | tm_abs _ a | tm_succ a => S (tm_size a)
  | tm_natrec n b s => S (tm_size n + tm_size b + tm_size s)
  | tm_if a b c => S (tm_size a + tm_size b + tm_size c)
  end.

Lemma tm_size_open_rec : forall t k u,
  tm_size u = 1 ->
  tm_size (open_rec k u t) = tm_size t.
Proof.
  induction t; intros k u Hu; simpl; try rewrite ?IHt by exact Hu;
    try rewrite ?IHt1 by exact Hu; try rewrite ?IHt2 by exact Hu;
    try rewrite ?IHt3 by exact Hu; try reflexivity.
  destruct (Nat.eqb k n); simpl; lia.
Qed.

Lemma typing_lc : forall Gamma t T,
  <{ Gamma |-- t \in T }> -> locally_closed t.
Proof.
  intros Gamma t T Hty.
  assert (Hgen : forall n, forall t, tm_size t = n -> forall Gamma T,
      <{ Gamma |-- t \in T }> -> locally_closed t).
  { apply (well_founded_induction_type lt_wf
    (fun n => forall t, tm_size t = n -> forall Gamma T,
      <{ Gamma |-- t \in T }> -> locally_closed t)).
  intros n IH t0 Hsize Gamma0 T0 Hty0.
  destruct Hty0; unfold locally_closed.
  - constructor.
  - apply lc_abs.
    assert (Hlt : tm_size (open t1 (tm_fvar (fresh L))) < n).
    { unfold open. rewrite tm_size_open_rec by reflexivity. simpl in Hsize. lia. }
    specialize (IH (tm_size (open t1 (tm_fvar (fresh L)))) Hlt
      (open t1 (tm_fvar (fresh L))) eq_refl
      (update Gamma0 (fresh L) T1) T2
      (H (fresh L) (fresh_notin L))).
    unfold locally_closed in IH.
    eapply lc_at_open_inv. exact IH.
  - apply lc_app.
    + eapply IH with (y := tm_size t1); [simpl in Hsize; lia|reflexivity|exact Hty0_1].
    + eapply IH with (y := tm_size t2); [simpl in Hsize; lia|reflexivity|exact Hty0_2].
  - constructor.
  - constructor.
  - constructor.
  - apply lc_succ. eapply IH with (y := tm_size n0).
    + simpl in Hsize; lia.
    + reflexivity.
    + exact Hty0.
  - apply lc_rec.
    + eapply IH with (y := tm_size n0); [simpl in Hsize; lia|reflexivity|exact Hty0_1].
    + eapply IH with (y := tm_size b); [simpl in Hsize; lia|reflexivity|exact Hty0_2].
    + eapply IH with (y := tm_size s); [simpl in Hsize; lia|reflexivity|exact Hty0_3].
  - apply lc_if.
    + eapply IH with (y := tm_size t1); [simpl in Hsize; lia|reflexivity|exact Hty0_1].
    + eapply IH with (y := tm_size t2); [simpl in Hsize; lia|reflexivity|exact Hty0_2].
    + eapply IH with (y := tm_size t3); [simpl in Hsize; lia|reflexivity|exact Hty0_3].
  }
  eapply Hgen; eauto.
Qed.

Lemma reducible_abs : forall A B b,
  lc_at 1 b ->
  (forall v, value v -> reducible A v -> reducible B (open b v)) ->
  reducible (Ty_Arrow A B) (tm_abs A b).
Proof.
  intros A B b Hlc Hbody. simpl. split.
  - constructor. intros t' Hs. inversion Hs.
  - intros v Hv Hrv.
    eapply reducible_of_steps.
    + intros t' Hs. inversion Hs; subst.
      * eapply Hbody; eauto.
      * match goal with Hred : tm_abs A b --> _ |- _ => inversion Hred end.
      * exfalso. match goal with
        | Hred : v --> ?z |- _ => exact (value_no_step v Hv z Hred)
        end.
    + intros w Hw Heq. subst w. inversion Hw; subst; inversion H.
Qed.

Definition related_env (Gamma : context) (rho : term_substitution) : Prop :=
  proper_substitution rho /\
  (forall x T, Gamma x = Some T -> reducible T (rho x)).

Lemma reducible_succ : forall t,
  reducible Ty_Nat t -> reducible Ty_Nat (tm_succ t).
Proof.
  intros t Ht. induction Ht as [t Hnext IH].
  simpl. constructor. intros u Hs.
  inversion Hs; subst. eapply IH. eassumption.
Qed.

Lemma reducible_if : forall c a b T,
  reducible Ty_Bool c -> reducible T a -> reducible T b ->
  reducible T (tm_if c a b).
Proof.
  intros c a b T Hc Ha Hb.
  change (strongly_normalizing c) in Hc.
  revert a b Ha Hb.
  induction Hc as [c Hnext IH]. intros a b Ha Hb.
  eapply reducible_of_steps.
  - intros u Hs. inversion Hs; subst.
    + exact Ha.
    + exact Hb.
    + eapply IH; eauto using reducible_step.
  - intros v Hv Heq. subst v. inversion Hv; subst; inversion H.
Qed.

Lemma reducible_rec_numeric : forall n,
  numeric_value n -> forall T b s,
  value b -> value s -> reducible T b ->
  reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  reducible T (tm_natrec n b s).
Proof.
  intros n Hnum. induction Hnum; intros T b s Hb Hs Hrb Hrs.
  - eapply reducible_of_steps.
    + intros u Hu. inversion Hu; subst.
      * exfalso. eapply (numeric_no_step tm_zero nv_zero); eassumption.
      * exfalso. exact (value_no_step b Hb b' H4).
      * exfalso. match goal with
        | Hred : s --> ?z |- _ => exact (value_no_step s Hs z Hred)
        end.
      * exact Hrb.
    + intros v Hv Heq. subst v. inversion Hv; subst; inversion H.
  - eapply reducible_of_steps.
    + intros u Hu. inversion Hu; subst.
      * exfalso. inversion H2; subst.
        eapply (numeric_no_step t Hnum); eassumption.
      * exfalso. exact (value_no_step b Hb b' H4).
      * exfalso. match goal with
        | Hred : s --> ?z |- _ => exact (value_no_step s Hs z Hred)
        end.
      * eapply reducible_app.
        -- eapply reducible_app.
           ++ exact Hrs.
           ++ simpl. constructor. intros z Hz. exfalso.
              exact (numeric_no_step t Hnum z Hz).
        -- eapply IHHnum; eauto.
    + intros v Hv Heq. subst v. inversion Hv; subst; inversion H.
Qed.

Lemma reducible_rec : forall n b s T,
  reducible Ty_Nat n -> reducible T b ->
  reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  reducible T (tm_natrec n b s).
Proof.
  intros n b s T Hn Hb Hs.
  pose proof (reducible_sn _ _ Hn) as Hnsn.
  revert b s Hb Hs.
  induction Hnsn as [n Hnnext IHn].
  intros b s Hb Hs.
  pose proof (reducible_sn _ _ Hb) as Hbsn.
  revert b Hbsn Hb s Hs.
  intros b Hbsn.
  induction Hbsn as [b Hbnext IHb].
  intros Hb s Hs.
  pose proof (reducible_sn _ _ Hs) as Hssn.
  revert s Hssn Hs.
  intros s Hssn.
  induction Hssn as [s Hsnext IHs].
  intros Hs.
  eapply reducible_of_steps.
  - intros u Hu. inversion Hu; subst.
    + eapply IHn.
      * exact H2.
      * simpl. apply Hnnext. exact H2.
      * exact Hb.
      * exact Hs.
    + eapply IHb.
      * exact H4.
      * eapply reducible_step; eauto.
      * exact Hs.
    + eapply IHs; eauto using reducible_step.
    + exact Hb.
    + eapply reducible_app.
      * eapply reducible_app.
        -- exact Hs.
        -- simpl. constructor. intros z Hz. exfalso.
           exact (numeric_no_step n0 H2 z Hz).
      * eapply reducible_rec_numeric; eauto.
  - intros v Hv Heq. subst v. inversion Hv; subst; inversion H.
Qed.

Lemma fundamental : forall n t,
  tm_size t = n -> forall Gamma T rho,
  <{ Gamma |-- t \in T }> -> related_env Gamma rho ->
  reducible T (msubst rho t).
Proof.
  apply (well_founded_induction_type lt_wf
    (fun n => forall t, tm_size t = n -> forall Gamma T rho,
      <{ Gamma |-- t \in T }> -> related_env Gamma rho ->
      reducible T (msubst rho t))).
  intros n IH t Hsize Gamma T rho Hty Henv.
  destruct Hty; destruct Henv as [Hproper Hrel]; simpl.
  - apply Hrel with (x := x). assumption.
  - apply reducible_abs.
    + pose proof (typing_lc _ _ _ (T_Abs L Gamma T1 T2 t1 H)) as Hlc.
      inversion Hlc; subst. eapply lc_at_msubst; eauto.
    + intros v Hv Hrv.
      set (x := fresh (L ++ free_vars t1)).
      assert (HxL : ~ In x L).
      { unfold x. intro Hin. apply (fresh_notin (L ++ free_vars t1)).
        apply in_or_app. left. exact Hin. }
      assert (HxF : ~ In x (free_vars t1)).
      { unfold x. intro Hin. apply (fresh_notin (L ++ free_vars t1)).
        apply in_or_app. right. exact Hin. }
      assert (Hext : related_env (update Gamma x T1)
          (subst_update rho x v)).
      { split.
        - apply proper_update.
          + exact Hproper.
          + eapply value_regular; eassumption.
        - intros y U Hy. unfold update in Hy.
          destruct (Nat.eqb x y) eqn:E.
          + apply Nat.eqb_eq in E. subst y. inversion Hy; subst.
            unfold subst_update. rewrite Nat.eqb_refl. exact Hrv.
          + unfold subst_update. rewrite E. apply Hrel. exact Hy. }
      specialize (IH (tm_size (open t1 (tm_fvar x)))
        (ltac:(unfold open; rewrite tm_size_open_rec by reflexivity;
          simpl in Hsize; lia))
        (open t1 (tm_fvar x)) eq_refl (update Gamma x T1) T2
        (subst_update rho x v) (H x HxL) Hext).
      rewrite <- (msubst_open_update rho x v t1).
      * exact IH.
      * apply proper_update.
        -- exact Hproper.
        -- eapply value_regular; eassumption.
      * exact HxF.
  - eapply reducible_app.
    + eapply IH with (y := tm_size t1); [simpl in Hsize; lia|reflexivity|exact Hty1|split; assumption].
    + eapply IH with (y := tm_size t2); [simpl in Hsize; lia|reflexivity|exact Hty2|split; assumption].
  - constructor. intros u Hs. inversion Hs.
  - constructor. intros u Hs. inversion Hs.
  - constructor. intros u Hs. inversion Hs.
  - eapply reducible_succ. eapply IH with (y := tm_size n0).
    + simpl in Hsize; lia.
    + reflexivity.
    + eassumption.
    + split; assumption.
  - eapply reducible_rec.
    + eapply IH with (y := tm_size n0); [simpl in Hsize; lia|reflexivity|eassumption|split; assumption].
    + eapply IH with (y := tm_size b); [simpl in Hsize; lia|reflexivity|eassumption|split; assumption].
    + eapply IH with (y := tm_size s); [simpl in Hsize; lia|reflexivity|eassumption|split; assumption].
  - eapply reducible_if.
    + eapply IH with (y := tm_size t1); [simpl in Hsize; lia|reflexivity|eassumption|split; assumption].
    + eapply IH with (y := tm_size t2); [simpl in Hsize; lia|reflexivity|eassumption|split; assumption].
    + eapply IH with (y := tm_size t3); [simpl in Hsize; lia|reflexivity|eassumption|split; assumption].
Qed.

Lemma msubst_id : forall t, msubst id_substitution t = t.
Proof.
  induction t; simpl; try rewrite ?IHt; try rewrite ?IHt1; try rewrite ?IHt2;
    try rewrite ?IHt3; reflexivity.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  assert (Henv : related_env empty id_substitution).
  { split.
    - exact id_substitution_proper.
    - intros x U Hx. unfold empty in Hx. discriminate. }
  pose proof (fundamental (tm_size t) t eq_refl empty T id_substitution
    Hty Henv) as Hr.
  pose proof (reducible_sn T (msubst id_substitution t) Hr) as Hsn.
  rewrite msubst_id in Hsn. exact Hsn.
Qed.

End STLCNormalizationIfRecursionEasyTask.
