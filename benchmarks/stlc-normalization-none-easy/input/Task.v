(** STLC call-by-value strong-normalization benchmark, Easy variant.
    No if-then-else, non-determinism, or recursion is included. *)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Relations.Relation_Definitions.
From Stdlib Require Import Lia.

Import ListNotations.

Module STLCNormalizationNoneEasyTask.

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

Fixpoint free_vars (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_app t1 t2 => free_vars t1 ++ free_vars t2
  | tm_abs _ t1 => free_vars t1
  | tm_true => []
  | tm_false => []
  end.

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

(** Provided logical relation. *)

Fixpoint value_relation (T : ty) (v : tm) : Prop :=
  value v /\
  match T with
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
  end.

Definition proper_substitution (rho : term_substitution) : Prop :=
  forall x, locally_closed (rho x).

Definition related_substitution
    (Gamma : context) (rho : term_substitution) : Prop :=
  forall x T,
    Gamma x = Some T ->
    value_relation T (rho x).

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
  unfold locally_closed. intros.
  eapply lc_at_weaken; eauto. lia.
Qed.

Lemma value_regular : forall v,
  value v -> locally_closed v.
Proof.
  intros v Hv. inversion Hv; subst.
  - assumption.
  - unfold locally_closed. apply lc_true.
  - unfold locally_closed. apply lc_false.
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
Qed.

Lemma value_relation_value : forall T v,
  value_relation T v -> value v.
Proof.
  intros T v H. destruct T; simpl in H; tauto.
Qed.

Lemma value_relation_term : forall T v,
  value_relation T v -> locally_closed v.
Proof.
  intros T v H.
  apply value_regular.
  apply value_relation_value with (T := T).
  exact H.
Qed.

Lemma expression_relation_halts : forall T t,
  expression_relation T t ->
  exists v, t -->* v /\ value v.
Proof.
  intros T t [_ [v [Hs HV]]].
  exists v. split.
  - exact Hs.
  - apply value_relation_value with (T := T). exact HV.
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
  apply term_lc_at. apply Hproper.
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

Lemma related_update : forall Gamma rho x T v,
  related_substitution Gamma rho ->
  value_relation T v ->
  related_substitution (update Gamma x T) (subst_update rho x v).
Proof.
  unfold related_substitution, subst_update, update.
  intros Gamma rho x T v Hrel HV y U Hy.
  destruct (Nat.eqb x y) eqn:Heq.
  - apply Nat.eqb_eq in Heq. subst y.
    injection Hy as ->. exact HV.
  - apply Hrel. exact Hy.
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
  induction t; simpl; try rewrite IHt; try rewrite IHt1; try rewrite IHt2;
    reflexivity.
Qed.

Lemma id_substitution_proper :
  proper_substitution id_substitution.
Proof.
  unfold proper_substitution, id_substitution, locally_closed.
  intros. apply lc_fvar.
Qed.

Lemma empty_related :
  related_substitution empty id_substitution.
Proof.
  unfold related_substitution, empty.
  intros. discriminate H.
Qed.

(** Supplied fundamental theorem. *)

Theorem fundamental : forall Gamma t T,
  <{ Gamma |-- t \in T }> ->
  forall rho,
    proper_substitution rho ->
    related_substitution Gamma rho ->
    expression_relation T (msubst rho t).
Proof.
  intros Gamma t T Htyping.
  induction Htyping; intros rho Hproper Hrel.
  - split.
    + apply Hproper.
    + exists (rho x). split.
      * apply multi_refl.
      * apply Hrel with (x := x). exact H.
  - split.
    + change (locally_closed (msubst rho (tm_abs T1 t1))).
      apply msubst_preserves_term.
      * exact Hproper.
      * apply typing_regular with (Gamma := Gamma) (T := Ty_Arrow T1 T2).
        apply T_Abs with (L := L). exact H.
    + exists (tm_abs T1 (msubst rho t1)).
      split.
      * apply multi_refl.
      * simpl. repeat split.
        -- apply v_abs.
           change (locally_closed (msubst rho (tm_abs T1 t1))).
           apply msubst_preserves_term.
           ++ exact Hproper.
           ++ apply typing_regular with (Gamma := Gamma) (T := Ty_Arrow T1 T2).
              apply T_Abs with (L := L). exact H.
        -- exists (msubst rho t1). split.
           ++ reflexivity.
           ++ intros arg HVarg.
              pose (x := fresh (L ++ free_vars t1)).
              assert (HxL : ~ In x L).
              {
                intro Hin. unfold x in Hin.
                apply (fresh_notin (L ++ free_vars t1)).
                apply in_or_app. left. exact Hin.
              }
              assert (Hxfv : ~ In x (free_vars t1)).
              {
                intro Hin. unfold x in Hin.
                apply (fresh_notin (L ++ free_vars t1)).
                apply in_or_app. right. exact Hin.
              }
              specialize (H0 x HxL (subst_update rho x arg)).
              assert (Harg_term : locally_closed arg).
              {
                apply value_relation_term with (T := T1). exact HVarg.
              }
              specialize (H0 (proper_update rho x arg Hproper Harg_term)).
              specialize (H0 (related_update Gamma rho x T1 arg Hrel HVarg)).
              rewrite (msubst_open_update t1 rho x arg Hxfv Hproper Harg_term) in H0.
              exact H0.
  - destruct (IHHtyping1 rho Hproper Hrel) as [Ht1 [vf [Hs1 HVf]]].
    destruct (IHHtyping2 rho Hproper Hrel) as [Ht2 [va [Hs2 HVa]]].
    destruct HVf as [HVf_value [body [Heq Hbody]]].
    subst vf.
    assert (HVf_term : locally_closed (tm_abs T1 body)).
    {
      apply value_regular. exact HVf_value.
    }
    specialize (Hbody va HVa).
    destruct Hbody as [Hbody_term [vr [Hsbody HVr]]].
    split.
    + simpl. apply lc_app; assumption.
    + exists vr. split.
      * eapply multi_trans.
        -- apply multi_app1; eauto.
        -- eapply multi_trans.
           ++ apply multi_app2.
              ** apply v_abs. exact HVf_term.
              ** exact Hs2.
           ++ eapply multi_step.
              ** apply ST_AppAbs.
                 --- exact HVf_term.
                 --- apply value_relation_value with (T := T1). exact HVa.
              ** exact Hsbody.
      * exact HVr.
  - split.
    + unfold locally_closed. apply lc_true.
    + exists tm_true. split.
      * apply multi_refl.
      * simpl. split.
        -- apply v_true.
        -- left. reflexivity.
  - split.
    + unfold locally_closed. apply lc_false.
    + exists tm_false. split.
      * apply multi_refl.
      * simpl. split.
        -- apply v_false.
        -- right. reflexivity.
Qed.

(** Target theorem: strong normalization for the supplied CBV relation. *)

Inductive strongly_normalizing : tm -> Prop :=
  | SN_intro : forall t,
      (forall t', t --> t' -> strongly_normalizing t') ->
      strongly_normalizing t.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  (* Derive strong normalization from the supplied fundamental theorem. *)
Qed.

End STLCNormalizationNoneEasyTask.
