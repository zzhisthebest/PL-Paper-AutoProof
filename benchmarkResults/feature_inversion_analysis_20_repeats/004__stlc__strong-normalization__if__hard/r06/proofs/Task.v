(** STLC call-by-value strong-normalization benchmark task. *)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Relations.Relation_Definitions.
From Stdlib Require Import Lia.

Module STLCCBVNormalizationTask.

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
Notation "'if' t1 'then' t2 'else' t3" :=
  (tm_if t1 t2 t3)
  (in custom stlc_tm at level 200,
   t1 custom stlc_tm,
   t2 custom stlc_tm,
   t3 custom stlc_tm at level 200,
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
  | tm_if t1 t2 t3 =>
      tm_if (open_rec k u t1) (open_rec k u t2) (open_rec k u t3)
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
  | lc_if : forall k t1 t2 t3,
      lc_at k t1 ->
      lc_at k t2 ->
      lc_at k t3 ->
      lc_at k (tm_if t1 t2 t3).

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
  | T_If : forall Gamma t1 t2 t3 T,
      <{ Gamma |-- $(t1) \in Bool }> ->
      <{ Gamma |-- $(t2) \in T }> ->
      <{ Gamma |-- $(t3) \in T }> ->
      <{ Gamma |-- $(tm_if t1 t2 t3) \in T }>
where "<{ Gamma '|--' t '\in' T }>" := (has_type Gamma t T)
  : stlc_scope.

(** Target theorem: strong normalization for the supplied CBV relation. *)

Inductive strongly_normalizing : tm -> Prop :=
  | SN_intro : forall t,
      (forall t', t --> t' -> strongly_normalizing t') ->
      strongly_normalizing t.

(** * Logical relation development *)

Definition extend (env : atom -> tm) (x : atom) (u : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then u else env y.

Fixpoint subst (env : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => env x
  | tm_app t1 t2 => tm_app (subst env t1) (subst env t2)
  | tm_abs T1 t1 => tm_abs T1 (subst env t1)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (subst env t1) (subst env t2) (subst env t3)
  end.

Fixpoint fvs (t : tm) : list atom :=
  match t with
  | tm_bvar _ => nil
  | tm_fvar x => x :: nil
  | tm_app t1 t2 => fvs t1 ++ fvs t2
  | tm_abs _ t1 => fvs t1
  | tm_true => nil
  | tm_false => nil
  | tm_if t1 t2 t3 => fvs t1 ++ fvs t2 ++ fvs t3
  end.

Lemma subst_identity : forall t, subst (fun x => tm_fvar x) t = t.
Proof.
  intros t. induction t as [i | x | t1 IH1 t2 IH2 | T1 t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
    simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH1. reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IH1, IH2, IH3. reflexivity.
Qed.

(* Fresh atoms from finitely many lists. *)

Fixpoint maxlist (l : list atom) : atom :=
  match l with
  | nil => 0
  | cons a l' => Nat.max a (maxlist l')
  end.

Lemma maxlist_ub : forall l x, In x l -> x <= maxlist l.
Proof.
  induction l as [| a l IH]; intros x H; simpl in *.
  - destruct H.
  - destruct H as [-> | H].
    + apply Nat.le_max_l.
    + apply Nat.le_trans with (maxlist l); [apply IH; auto | apply Nat.le_max_r].
Qed.

Lemma fresh_atom : forall l : list atom, exists x, ~ In x l.
Proof.
  intros l. exists (S (maxlist l)). intro H.
  pose proof (maxlist_ub l _ H). lia.
Qed.

Lemma fresh3 : forall l1 l2 l3 : list atom,
  exists x, ~ In x l1 /\ ~ In x l2 /\ ~ In x l3.
Proof.
  intros l1 l2 l3.
  destruct (fresh_atom (l1 ++ l2 ++ l3)) as [x Hx].
  exists x. repeat split; intros H.
  - apply Hx. apply in_app_iff. left. exact H.
  - apply Hx. apply in_app_iff. right. apply in_app_iff. left. exact H.
  - apply Hx. apply in_app_iff. right. apply in_app_iff. right. exact H.
Qed.

(* Local closure lemmas. *)

Lemma lc_at_mono : forall t k m, lc_at k t -> k <= m -> lc_at m t.
Proof.
  intros t k m H. revert m. induction H as
    [k i Hlt | k x | k a b Ha IHa Hb IHb | k T a Ha IHa | k | k | k a b c Ha IHa Hb IHb Hc IHc];
    intros m Hle.
  - constructor. lia.
  - constructor.
  - constructor; auto.
  - constructor. apply IHa. lia.
  - constructor.
  - constructor.
  - constructor; auto.
Qed.

Lemma lc_open_rec_id : forall t k, lc_at k t ->
  forall j u, k <= j -> open_rec j u t = t.
Proof.
  intros t k H. induction H as
    [k i Hlt | k x | k a b Ha IHa Hb IHb | k T a Ha IHa | k | k | k a b c Ha IHa Hb IHb Hc IHc];
    intros j u Hle; simpl.
  - assert (i <> j) by lia.
    destruct (Nat.eqb j i) eqn:E.
    + apply Nat.eqb_eq in E. exfalso. lia.
    + reflexivity.
  - reflexivity.
  - rewrite (IHa j u Hle). rewrite (IHb j u Hle). reflexivity.
  - rewrite (IHa (S j) u). reflexivity. lia.
  - reflexivity.
  - reflexivity.
  - rewrite (IHa j u Hle). rewrite (IHb j u Hle). rewrite (IHc j u Hle). reflexivity.
Qed.

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v H. destruct H.
  - simpl. exact H.
  - simpl. constructor.
  - simpl. constructor.
Qed.

Lemma value_no_step : forall v t', value v -> step v t' -> False.
Proof.
  intros v t' Hv Hs. destruct Hv; inversion Hs.
Qed.

Lemma SN_of_no_step : forall t, (forall t', ~ step t t') -> strongly_normalizing t.
Proof.
  intros t H. apply SN_intro. intros t' Hs. exfalso. apply (H t'). exact Hs.
Qed.

Lemma SN_abs : forall T t, strongly_normalizing (tm_abs T t).
Proof.
  intros. apply SN_of_no_step. intros t' Hs. inversion Hs.
Qed.

Lemma SN_step : forall t t', strongly_normalizing t -> step t t' -> strongly_normalizing t'.
Proof.
  intros t t' H. induction H as [t0 Hf]. intros Hs. apply Hf. exact Hs.
Qed.

Lemma multi_no_step : forall t t', multi step t t' -> (forall s, ~ step t s) -> t' = t.
Proof.
  intros t t' Hm. induction Hm as [x | x y z Hxy Hyz IH]; intros Hn.
  - reflexivity.
  - exfalso. apply (Hn y). exact Hxy.
Qed.

Lemma multi_step_decompose : forall t s, multi step t s ->
  t = s \/ (exists s1, step t s1 /\ multi step s1 s).
Proof.
  intros t s Hm. induction Hm as [x | x y z Hxy Hyz IH].
  - left. reflexivity.
  - right. exists y. split; assumption.
Qed.

(* The logical relation: a term is in R T when it is strongly normalizing
   and every value it reduces to satisfies the value condition for T. *)

Fixpoint R (T : ty) (t : tm) : Prop :=
  match T with
  | Ty_Bool =>
      strongly_normalizing t /\
      (forall t', multi step t t' -> value t' ->
         t' = tm_true \/ t' = tm_false)
  | Ty_Arrow T1 T2 =>
      strongly_normalizing t /\
      (forall t', multi step t t' -> value t' ->
         forall T1' body, t' = tm_abs T1' body ->
         T1' = T1 /\
         (forall u, value u -> R T1 u -> R T2 (open body u)))
  end.

Lemma R_sn : forall T t, R T t -> strongly_normalizing t.
Proof.
  intros T t H. destruct T; exact (proj1 H).
Qed.

Lemma R_step : forall T t t', R T t -> step t t' -> R T t'.
Proof.
  intros T t t' H Hs. destruct T as [| T1 T2].
  - destruct H as [HSN HVC]. split.
    + apply SN_step with (t := t); assumption.
    + intros s Hm Hv. apply HVC with (t' := s); auto.
      apply multi_step with (y := t'); assumption.
  - destruct H as [HSN HVC]. split.
    + apply SN_step with (t := t); assumption.
    + intros s Hm Hv T1' body Heq.
      apply (HVC s (multi_step step t t' s Hs Hm) Hv T1' body Heq).
Qed.

(* Substitution and opening. *)

Lemma not_in_app_inv : forall x (l1 l2 : list atom),
  ~ In x (l1 ++ l2) -> ~ In x l1 /\ ~ In x l2.
Proof.
  intros x l1 l2 H. split; intros Hin; apply H; apply in_app_iff; auto.
Qed.

Lemma subst_open_rec : forall (t : tm) (x : atom) (u : tm) (env : atom -> tm) (k : nat),
  ~ In x (fvs t) ->
  env x = tm_fvar x ->
  (forall y, locally_closed (env y)) ->
  subst (extend env x u) (open_rec k (tm_fvar x) t) = open_rec k u (subst env t).
Proof.
  intros t. induction t as [i | y | a IH1 b IH2 | T1 a IH1 | | | a IH1 b IH2 c IH3];
    intros x u env k Hfresh Henv Hlc; simpl.
  - destruct (Nat.eqb k i) eqn:E.
    + simpl. unfold extend. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - assert (Hxy : x <> y).
    { intro E. apply Hfresh. left. symmetry. exact E. }
    assert (Ey : (x =? y) = false) by (apply Nat.eqb_neq; exact Hxy).
    assert (Hid : open_rec k u (env y) = env y).
    { apply (lc_open_rec_id (env y) 0 (Hlc y) k u). lia. }
    unfold extend. rewrite Ey. rewrite Hid. reflexivity.
  - destruct (not_in_app_inv x (fvs a) (fvs b) Hfresh) as [Hfa Hfb].
    rewrite (IH1 x u env k Hfa Henv Hlc).
    rewrite (IH2 x u env k Hfb Henv Hlc).
    reflexivity.
  - rewrite (IH1 x u env (S k) Hfresh Henv Hlc).
    reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct (not_in_app_inv x (fvs a) (fvs b ++ fvs c) Hfresh) as [Hfa Hfbc].
    destruct (not_in_app_inv x (fvs b) (fvs c) Hfbc) as [Hfb Hfc].
    rewrite (IH1 x u env k Hfa Henv Hlc).
    rewrite (IH2 x u env k Hfb Henv Hlc).
    rewrite (IH3 x u env k Hfc Henv Hlc).
    reflexivity.
Qed.

Lemma subst_open : forall (t : tm) (x : atom) (u : tm) (env : atom -> tm),
  ~ In x (fvs t) ->
  env x = tm_fvar x ->
  (forall y, locally_closed (env y)) ->
  subst (extend env x u) (open t (tm_fvar x)) = open (subst env t) u.
Proof.
  intros. unfold open. apply subst_open_rec; auto.
Qed.

(* Inversion lemmas for the step relation. *)

Lemma step_app_inv : forall (t1 t2 s : tm),
  tm_app t1 t2 --> s ->
  (exists T body v, t1 = tm_abs T body /\ t2 = v /\
     locally_closed (tm_abs T body) /\ value v /\ s = open body v)
  \/ (exists t1', t1 --> t1' /\ locally_closed t2 /\ s = tm_app t1' t2)
  \/ (exists v1 t2', t1 = v1 /\ value v1 /\ t2 --> t2' /\ s = tm_app v1 t2').
Proof.
  intros t1 t2 s H. inversion H; subst.
  - left. eexists _, _, _. repeat split; eauto.
  - right; left. eexists. repeat split; eauto.
  - right; right. eexists _, _. repeat split; eauto.
Qed.

Lemma step_if_inv : forall (b x y s : tm),
  tm_if b x y --> s ->
  (b = tm_true /\ locally_closed x /\ locally_closed y /\ s = x)
  \/ (b = tm_false /\ locally_closed x /\ locally_closed y /\ s = y)
  \/ (exists b', b --> b' /\ locally_closed x /\ locally_closed y /\ s = tm_if b' x y).
Proof.
  intros b x y s H. inversion H; subst.
  - left. repeat split; eauto.
  - right; left. repeat split; eauto.
  - right; right. eexists. repeat split; eauto.
Qed.

(* Application of a related value to a related argument. *)

Lemma R_app_value : forall T1 T2 (v t2 : tm),
  value v -> R (Ty_Arrow T1 T2) v -> R T1 t2 -> R T2 (tm_app v t2).
Proof.
  intros T1 T2 v t2 Hv HRv HR2.
  assert (HSN2 : strongly_normalizing t2) by (apply (R_sn T1 t2 HR2)).
  revert T2 v Hv HRv HR2.
  induction HSN2 as [t2 Hstep2 IH].
  intros T2 v Hv HRv HR2.
  destruct T2 as [| C D].
  - (* T2 = Bool *)
    destruct HRv as [HSNv HVCv].
    split.
    + apply SN_intro. intros s Hs.
      destruct (step_app_inv v t2 s Hs) as
        [[T [body [vv [Heq1 [Heq2 [Hlc [Hval HeqS]]]]]]]
        |[[t1' [Hstep1 [Hlc2 HeqS]]]
         |[v1 [t2' [Heq1 [Hval [Hstep2' HeqS]]]]]]].
      * rewrite HeqS. rewrite Heq1 in HVCv. rewrite Heq2 in HR2.
        destruct (HVCv (tm_abs T body) (multi_refl step (tm_abs T body))
                    (v_abs T body Hlc) T body eq_refl) as [HT Hbody].
        apply (R_sn Ty_Bool). apply (Hbody vv Hval HR2).
      * exfalso. apply (value_no_step v t1'); [exact Hv | exact Hstep1].
      * rewrite HeqS. subst v1.
        apply (R_sn Ty_Bool).
        apply (IH t2' Hstep2' Ty_Bool v Hv (conj HSNv HVCv) (R_step T1 t2 t2' HR2 Hstep2')).
    + intros s Hm Hvl.
      destruct (multi_step_decompose (tm_app v t2) s Hm) as [Heq | [s1 [Hs1 Htail]]].
      * subst s. inversion Hvl.
      * destruct (step_app_inv v t2 s1 Hs1) as
          [[T [body [vv [Heq1 [Heq2 [Hlc [Hval HeqS]]]]]]]
          |[[t1' [Hstep1 [Hlc2 HeqS]]]
           |[v1 [t2' [Heq1 [Hval [Hstep2' HeqS]]]]]]].
        -- rewrite Heq1 in HVCv. rewrite Heq2 in HR2.
           destruct (HVCv (tm_abs T body) (multi_refl step (tm_abs T body))
                       (v_abs T body Hlc) T body eq_refl) as [HT Hbody].
           destruct (Hbody vv Hval HR2) as [HSN' HVC'].
           rewrite HeqS in Htail. apply (HVC' s Htail Hvl).
        -- exfalso. apply (value_no_step v t1'); [exact Hv | exact Hstep1].
        -- subst v1.
           destruct (IH t2' Hstep2' Ty_Bool v Hv (conj HSNv HVCv) (R_step T1 t2 t2' HR2 Hstep2'))
             as [HSN' HVC'].
           rewrite HeqS in Htail. apply (HVC' s Htail Hvl).
  - (* T2 = Arrow C D *)
    destruct HRv as [HSNv HVCv].
    split.
    + apply SN_intro. intros s Hs.
      destruct (step_app_inv v t2 s Hs) as
        [[T [body [vv [Heq1 [Heq2 [Hlc [Hval HeqS]]]]]]]
        |[[t1' [Hstep1 [Hlc2 HeqS]]]
         |[v1 [t2' [Heq1 [Hval [Hstep2' HeqS]]]]]]].
      * rewrite HeqS. rewrite Heq1 in HVCv. rewrite Heq2 in HR2.
        destruct (HVCv (tm_abs T body) (multi_refl step (tm_abs T body))
                    (v_abs T body Hlc) T body eq_refl) as [HT Hbody].
        apply (R_sn (Ty_Arrow C D)). apply (Hbody vv Hval HR2).
      * exfalso. apply (value_no_step v t1'); [exact Hv | exact Hstep1].
      * rewrite HeqS. subst v1.
        apply (R_sn (Ty_Arrow C D)).
        apply (IH t2' Hstep2' (Ty_Arrow C D) v Hv (conj HSNv HVCv) (R_step T1 t2 t2' HR2 Hstep2')).
    + intros s Hm Hvl T1' body' Heq'.
      destruct (multi_step_decompose (tm_app v t2) s Hm) as [Heq | [s1 [Hs1 Htail]]].
      * exfalso. rewrite <- Heq in Heq'. discriminate Heq'.
      * destruct (step_app_inv v t2 s1 Hs1) as
          [[T [body [vv [Heq1 [Heq2 [Hlc [Hval HeqS]]]]]]]
          |[[t1' [Hstep1 [Hlc2 HeqS]]]
           |[v1 [t2' [Heq1 [Hval [Hstep2' HeqS]]]]]]].
        -- rewrite Heq1 in HVCv. rewrite Heq2 in HR2.
           destruct (HVCv (tm_abs T body) (multi_refl step (tm_abs T body))
                       (v_abs T body Hlc) T body eq_refl) as [HT Hbody].
           destruct (Hbody vv Hval HR2) as [HSN' HVC'].
           rewrite HeqS in Htail. apply (HVC' s Htail Hvl T1' body' Heq').
        -- exfalso. apply (value_no_step v t1'); [exact Hv | exact Hstep1].
        -- subst v1.
           destruct (IH t2' Hstep2' (Ty_Arrow C D) v Hv (conj HSNv HVCv) (R_step T1 t2 t2' HR2 Hstep2'))
             as [HSN' HVC'].
           rewrite HeqS in Htail. apply (HVC' s Htail Hvl T1' body' Heq').
Qed.

(* Application of two related terms. *)

Lemma R_app : forall T1 T2 (t1 t2 : tm),
  R (Ty_Arrow T1 T2) t1 -> R T1 t2 -> R T2 (tm_app t1 t2).
Proof.
  intros T1 T2 t1 t2 HR1 HR2.
  assert (HSN1 : strongly_normalizing t1) by (apply (R_sn (Ty_Arrow T1 T2) t1 HR1)).
  revert T2 t2 HR1 HR2.
  induction HSN1 as [t1 Hstep1 IH].
  intros T2 t2 HR1 HR2.
  destruct T2 as [| C D].
  - (* T2 = Bool *)
    destruct HR1 as [HSN1' HVC1].
    split.
    + apply SN_intro. intros s Hs.
      destruct (step_app_inv t1 t2 s Hs) as
        [[T [body [vv [Heq1 [Heq2 [Hlc [Hval HeqS]]]]]]]
        |[[t1' [Hstep1' [Hlc2 HeqS]]]
         |[v1 [t2' [Heq1 [Hval [Hstep2' HeqS]]]]]]].
      * rewrite HeqS. rewrite Heq1 in HVC1. rewrite Heq2 in HR2.
        destruct (HVC1 (tm_abs T body) (multi_refl step (tm_abs T body))
                    (v_abs T body Hlc) T body eq_refl) as [HT Hbody].
        apply (R_sn Ty_Bool). apply (Hbody vv Hval HR2).
      * rewrite HeqS.
        apply (R_sn Ty_Bool).
        apply (IH t1' Hstep1' Ty_Bool t2 (R_step (Ty_Arrow T1 Ty_Bool) t1 t1' (conj HSN1' HVC1) Hstep1') HR2).
      * rewrite HeqS. subst v1.
        apply (R_sn Ty_Bool).
        apply (R_app_value T1 Ty_Bool t1 t2' Hval (conj HSN1' HVC1) (R_step T1 t2 t2' HR2 Hstep2')).
    + intros s Hm Hvl.
      destruct (multi_step_decompose (tm_app t1 t2) s Hm) as [Heq | [s1 [Hs1 Htail]]].
      * subst s. inversion Hvl.
      * destruct (step_app_inv t1 t2 s1 Hs1) as
          [[T [body [vv [Heq1 [Heq2 [Hlc [Hval HeqS]]]]]]]
          |[[t1' [Hstep1' [Hlc2 HeqS]]]
           |[v1 [t2' [Heq1 [Hval [Hstep2' HeqS]]]]]]].
        -- rewrite Heq1 in HVC1. rewrite Heq2 in HR2.
           destruct (HVC1 (tm_abs T body) (multi_refl step (tm_abs T body))
                       (v_abs T body Hlc) T body eq_refl) as [HT Hbody].
           destruct (Hbody vv Hval HR2) as [HSN' HVC'].
           rewrite HeqS in Htail. apply (HVC' s Htail Hvl).
        --            destruct (IH t1' Hstep1' Ty_Bool t2 (R_step (Ty_Arrow T1 Ty_Bool) t1 t1' (conj HSN1' HVC1) Hstep1') HR2)
             as [HSN' HVC'].
           rewrite HeqS in Htail. apply (HVC' s Htail Hvl).
        -- subst v1.
           destruct (R_app_value T1 Ty_Bool t1 t2' Hval (conj HSN1' HVC1) (R_step T1 t2 t2' HR2 Hstep2'))
             as [HSN' HVC'].
           rewrite HeqS in Htail. apply (HVC' s Htail Hvl).
  - (* T2 = Arrow C D *)
    destruct HR1 as [HSN1' HVC1].
    split.
    + apply SN_intro. intros s Hs.
      destruct (step_app_inv t1 t2 s Hs) as
        [[T [body [vv [Heq1 [Heq2 [Hlc [Hval HeqS]]]]]]]
        |[[t1' [Hstep1' [Hlc2 HeqS]]]
         |[v1 [t2' [Heq1 [Hval [Hstep2' HeqS]]]]]]].
      * rewrite HeqS. rewrite Heq1 in HVC1. rewrite Heq2 in HR2.
        destruct (HVC1 (tm_abs T body) (multi_refl step (tm_abs T body))
                    (v_abs T body Hlc) T body eq_refl) as [HT Hbody].
        apply (R_sn (Ty_Arrow C D)). apply (Hbody vv Hval HR2).
      * rewrite HeqS.
        apply (R_sn (Ty_Arrow C D)).
        apply (IH t1' Hstep1' (Ty_Arrow C D) t2
                 (R_step (Ty_Arrow T1 (Ty_Arrow C D)) t1 t1' (conj HSN1' HVC1) Hstep1') HR2).
      * rewrite HeqS. subst v1.
        apply (R_sn (Ty_Arrow C D)).
        apply (R_app_value T1 (Ty_Arrow C D) t1 t2' Hval (conj HSN1' HVC1)
                 (R_step T1 t2 t2' HR2 Hstep2')).
    + intros s Hm Hvl T1' body' Heq'.
      destruct (multi_step_decompose (tm_app t1 t2) s Hm) as [Heq | [s1 [Hs1 Htail]]].
      * exfalso. rewrite <- Heq in Heq'. discriminate Heq'.
      * destruct (step_app_inv t1 t2 s1 Hs1) as
          [[T [body [vv [Heq1 [Heq2 [Hlc [Hval HeqS]]]]]]]
          |[[t1' [Hstep1' [Hlc2 HeqS]]]
           |[v1 [t2' [Heq1 [Hval [Hstep2' HeqS]]]]]]].
        -- rewrite Heq1 in HVC1. rewrite Heq2 in HR2.
           destruct (HVC1 (tm_abs T body) (multi_refl step (tm_abs T body))
                       (v_abs T body Hlc) T body eq_refl) as [HT Hbody].
           destruct (Hbody vv Hval HR2) as [HSN' HVC'].
           rewrite HeqS in Htail. apply (HVC' s Htail Hvl T1' body' Heq').
        -- destruct (IH t1' Hstep1' (Ty_Arrow C D) t2
                      (R_step (Ty_Arrow T1 (Ty_Arrow C D)) t1 t1' (conj HSN1' HVC1) Hstep1') HR2)
             as [HSN' HVC'].
           rewrite HeqS in Htail. apply (HVC' s Htail Hvl T1' body' Heq').
        -- subst v1.
           destruct (R_app_value T1 (Ty_Arrow C D) t1 t2' Hval (conj HSN1' HVC1)
                       (R_step T1 t2 t2' HR2 Hstep2')) as [HSN' HVC'].
           rewrite HeqS in Htail. apply (HVC' s Htail Hvl T1' body' Heq').
Qed.

(* Conditional. *)

Lemma R_if : forall T (b x y : tm),
  R Ty_Bool b -> R T x -> R T y -> R T (tm_if b x y).
Proof.
  intros T b x y HRb HRx HRy.
  assert (HSNb : strongly_normalizing b) by (apply (R_sn Ty_Bool b HRb)).
  revert T x y HRx HRy HRb.
  induction HSNb as [b Hstepb IHb].
  intros T x y HRx HRy HRb.
  destruct T as [| A B].
  - (* T = Bool *)
    split.
    + apply SN_intro. intros s Hs.
      destruct (step_if_inv b x y s Hs) as
        [[Heqb [Hlcx [Hlcy Heqs]]]
        |[[Heqb [Hlcx [Hlcy Heqs]]]
         |[b' [Hstepb' [Hlcx [Hlcy Heqs]]]]]].
      * rewrite Heqs. apply (R_sn Ty_Bool x). exact HRx.
      * rewrite Heqs. apply (R_sn Ty_Bool y). exact HRy.
      * rewrite Heqs. apply (R_sn Ty_Bool).
        apply (IHb b' Hstepb' Ty_Bool x y HRx HRy (R_step Ty_Bool b b' HRb Hstepb')).
    + intros s Hm Hvl.
      destruct (multi_step_decompose (tm_if b x y) s Hm) as [Heq | [s1 [Hs1 Htail]]].
      * subst s. inversion Hvl.
      * destruct (step_if_inv b x y s1 Hs1) as
          [[Heqb [Hlcx [Hlcy Heqs]]]
          |[[Heqb [Hlcx [Hlcy Heqs]]]
           |[b' [Hstepb' [Hlcx [Hlcy Heqs]]]]]].
        -- rewrite Heqs in Htail. destruct HRx as [HSNx HVCx]. apply (HVCx s Htail Hvl).
        -- rewrite Heqs in Htail. destruct HRy as [HSNy HVCy]. apply (HVCy s Htail Hvl).
        -- rewrite Heqs in Htail.
           destruct (IHb b' Hstepb' Ty_Bool x y HRx HRy (R_step Ty_Bool b b' HRb Hstepb'))
             as [HSN' HVC'].
           apply (HVC' s Htail Hvl).
  - (* T = Arrow A B *)
    split.
    + apply SN_intro. intros s Hs.
      destruct (step_if_inv b x y s Hs) as
        [[Heqb [Hlcx [Hlcy Heqs]]]
        |[[Heqb [Hlcx [Hlcy Heqs]]]
         |[b' [Hstepb' [Hlcx [Hlcy Heqs]]]]]].
      * rewrite Heqs. apply (R_sn (Ty_Arrow A B) x). exact HRx.
      * rewrite Heqs. apply (R_sn (Ty_Arrow A B) y). exact HRy.
      * rewrite Heqs. apply (R_sn (Ty_Arrow A B)).
        apply (IHb b' Hstepb' (Ty_Arrow A B) x y HRx HRy (R_step Ty_Bool b b' HRb Hstepb')).
    + intros s Hm Hvl T1' body' Heq'.
      destruct (multi_step_decompose (tm_if b x y) s Hm) as [Heq | [s1 [Hs1 Htail]]].
      * exfalso. rewrite <- Heq in Heq'. discriminate Heq'.
      * destruct (step_if_inv b x y s1 Hs1) as
          [[Heqb [Hlcx [Hlcy Heqs]]]
          |[[Heqb [Hlcx [Hlcy Heqs]]]
           |[b' [Hstepb' [Hlcx [Hlcy Heqs]]]]]].
        -- rewrite Heqs in Htail. destruct HRx as [HSNx HVCx].
           apply (HVCx s Htail Hvl T1' body' Heq').
        -- rewrite Heqs in Htail. destruct HRy as [HSNy HVCy].
           apply (HVCy s Htail Hvl T1' body' Heq').
        -- rewrite Heqs in Htail.
           destruct (IHb b' Hstepb' (Ty_Arrow A B) x y HRx HRy (R_step Ty_Bool b b' HRb Hstepb'))
             as [HSN' HVC'].
           apply (HVC' s Htail Hvl T1' body' Heq').
Qed.

(* Environments for the semantic typing judgement. *)

Definition env_ok (Gamma : context) (env : atom -> tm) (S : list atom) : Prop :=
  (forall y, locally_closed (env y)) /\
  (forall y U, Gamma y = Some U -> R U (env y)) /\
  (forall y, ~ In y S -> env y = tm_fvar y).

Lemma fundamental : forall Gamma t T,
  has_type Gamma t T ->
  forall env S, env_ok Gamma env S -> R T (subst env t).
Proof.
  intros Gamma t T H.
  induction H as
    [Gamma x T0 Hvar
    | L Gamma T1 T2 t1 Hbody IHbody
    | Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
    | Gamma
    | Gamma
    | Gamma t1 t2 t3 T H1 IH1 H2 IH2 H3 IH3];
    intros env S Hok.
  - (* T_Var *) simpl. destruct Hok as [Hlc [HRv Hid]]. apply (HRv x T0 Hvar).
  - (* T_Abs *)
    simpl. split.
    + apply SN_abs.
    + intros t' Hm Hval T1' body' Heq.
      assert (Ht' : t' = tm_abs T1 (subst env t1)).
      { apply (multi_no_step (tm_abs T1 (subst env t1)) t').
        - exact Hm.
        - intros s Hs. inversion Hs. }
      rewrite Ht' in Heq.
      subst t'.
      injection Heq as HT HB. subst T1'. subst body'.
      split.
      * reflexivity.
      * intros u Hvalu HRu.
        destruct (fresh3 L (fvs t1) S) as [x [HxL [Hxfvs HxS]]].
        destruct Hok as [Hlc [HRv Hid]].
        assert (Hok' : env_ok (update Gamma x T1) (extend env x u) (x :: S)).
        { unfold env_ok. repeat split.
          - intros y. unfold extend. destruct (Nat.eqb x y) eqn:E.
            + apply Nat.eqb_eq in E. subst y.
              apply value_lc. exact Hvalu.
            + apply Hlc.
          - intros y U Hy. unfold extend. destruct (Nat.eqb x y) eqn:E.
            + apply Nat.eqb_eq in E. subst y.
              unfold update in Hy. rewrite Nat.eqb_refl in Hy.
              injection Hy as HU. subst U. exact HRu.
            + unfold update in Hy. rewrite E in Hy.
              apply HRv. exact Hy.
          - intros y Hy. unfold extend. destruct (Nat.eqb x y) eqn:E.
            + apply Nat.eqb_eq in E. subst y. exfalso. apply Hy. left. reflexivity.
            + apply Hid.
              intro HyS. apply Hy. right. exact HyS. }
        specialize (IHbody x HxL (extend env x u) (x :: S) Hok').
        assert (Heqsub : subst (extend env x u) (open t1 (tm_fvar x))
                        = open (subst env t1) u).
        { apply subst_open.
          - exact Hxfvs.
          - apply Hid. exact HxS.
          - exact Hlc. }
        rewrite <- Heqsub. exact IHbody.
  - (* T_App *)
    simpl. apply R_app with (T1 := T1).
    + apply (IH1 env S Hok).
    + apply (IH2 env S Hok).
  - (* T_True *)
    simpl. split.
    + apply SN_of_no_step. intros s Hs. inversion Hs.
    + intros t' Hm Hvl.
      apply multi_no_step with (t := tm_true) in Hm.
      * subst t'. left. reflexivity.
      * intros s Hs. inversion Hs.
  - (* T_False *)
    simpl. split.
    + apply SN_of_no_step. intros s Hs. inversion Hs.
    + intros t' Hm Hvl.
      apply multi_no_step with (t := tm_false) in Hm.
      * subst t'. right. reflexivity.
      * intros s Hs. inversion Hs.
  - (* T_If *)
    simpl. apply R_if.
    + apply (IH1 env S Hok).
    + apply (IH2 env S Hok).
    + apply (IH3 env S Hok).
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T H.
  assert (Hok : env_ok empty (fun x => tm_fvar x) nil).
  { unfold env_ok. split.
    - intros y. apply lc_fvar.
    - split.
      + intros y U Hy. cbv in Hy. discriminate Hy.
      + intros y Hy. reflexivity. }
  pose proof (fundamental empty t T H (fun x => tm_fvar x) nil Hok) as HR.
  rewrite subst_identity in HR.
  apply (R_sn T t HR).
Qed.

End STLCCBVNormalizationTask.
