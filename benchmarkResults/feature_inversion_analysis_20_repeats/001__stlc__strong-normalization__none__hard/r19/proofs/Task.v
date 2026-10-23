(** STLC call-by-value strong-normalization benchmark.
    No if-then-else, non-determinism, or recursion is included. *)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Relations.Relation_Definitions.
From Stdlib Require Import Lia.

Module STLCNormalizationNoneHardTask.

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

(** Target theorem: strong normalization for the supplied CBV relation. *)

Inductive strongly_normalizing : tm -> Prop :=
  | SN_intro : forall t,
      (forall t', t --> t' -> strongly_normalizing t') ->
      strongly_normalizing t.

(* ============================================================ *)
(* Auxiliary development for the strong normalization proof.     *)
(* ============================================================ *)

(** ** Free variables and fresh atoms *)

Fixpoint fvars (t : tm) : list atom :=
  match t with
  | tm_bvar _ => nil
  | tm_fvar x => x :: nil
  | tm_app t1 t2 => fvars t1 ++ fvars t2
  | tm_abs _ t1 => fvars t1
  | tm_true => nil
  | tm_false => nil
  end.

Fixpoint list_max (l : list atom) : nat :=
  match l with
  | nil => 0
  | x :: xs => Nat.max x (list_max xs)
  end.

Lemma in_list_max : forall (l : list atom) x, In x l -> x <= list_max l.
Proof.
  intros l. induction l as [| y ys IH]; intros x Hin.
  - destruct Hin.
  - simpl in *. destruct Hin as [-> | Hin].
    + apply Nat.le_max_l.
    + apply Nat.le_trans with (list_max ys);
        [apply IH; exact Hin | apply Nat.le_max_r].
Qed.

Lemma fresh_atom : forall (l : list atom), ~ In (S (list_max l)) l.
Proof.
  intros l Hin. apply in_list_max in Hin. lia.
Qed.

(** ** Local closure lemmas *)

Lemma lc_at_weaken : forall k t, lc_at k t -> forall j, k <= j -> lc_at j t.
Proof.
  intros k t H.
  induction H as [k i Hlt | k x | k t1 t2 H1 IH1 H2 IH2 | k T t1 H1 IH1 | k | k];
    intros j Hle.
  - apply lc_bvar. lia.
  - apply lc_fvar.
  - apply lc_app; [apply IH1 | apply IH2]; lia.
  - apply lc_abs. apply IH1. lia.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma lc_app_inv : forall k t1 t2, lc_at k (tm_app t1 t2) -> lc_at k t1 /\ lc_at k t2.
Proof. intros k t1 t2 H; inversion H; subst; auto. Qed.

Lemma lc_abs_inv : forall k T t, lc_at k (tm_abs T t) -> lc_at (S k) t.
Proof. intros k T t H; inversion H; subst; auto. Qed.

Lemma lc_open_rec : forall t k u,
  lc_at (S k) t -> lc_at k u -> lc_at k (open_rec k u t).
Proof.
  induction t as [i | x | t1 IH1 t2 IH2 | T t1 IH1 | | ];
    intros k u H Hu; simpl.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst i. exact Hu.
    + apply lc_bvar. apply Nat.eqb_neq in E.
      inversion H. lia.
  - apply lc_fvar.
  - apply lc_app_inv in H. destruct H as [H1 H2].
    apply lc_app; [apply IH1 | apply IH2]; assumption.
  - apply lc_abs_inv in H.
    apply lc_abs. apply IH1 with (k := S k).
    + exact H.
    + apply lc_at_weaken with (k := k); [exact Hu | lia].
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma lc_at_open_inv : forall t k x,
  lc_at k (open_rec k (tm_fvar x) t) -> lc_at (S k) t.
Proof.
  induction t as [i | y | t1 IH1 t2 IH2 | T t1 IH1 | | ];
    intros k x H; simpl in H.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst i. apply lc_bvar. lia.
    + apply lc_bvar. apply Nat.eqb_neq in E. inversion H. lia.
  - apply lc_fvar.
  - apply lc_app_inv in H. destruct H as [H1 H2].
    apply lc_app; [apply IH1 with (x := x) | apply IH2 with (x := x)]; assumption.
  - apply lc_abs_inv in H.
    apply lc_abs. apply IH1 with (k := S k) (x := x). exact H.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma lc_open_rec_id : forall t k j u,
  lc_at k t -> k <= j -> open_rec j u t = t.
Proof.
  induction t as [i | y | t1 IH1 t2 IH2 | T t1 IH1 | | ];
    intros k j u H Hle; simpl.
  - destruct (Nat.eqb j i) eqn:E.
    + apply Nat.eqb_eq in E. subst i. inversion H. lia.
    + reflexivity.
  - reflexivity.
  - apply lc_app_inv in H. destruct H as [H1 H2].
    assert (E1 : open_rec j u t1 = t1) by (apply IH1 with (k := k); assumption).
    assert (E2 : open_rec j u t2 = t2) by (apply IH2 with (k := k); assumption).
    rewrite E1, E2. reflexivity.
  - assert (E : open_rec (S j) u t1 = t1).
    { apply IH1 with (k := S k). apply lc_abs_inv in H. exact H. lia. }
    rewrite E. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v H. induction H as [T t Hlc | | ].
  - exact Hlc.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma abs_no_step : forall T body t', ~ (tm_abs T body --> t').
Proof. intros T body t' H; inversion H. Qed.

Lemma app_not_value : forall t1 t2, ~ value (tm_app t1 t2).
Proof. intros t1 t2 H; inversion H. Qed.

Lemma step_lc : forall t t', t --> t' -> locally_closed t -> locally_closed t'.
Proof.
  intros t t' H. induction H as [T body v Hlc0 Hval | t1 t1' t2 Hst IH Hlc2 |
                                  v1 t2 t2' Hval Hst IH]; intros Hlc.
  - (* ST_AppAbs *) unfold open.
    destruct (lc_app_inv 0 (tm_abs T body) v Hlc) as [H1 H2].
    apply lc_abs_inv in H1.
    apply lc_open_rec with (k := 0); assumption.
  - (* ST_App1 *)
    destruct (lc_app_inv 0 t1 t2 Hlc) as [H1 H2].
    apply lc_app; [apply IH; exact H1 | exact H2].
  - (* ST_App2 *)
    destruct (lc_app_inv 0 v1 t2 Hlc) as [H1 H2].
    apply lc_app; [exact H1 | apply IH; exact H2].
Qed.

(** ** Substitution of free variables *)

Definition update_env (gamma : atom -> tm) (x : atom) (u : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then u else gamma y.

Fixpoint subst (gamma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => gamma x
  | tm_app t1 t2 => tm_app (subst gamma t1) (subst gamma t2)
  | tm_abs T t1 => tm_abs T (subst gamma t1)
  | tm_true => tm_true
  | tm_false => tm_false
  end.

Lemma subst_lc : forall t k gamma,
  lc_at k t ->
  (forall x, locally_closed (gamma x)) ->
  lc_at k (subst gamma t).
Proof.
  induction t as [i | x | t1 IH1 t2 IH2 | T t1 IH1 | | ];
    intros k gamma H Henv; simpl.
  - apply lc_bvar. inversion H. assumption.
  - apply lc_at_weaken with (k := 0); [apply Henv | lia].
  - apply lc_app_inv in H. destruct H as [H1 H2].
    apply lc_app; [apply IH1 | apply IH2]; assumption.
  - apply lc_abs_inv in H.
    apply lc_abs. apply IH1 with (k := S k); assumption.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma subst_open_rec : forall t gamma k w,
  (forall x, locally_closed (gamma x)) ->
  subst gamma (open_rec k w t) = open_rec k (subst gamma w) (subst gamma t).
Proof.
  induction t as [i | x | t1 IH1 t2 IH2 | T t1 IH1 | | ];
    intros gamma k w Henv; simpl.
  - destruct (Nat.eqb k i) eqn:E; reflexivity.
  - symmetry. apply lc_open_rec_id with (k := 0). apply Henv. lia.
  - rewrite (IH1 gamma k w Henv). rewrite (IH2 gamma k w Henv). reflexivity.
  - rewrite (IH1 gamma (S k) w Henv). reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma subst_update_notin : forall t gamma x w,
  ~ In x (fvars t) ->
  subst (update_env gamma x w) t = subst gamma t.
Proof.
  induction t as [i | y | t1 IH1 t2 IH2 | T t1 IH1 | | ];
    intros gamma x w Hnotin; simpl in *.
  - reflexivity.
  - unfold update_env.
    assert (Hneq : x <> y).
    { intro Heq. apply Hnotin. subst y. simpl. auto. }
    destruct (Nat.eqb x y) eqn:E; [| reflexivity].
    apply Nat.eqb_eq in E. exfalso. exact (Hneq E).
  - assert (E1 : subst (update_env gamma x w) t1 = subst gamma t1).
    { apply IH1. intro Hin. apply Hnotin. apply in_or_app. left. exact Hin. }
    assert (E2 : subst (update_env gamma x w) t2 = subst gamma t2).
    { apply IH2. intro Hin. apply Hnotin. apply in_or_app. right. exact Hin. }
    rewrite E1, E2. reflexivity.
  - assert (E : subst (update_env gamma x w) t1 = subst gamma t1).
    { apply IH1. exact Hnotin. }
    rewrite E. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma subst_id : forall t, subst (fun x => tm_fvar x) t = t.
Proof.
  induction t as [i | x | t1 IH1 t2 IH2 | T t1 IH1 | | ]; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH1. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** ** Step inversion for applications *)

Lemma step_app_inv : forall t1 t2 r,
  tm_app t1 t2 --> r ->
  (exists T body v, t1 = tm_abs T body /\ r = open body v /\
                    locally_closed (tm_abs T body) /\ value v)
  \/ (exists t1', t1 --> t1' /\ r = tm_app t1' t2)
  \/ (exists t2', value t1 /\ t2 --> t2' /\ r = tm_app t1 t2').
Proof.
  intros t1 t2 r H. inversion H; subst; clear H.
  - left. eexists; eexists; eexists. repeat split; eauto.
  - right; left. eexists. split; eauto.
  - right; right. eexists. repeat split; eauto.
Qed.

Lemma step_abs_app_inv : forall A body u r,
  tm_app (tm_abs A body) u --> r ->
  (r = open body u /\ value u) \/
  (exists u', u --> u' /\ r = tm_app (tm_abs A body) u').
Proof.
  intros A body u r H. inversion H; subst; clear H.
  - left. split; eauto.
  - exfalso. eapply abs_no_step. eassumption.
  - right. eexists. split; eauto.
Qed.

(** ** The logical relation *)

Fixpoint R (T : ty) : tm -> Prop :=
  match T with
  | Ty_Bool => fun t => locally_closed t /\ strongly_normalizing t
  | Ty_Arrow T1 T2 => fun t =>
      locally_closed t /\ strongly_normalizing t /\
      (forall u, R T1 u -> R T2 (tm_app t u))
  end.

Lemma R_lc : forall T t, R T t -> locally_closed t.
Proof.
  intros T. induction T as [| T1 IH1 T2 IH2]; intros t H; simpl in H; tauto.
Qed.

Lemma R_SN : forall T t, R T t -> strongly_normalizing t.
Proof.
  intros T. induction T as [| T1 IH1 T2 IH2]; intros t H; simpl in H; tauto.
Qed.

Lemma SN_step : forall t t', t --> t' -> strongly_normalizing t -> strongly_normalizing t'.
Proof.
  intros t t' Hstep Hsn. destruct Hsn as [t0 Hred]. apply Hred. exact Hstep.
Qed.

Lemma R_step : forall T t t', R T t -> t --> t' -> R T t'.
Proof.
  intros T. induction T as [| T1 IH1 T2 IH2]; intros t t' HR Hstep.
  - simpl in HR. destruct HR as [Hlc Hsn]. simpl. split.
    + apply step_lc with (t := t); assumption.
    + eapply SN_step; eassumption.
  - simpl in HR. destruct HR as [Hlc [Hsn Harr]]. simpl. split; [| split].
    + apply step_lc with (t := t); assumption.
    + eapply SN_step; eassumption.
    + intros u Hu.
      eapply IH2.
      * apply Harr. exact Hu.
      * apply ST_App1; [exact Hstep | apply R_lc with (T := T1); exact Hu].
Qed.

Lemma R_intro_neutral : forall T t,
  locally_closed t ->
  ~ value t ->
  (forall t', t --> t' -> R T t') ->
  R T t.
Proof.
  intros T. induction T as [| T1 IH1 T2 IH2]; intros t Hlc Hnv Hred.
  - simpl. split; [exact Hlc |].
    apply SN_intro. intros t' Hs.
    apply R_SN with (T := Ty_Bool). apply Hred. exact Hs.
  - simpl. split; [exact Hlc | split].
    + apply SN_intro. intros t' Hs.
      apply R_SN with (T := Ty_Arrow T1 T2). apply Hred. exact Hs.
    + intros u Hu.
      apply IH2 with (t := tm_app t u).
      * apply lc_app; [exact Hlc | apply R_lc with (T := T1); exact Hu].
      * apply app_not_value.
      * intros r Hs.
        pose proof (step_app_inv t u r Hs) as Hcases.
        destruct Hcases as [Habs | [Happ1 | Happ2]].
        -- destruct Habs as [T0 [body [v [Heq1 [Heq2 [Hlc0 Hval]]]]]].
           exfalso. apply Hnv. rewrite Heq1. apply v_abs. exact Hlc0.
        -- destruct Happ1 as [t1' [Hst Heq]].
           rewrite Heq. pose proof (Hred t1' Hst) as Harr. simpl in Harr.
           destruct Harr as [Hl [Hsn' Harr2]]. apply Harr2. exact Hu.
        -- destruct Happ2 as [t2' [Hval [Hst Heq]]].
           exfalso. apply Hnv. exact Hval.
Qed.

Lemma abs_app : forall A B body,
  locally_closed (tm_abs A body) ->
  (forall v, value v -> R A v -> R B (open body v)) ->
  forall u, R A u -> R B (tm_app (tm_abs A body) u).
Proof.
  intros A B body Hlc Hbody u Hu.
  destruct B as [| C D].
  - (* B = Bool *)
    assert (Hmain : forall u0, strongly_normalizing u0 -> R A u0 ->
                    R Ty_Bool (tm_app (tm_abs A body) u0)).
    { intros u0 Hsn. induction Hsn as [u0 Hred IHred]. intros Hu0.
      simpl. split.
      + apply lc_app; [exact Hlc | apply R_lc with (T := A); exact Hu0].
      + apply SN_intro. intros r Hs.
        destruct (step_abs_app_inv A body u0 r Hs) as [[Heq Hval] | [u' [Hst Heq]]].
        * rewrite Heq. apply R_SN with (T := Ty_Bool). apply Hbody; assumption.
        * rewrite Heq. apply R_SN with (T := Ty_Bool).
          apply IHred; [exact Hst | apply R_step with (t := u0); assumption].
    }
    apply Hmain; [apply R_SN with (T := A); exact Hu | exact Hu].
  - (* B = Arrow C D *)
    assert (Hmain : forall u0, strongly_normalizing u0 -> R A u0 ->
                    R (Ty_Arrow C D) (tm_app (tm_abs A body) u0)).
    { intros u0 Hsn. induction Hsn as [u0 Hred IHred]. intros Hu0.
      simpl. split; [| split].
      + apply lc_app; [exact Hlc | apply R_lc with (T := A); exact Hu0].
      + apply SN_intro. intros r Hs.
        destruct (step_abs_app_inv A body u0 r Hs) as [[Heq Hval] | [u' [Hst Heq]]].
        * rewrite Heq. apply R_SN with (T := Ty_Arrow C D). apply Hbody; assumption.
        * rewrite Heq. apply R_SN with (T := Ty_Arrow C D).
          apply IHred; [exact Hst | apply R_step with (t := u0); assumption].
      + intros v Hv.
        apply R_intro_neutral with (T := D).
        * apply lc_app.
          -- apply lc_app; [exact Hlc | apply R_lc with (T := A); exact Hu0].
          -- apply R_lc with (T := C); exact Hv.
        * apply app_not_value.
        * intros r Hs.
          pose proof (step_app_inv (tm_app (tm_abs A body) u0) v r Hs) as Hcases.
          destruct Hcases as [Habs | [Happ1 | Happ2]].
          -- destruct Habs as [T0 [body0 [v0 [Heq1 [Heq2 [Hlc0 Hval0]]]]]].
             exfalso. discriminate Heq1.
          -- destruct Happ1 as [f' [Hst Heq]].
             rewrite Heq.
             destruct (step_abs_app_inv A body u0 f' Hst)
               as [[Heq' Hval'] | [u' [Hst' Heq']]].
             ++ rewrite Heq'. pose proof (Hbody u0 Hval' Hu0) as Harr.
                simpl in Harr. destruct Harr as [Hl [Hsn' Harr2]]. apply Harr2. exact Hv.
             ++ rewrite Heq'. pose proof (IHred u' Hst' (R_step A u0 u' Hu0 Hst')) as Harr.
                simpl in Harr. destruct Harr as [Hl [Hsn' Harr2]]. apply Harr2. exact Hv.
          -- destruct Happ2 as [v2 [Hval2 [Hst Heq]]].
             exfalso. apply app_not_value in Hval2. exact Hval2.
    }
    apply Hmain; [apply R_SN with (T := A); exact Hu | exact Hu].
Qed.

Lemma abs_intro : forall A B body,
  locally_closed (tm_abs A body) ->
  (forall v, value v -> R A v -> R B (open body v)) ->
  R (Ty_Arrow A B) (tm_abs A body).
Proof.
  intros A B body Hlc Hbody.
  simpl. split; [exact Hlc | split].
  - apply SN_intro. intros t' Hs. exfalso. exact (abs_no_step A body t' Hs).
  - apply abs_app; assumption.
Qed.

(** ** Environment interpretation *)

Definition env_CR (Gamma : context) (gamma : atom -> tm) : Prop :=
  (forall x, locally_closed (gamma x)) /\
  (forall x T, Gamma x = Some T -> R T (gamma x)).

Lemma update_env_lc : forall gamma x u,
  (forall y, locally_closed (gamma y)) ->
  locally_closed u ->
  forall y, locally_closed ((update_env gamma x u) y).
Proof.
  intros gamma x u Hg Hu y. unfold update_env.
  destruct (Nat.eqb x y) eqn:E; auto.
Qed.

Lemma update_env_R : forall Gamma gamma x T1 u,
  env_CR Gamma gamma ->
  R T1 u ->
  forall y T, update Gamma x T1 y = Some T -> R T ((update_env gamma x u) y).
Proof.
  intros Gamma gamma x T1 u [Hlc HR] Hu y T Heq.
  unfold update in Heq.
  destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. subst y.
    injection Heq as HT. subst T.
    unfold update_env. simpl. rewrite Nat.eqb_refl. exact Hu.
  - pose proof (HR y T Heq) as HRy.
    unfold update_env. simpl. rewrite E. exact HRy.
Qed.

Lemma has_type_lc : forall Gamma t T, has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T H.
  induction H as [Gamma0 x T0 Heq | L Gamma0 T1 T2 t1 Hprem IHprem |
                  Gamma0 t1 t2 T1 T2 H1 IH1 H2 IH2 | Gamma0 | Gamma0].
  - apply lc_fvar.
  - set (x := S (list_max (L ++ fvars t1))).
    assert (Hx : ~ In x L).
    { intro Hin. apply (fresh_atom (L ++ fvars t1)). apply in_or_app. left. exact Hin. }
    apply lc_abs.
    pose proof (IHprem x Hx) as Hlcx.
    apply lc_at_open_inv with (k := 0) (x := x). exact Hlcx.
  - apply lc_app; assumption.
  - apply lc_true.
  - apply lc_false.
Qed.

(** ** Fundamental theorem *)

Lemma fundamental : forall Gamma t T,
  has_type Gamma t T ->
  forall gamma, env_CR Gamma gamma -> R T (subst gamma t).
Proof.
  intros Gamma t T H.
  induction H as [Gamma0 x T0 Heq | L Gamma0 T1 T2 t1 Hprem IHprem |
                  Gamma0 t1 t2 T1 T2 H1 IH1 H2 IH2 | Gamma0 | Gamma0];
    intros gamma Henv.
  - (* T_Var *) simpl. destruct Henv as [Hlc HR]. apply HR. exact Heq.
  - (* T_Abs *) simpl.
    apply abs_intro.
    + (* local closure of the abstraction *)
      apply lc_abs.
      apply (subst_lc t1 1 gamma).
      * set (x := S (list_max (L ++ fvars t1))).
        assert (Hx : ~ In x L).
        { intro Hin. apply (fresh_atom (L ++ fvars t1)). apply in_or_app. left. exact Hin. }
        pose proof (Hprem x Hx) as Hty.
        pose proof (has_type_lc _ _ _ Hty) as Hlcx.
        apply lc_at_open_inv with (k := 0) (x := x). exact Hlcx.
      * destruct Henv as [Hlc _]. exact Hlc.
    + (* body condition *)
      intros v Hval Hv.
      set (x := S (list_max (L ++ fvars t1))).
      assert (HxL : ~ In x L).
      { intro Hin. apply (fresh_atom (L ++ fvars t1)). apply in_or_app. left. exact Hin. }
      assert (Hxt : ~ In x (fvars t1)).
      { intro Hin. apply (fresh_atom (L ++ fvars t1)). apply in_or_app. right. exact Hin. }
      assert (Henv' : env_CR (update Gamma0 x T1) (update_env gamma x v)).
      { split.
        - apply update_env_lc.
          + destruct Henv as [Hlc _]; exact Hlc.
          + apply R_lc with (T := T1); exact Hv.
        - intros y T0 Hy. apply update_env_R with (Gamma := Gamma0) (T1 := T1);
            [exact Henv | exact Hv | exact Hy]. }
      specialize (IHprem x HxL (update_env gamma x v) Henv').
      assert (Hsub1 : subst (update_env gamma x v) (tm_fvar x) = v).
      { unfold update_env. simpl. rewrite Nat.eqb_refl. reflexivity. }
      assert (Hsub2 : subst (update_env gamma x v) t1 = subst gamma t1).
      { apply subst_update_notin. exact Hxt. }
      assert (Hop : subst (update_env gamma x v) (open t1 (tm_fvar x))
                   = open_rec 0 v (subst gamma t1)).
      { unfold open.
        rewrite (subst_open_rec t1 (update_env gamma x v) 0 (tm_fvar x)).
        - rewrite Hsub1, Hsub2. reflexivity.
        - apply update_env_lc.
          + destruct Henv as [Hlc _]; exact Hlc.
          + apply R_lc with (T := T1); exact Hv. }
      rewrite Hop in IHprem.
      exact IHprem.
  - (* T_App *) simpl.
    destruct Henv as [Hlc HR].
    pose proof (IH1 gamma (conj Hlc HR)) as Harr.
    pose proof (IH2 gamma (conj Hlc HR)) as Harg.
    simpl in Harr. destruct Harr as [Hl [Hsn Harr2]]. apply Harr2. exact Harg.
  - (* T_True *) simpl. split.
    + apply lc_true.
    + apply SN_intro. intros t' Hs. inversion Hs.
  - (* T_False *) simpl. split.
    + apply lc_false.
    + apply SN_intro. intros t' Hs. inversion Hs.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  assert (Henv : env_CR empty (fun x => tm_fvar x)).
  { split.
    - intros x. apply lc_fvar.
    - intros x T0 Heq. unfold empty in Heq. discriminate. }
  pose proof (fundamental empty t T Hty (fun x => tm_fvar x) Henv) as HR.
  rewrite subst_id in HR.
  apply R_SN with (T := T). exact HR.
Qed.

End STLCNormalizationNoneHardTask.
