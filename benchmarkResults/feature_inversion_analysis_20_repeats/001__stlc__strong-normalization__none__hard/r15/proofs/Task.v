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

(** ** Substitution of free variables (atoms). *)

Fixpoint subst_tm (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_app t1 t2 => tm_app (subst_tm sigma t1) (subst_tm sigma t2)
  | tm_abs T t1 => tm_abs T (subst_tm sigma t1)
  | tm_true => tm_true
  | tm_false => tm_false
  end.

Definition upd (sigma : atom -> tm) (x : atom) (v : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then v else sigma y.

Lemma subst_tm_fvar : forall sigma x, subst_tm sigma (tm_fvar x) = sigma x.
Proof. reflexivity. Qed.

Lemma upd_same : forall sigma x v, upd sigma x v x = v.
Proof. intros. unfold upd. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma upd_neq : forall sigma x y v, x <> y -> upd sigma x v y = sigma y.
Proof.
  intros sigma x y v H. unfold upd.
  destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. contradiction.
  - reflexivity.
Qed.

(** Free variables of a term. *)

Fixpoint fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ => nil
  | tm_fvar x => x :: nil
  | tm_app t1 t2 => fv t1 ++ fv t2
  | tm_abs _ t1 => fv t1
  | tm_true => nil
  | tm_false => nil
  end.

Lemma subst_tm_id : forall t, subst_tm (fun x => tm_fvar x) t = t.
Proof. induction t; simpl; congruence. Qed.

Lemma lc_at_mono : forall k j t, k <= j -> lc_at k t -> lc_at j t.
Proof.
  intros k j t Hle Hlc. revert j Hle.
  induction Hlc as [k' i Hi | k' x | k' a b H1 IH1 H2 IH2 | k' T b H1 IH1 | k' | k'];
    intros j Hle.
  - apply lc_bvar. lia.
  - apply lc_fvar.
  - apply lc_app; [apply IH1 | apply IH2]; exact Hle.
  - apply lc_abs. apply IH1. lia.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma open_rec_lc : forall s k u, lc_at k s -> open_rec k u s = s.
Proof.
  intros s. induction s as [n | a | s1 IH1 s2 IH2 | T s1 IH | |];
    intros k u Hlc; simpl.
  - inversion Hlc; subst.
    assert (H : (k =? n) = false) by (apply Nat.eqb_neq; lia).
    rewrite H. reflexivity.
  - reflexivity.
  - inversion Hlc; subst. rewrite IH1 by assumption. rewrite IH2 by assumption.
    reflexivity.
  - inversion Hlc; subst. rewrite IH with (k := S k) by assumption. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma subst_tm_open_rec : forall sigma t u k,
  (forall x, locally_closed (sigma x)) ->
  subst_tm sigma (open_rec k u t) =
  open_rec k (subst_tm sigma u) (subst_tm sigma t).
Proof.
  intros sigma t. induction t as [n | a | t1 IH1 t2 IH2 | T t1 IH | |];
    intros u k Hlc; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - rewrite open_rec_lc with (k := k) (u := subst_tm sigma u).
    + reflexivity.
    + apply lc_at_mono with (k := 0); [lia | apply Hlc].
  - rewrite IH1 by exact Hlc. rewrite IH2 by exact Hlc. reflexivity.
  - rewrite IH by exact Hlc. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma subst_tm_upd_notin : forall sigma x v t,
  ~ In x (fv t) -> subst_tm (upd sigma x v) t = subst_tm sigma t.
Proof.
  intros sigma x v t. induction t as [n | a | t1 IH1 t2 IH2 | T t1 IH | |];
    simpl; intros H.
  - reflexivity.
  - unfold upd. destruct (Nat.eqb x a) eqn:E.
    + exfalso. apply H. apply Nat.eqb_eq in E. subst a. simpl. left. reflexivity.
    + reflexivity.
  - assert (H1 : ~ In x (fv t1))
      by (intro Hc; apply H; apply in_app_iff; left; exact Hc).
    assert (H2 : ~ In x (fv t2))
      by (intro Hc; apply H; apply in_app_iff; right; exact Hc).
    rewrite IH1 by exact H1. rewrite IH2 by exact H2. reflexivity.
  - rewrite IH by exact H. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** Fresh atoms. *)

Fixpoint max_atoms (l : list atom) : atom :=
  match l with
  | nil => 0
  | x :: xs => Nat.max x (max_atoms xs)
  end.

Lemma in_max_atoms : forall l x, In x l -> x <= max_atoms l.
Proof.
  induction l as [| y ys IH]; simpl; intros x H.
  - contradiction.
  - destruct H as [-> | H].
    + apply Nat.le_max_l.
    + apply Nat.le_trans with (max_atoms ys); [apply IH; exact H | apply Nat.le_max_r].
Qed.

Lemma fresh_atom : forall l : list atom, exists x, ~ In x l.
Proof.
  intros l. exists (S (max_atoms l)). intro H.
  apply in_max_atoms in H. lia.
Qed.

(** Basic properties of local closure. *)

Lemma lc_open_rec : forall s k u,
  lc_at (S k) s -> lc_at k u -> lc_at k (open_rec k u s).
Proof.
  intros s. induction s as [n | a | s1 IH1 s2 IH2 | T s1 IH | |];
    intros k u Hlc Hu; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. exact Hu.
    + apply lc_bvar. inversion Hlc; subst. apply Nat.eqb_neq in E. lia.
  - apply lc_fvar.
  - inversion Hlc; subst. apply lc_app; [apply IH1 | apply IH2]; assumption.
  - apply lc_abs. apply IH with (k := S k).
    + inversion Hlc; subst. assumption.
    + apply lc_at_mono with (k := k); [lia | exact Hu].
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma lc_open_inv : forall s k u,
  lc_at k (open_rec k u s) -> lc_at (S k) s.
Proof.
  intros s. induction s as [n | a | s1 IH1 s2 IH2 | T s1 IH | |];
    intros k u H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. apply lc_bvar. lia.
    + apply lc_bvar. inversion H; subst. lia.
  - apply lc_fvar.
  - inversion H; subst.
    apply lc_app; [eapply IH1; eassumption | eapply IH2; eassumption].
  - inversion H; subst. apply lc_abs.
    eapply IH with (k := S k); eassumption.
  - apply lc_true.
  - apply lc_false.
Qed.

(** Values, stuck terms, and inversion principles for [step]. *)

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v H. destruct H as [T t Hlc | |].
  - exact Hlc.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma app_not_value : forall t1 t2, ~ value (tm_app t1 t2).
Proof. intros t1 t2 H. inversion H. Qed.

Lemma fvar_not_value : forall x, ~ value (tm_fvar x).
Proof. intros x H. inversion H. Qed.

Lemma abs_not_step : forall T t t', ~ (tm_abs T t --> t').
Proof. intros T t t' H. inversion H. Qed.

Lemma fvar_no_step : forall x t', ~ (tm_fvar x --> t').
Proof. intros x t' H. inversion H. Qed.

Lemma lc_app_inv : forall k t1 t2,
  lc_at k (tm_app t1 t2) -> lc_at k t1 /\ lc_at k t2.
Proof. intros k t1 t2 H. inversion H; subst; auto. Qed.

Lemma lc_abs_inv : forall k T t,
  lc_at k (tm_abs T t) -> lc_at (S k) t.
Proof. intros k T t H. inversion H; subst; assumption. Qed.

Lemma step_app_cases : forall t v w,
  tm_app t v --> w ->
  (exists T s, t = tm_abs T s /\ w = open s v) \/
  (exists t', t --> t' /\ w = tm_app t' v) \/
  (exists v', value t /\ v --> v' /\ w = tm_app t v').
Proof.
  intros t v w H. inversion H; subst.
  - left. eexists. eexists. split; reflexivity.
  - right. left. eexists. split; [eassumption | reflexivity].
  - right. right. eexists. split; [eassumption | split; [eassumption | reflexivity]].
Qed.

Lemma lc_step : forall t t', t --> t' -> locally_closed t -> locally_closed t'.
Proof.
  intros t t' Hst. induction Hst; intros Hlc.
  - apply lc_app_inv in Hlc. destruct Hlc as [Hla Hlv].
    apply lc_abs_inv in Hla.
    apply lc_open_rec with (k := 0); assumption.
  - apply lc_app_inv in Hlc. destruct Hlc as [Hl1 Hl2].
    apply lc_app; [apply IHHst; exact Hl1 | exact Hl2].
  - apply lc_app_inv in Hlc. destruct Hlc as [Hlv Hl2].
    apply lc_app; [exact Hlv | apply IHHst; exact Hl2].
Qed.

Lemma SN_step : forall t t', strongly_normalizing t -> t --> t' -> strongly_normalizing t'.
Proof.
  intros t t' Hsn. induction Hsn as [t Hred IH]. intros Hst. apply Hred. exact Hst.
Qed.

Lemma SN_ind : forall (P : tm -> Prop),
  (forall t, (forall t', t --> t' -> P t') -> P t) ->
  forall t, strongly_normalizing t -> P t.
Proof.
  intros P H t Hsn. induction Hsn as [t Hred IH]. apply H. exact IH.
Qed.

(** ** The logical relation. *)

Fixpoint LR (T : ty) (t : tm) : Prop :=
  match T with
  | Ty_Bool => strongly_normalizing t /\ locally_closed t
  | Ty_Arrow T1 T2 =>
      strongly_normalizing t /\ locally_closed t /\
      (forall u, LR T1 u -> LR T2 (tm_app t u))
  end.

Lemma LR_sn : forall T t, LR T t -> strongly_normalizing t.
Proof.
  induction T as [| A IHA B IHB]; simpl; intros t H.
  - destruct H as [Hsn Hlc]. exact Hsn.
  - destruct H as [Hsn [Hlc Hfun]]. exact Hsn.
Qed.

Lemma LR_lc : forall T t, LR T t -> locally_closed t.
Proof.
  induction T as [| A IHA B IHB]; simpl; intros t H.
  - destruct H as [Hsn Hlc]. exact Hlc.
  - destruct H as [Hsn [Hlc Hfun]]. exact Hlc.
Qed.

Lemma LR_step : forall T t t', LR T t -> t --> t' -> LR T t'.
Proof.
  induction T as [| A IHA B IHB]; simpl; intros t t' H Hst.
  - destruct H as [Hsn Hlc]. split.
    + apply SN_step with (t := t); assumption.
    + apply lc_step with (t := t); assumption.
  - destruct H as [Hsn [Hlc Hfun]]. split.
    + apply SN_step with (t := t); assumption.
    + split.
      * apply lc_step with (t := t); assumption.
      * intros u Hu.
        apply (IHB (tm_app t u) (tm_app t' u)).
        -- apply Hfun. exact Hu.
        -- eapply ST_App1; [exact Hst | apply LR_lc with (T := A); exact Hu].
Qed.

(** Backward closure for non-values. *)
Lemma LR_back : forall T t,
  locally_closed t ->
  ~ value t ->
  strongly_normalizing t ->
  (forall t', t --> t' -> LR T t') ->
  LR T t.
Proof.
  induction T as [| A IHA B IHB]; simpl; intros t Hlc Hnv Hsn Hred.
  - split; assumption.
  - split.
    + exact Hsn.
    + split.
      * exact Hlc.
      * intros u Hu.
        assert (Hreds : forall w, tm_app t u --> w -> LR B w).
        { intros w Hst.
          destruct (step_app_cases t u w Hst) as
            [[T0 [s [Heq Hw]]] | [[t' [Hstep Hw]] | [u' [Hval [Hstep Hw]]]]].
          - exfalso. apply Hnv. rewrite Heq. apply v_abs. rewrite Heq in Hlc. exact Hlc.
          - rewrite Hw. destruct (Hred t' Hstep) as [Hsn' [Hlc' Hfun']].
            apply Hfun'. exact Hu.
          - exfalso. apply Hnv. exact Hval. }
        refine (IHB (tm_app t u) _ _ _ _).
        -- apply lc_app; [exact Hlc | apply LR_lc with (T := A); exact Hu].
        -- apply app_not_value.
        -- apply SN_intro. intros w Hst. apply LR_sn with (T := B). apply Hreds. exact Hst.
        -- exact Hreds.
Qed.

Lemma LR_fvar : forall T x, LR T (tm_fvar x).
Proof.
  induction T as [| A IHA B IHB]; simpl.
  - split.
    + apply SN_intro. intros t' Hst. inversion Hst.
    + apply lc_fvar.
  - split.
    + apply SN_intro. intros t' Hst. inversion Hst.
    + split.
      * apply lc_fvar.
      * intros u Hu.
        assert (Hnw : forall w, tm_app (tm_fvar x) u --> w -> False).
        { intros w Hst.
          destruct (step_app_cases (tm_fvar x) u w Hst) as
            [[T0 [s [Heq Hw]]] | [[t' [Hstep Hw]] | [u' [Hval [Hstep Hw]]]]].
          - discriminate Heq.
          - eapply fvar_no_step. eexact Hstep.
          - eapply fvar_not_value. eexact Hval. }
        refine (LR_back B (tm_app (tm_fvar x) u) _ _ _ _).
        -- apply lc_app; [apply lc_fvar | apply LR_lc with (T := A); exact Hu].
        -- apply app_not_value.
        -- apply SN_intro. intros w Hst. exfalso. apply (Hnw w Hst).
        -- intros w Hst. exfalso. apply (Hnw w Hst).
Qed.

(** ** Environment semantics *)

Definition env_sem (Gamma : context) (sigma : atom -> tm) : Prop :=
  (forall x, locally_closed (sigma x)) /\
  (forall x T, Gamma x = Some T -> LR T (sigma x)).

Lemma env_sem_lc : forall Gamma sigma,
  env_sem Gamma sigma -> forall x, locally_closed (sigma x).
Proof. intros Gamma sigma [H _]. exact H. Qed.

Lemma env_sem_ty : forall Gamma sigma,
  env_sem Gamma sigma -> forall x T, Gamma x = Some T -> LR T (sigma x).
Proof. intros Gamma sigma [_ H]. exact H. Qed.

Lemma env_sem_update : forall Gamma sigma x T v,
  env_sem Gamma sigma -> LR T v -> env_sem (update Gamma x T) (upd sigma x v).
Proof.
  intros Gamma sigma x T v [Hlc Henv] Hv. split.
  - intro y. unfold upd.
    remember (Nat.eqb x y) as b eqn:E. destruct b.
    + apply LR_lc with (T := T). exact Hv.
    + apply Hlc.
  - intros y U Hy. unfold update in Hy. unfold upd.
    remember (Nat.eqb x y) as b eqn:E. destruct b.
    + simpl in Hy. injection Hy as Heq. subst U. exact Hv.
    + apply Henv. simpl in Hy. exact Hy.
Qed.

(** ** Fundamental theorem *)

Lemma fundamental : forall Gamma t T,
  has_type Gamma t T ->
  forall sigma, env_sem Gamma sigma -> LR T (subst_tm sigma t).
Proof.
  intros Gamma t T Hty.
  induction Hty as [Gamma0 x0 T0 Hlookup
                 | L Gamma0 T1 T2 t1 Hbody IHbody
                 | Gamma0 t1 t2 T1 T2 H1 IH1 H2 IH2
                 | Gamma0
                 | Gamma0]; intros sigma Henv.
  - (* T_Var *) simpl. eapply env_sem_ty; eassumption.
  - (* T_Abs *)
    simpl.
    destruct (fresh_atom (L ++ fv t1)) as [x Hx].
    assert (HxL : ~ In x L)
      by (intro Hc; apply Hx; apply in_app_iff; left; exact Hc).
    assert (Hxfv : ~ In x (fv t1))
      by (intro Hc; apply Hx; apply in_app_iff; right; exact Hc).
    assert (Hsub : forall u, locally_closed u ->
      subst_tm (upd sigma x u) (open t1 (tm_fvar x)) = open (subst_tm sigma t1) u).
    { intros u Hlu. unfold open.
      assert (Hsig : forall y, locally_closed (upd sigma x u y)).
      { intro y. unfold upd.
        remember (Nat.eqb x y) as b eqn:E. destruct b.
        - exact Hlu.
        - exact (env_sem_lc Gamma0 sigma Henv y). }
      rewrite (subst_tm_open_rec (upd sigma x u) t1 (tm_fvar x) 0 Hsig).
      rewrite subst_tm_fvar. rewrite upd_same.
      rewrite subst_tm_upd_notin by exact Hxfv. reflexivity. }
    assert (Hs : forall u, LR T1 u -> LR T2 (open (subst_tm sigma t1) u)).
    { intros u Hu.
      pose proof (IHbody x HxL (upd sigma x u)) as Hiu.
      assert (Hlu : locally_closed u) by (apply LR_lc with (T := T1); exact Hu).
      rewrite <- (Hsub u Hlu).
      apply Hiu. apply env_sem_update; [exact Henv | exact Hu]. }
    assert (Hlc_s : lc_at 1 (subst_tm sigma t1)).
    { pose proof (Hs (tm_fvar 0) (LR_fvar T1 0)) as H0.
      pose proof (LR_lc T2 _ H0) as H1.
      exact (lc_open_inv (subst_tm sigma t1) 0 (tm_fvar 0) H1). }
    split.
    + (* strong normalization of the abstraction *)
      apply SN_intro. intros t' Hst. inversion Hst.
    + split.
      * (* local closure *) apply lc_abs. exact Hlc_s.
      * (* application closure *)
        intros u Hu.
        assert (Hsn_u : strongly_normalizing u)
          by (apply LR_sn with (T := T1); exact Hu).
        revert Hu.
        refine (SN_ind
          (fun v => LR T1 v ->
             LR T2 (tm_app (tm_abs T1 (subst_tm sigma t1)) v)) _ u Hsn_u).
        intros v Hred Hv.
        assert (Hreds : forall w,
          tm_app (tm_abs T1 (subst_tm sigma t1)) v --> w -> LR T2 w).
        { intros w Hst.
          destruct (step_app_cases (tm_abs T1 (subst_tm sigma t1)) v w Hst) as
            [[T0 [s [Heq Hw]]] | [[t' [Hstep Hw]] | [v' [Hval [Hstep Hw]]]]].
          - injection Heq as HT Hs_eq. subst T0. subst s.
            rewrite Hw. apply Hs. exact Hv.
          - exfalso. eapply abs_not_step. eexact Hstep.
          - rewrite Hw. apply Hred.
            + exact Hstep.
            + apply LR_step with (t := v); [exact Hv | exact Hstep]. }
        refine (LR_back T2 (tm_app (tm_abs T1 (subst_tm sigma t1)) v) _ _ _ _).
        -- (* local closure *)
           apply lc_app; [apply lc_abs; exact Hlc_s | apply LR_lc with (T := T1); exact Hv].
        -- apply app_not_value.
        -- apply SN_intro. intros w Hst. apply LR_sn with (T := T2).
           apply Hreds. exact Hst.
        -- exact Hreds.
  - (* T_App *)
    simpl. destruct (IH1 sigma Henv) as [Hsn [Hlc Hfun]].
    apply Hfun. apply IH2. exact Henv.
  - (* T_True *)
    simpl. split.
    + apply SN_intro. intros t' Hst. inversion Hst.
    + apply lc_true.
  - (* T_False *)
    simpl. split.
    + apply SN_intro. intros t' Hst. inversion Hst.
    + apply lc_false.
Qed.

(** ** Target theorem *)

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  assert (Henv : env_sem empty (fun x => tm_fvar x)).
  { split.
    - intro x. apply lc_fvar.
    - intros x U Hc. unfold empty in Hc. discriminate Hc. }
  pose proof (fundamental empty t T Hty (fun x => tm_fvar x) Henv) as HLR.
  rewrite subst_tm_id in HLR.
  apply LR_sn with (T := T). exact HLR.
Qed.

End STLCNormalizationNoneHardTask.
