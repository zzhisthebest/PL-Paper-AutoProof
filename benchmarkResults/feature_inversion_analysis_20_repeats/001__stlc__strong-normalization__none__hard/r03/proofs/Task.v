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


(** ** Auxiliary definitions and lemmas for strong normalization.

    We prove strong normalization via a unary, type-indexed logical
    relation over terms.  Because binders are locally nameless, the
    typing context is interpreted by a substitution from atoms to terms
    (free-variable substitution). *)

(** Substitution of free (named) variables.  This is a plain homomorphism
    on terms: local binders are [tm_bvar], so no shifting is needed. *)

Fixpoint subst_fvar (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_app t1 t2 => tm_app (subst_fvar sigma t1) (subst_fvar sigma t2)
  | tm_abs T t1 => tm_abs T (subst_fvar sigma t1)
  | tm_true => tm_true
  | tm_false => tm_false
  end.

(** Free atoms occurring in a term. *)

Fixpoint fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ => nil
  | tm_fvar x => x :: nil
  | tm_app t1 t2 => fv t1 ++ fv t2
  | tm_abs _ t1 => fv t1
  | tm_true => nil
  | tm_false => nil
  end.

(** A fresh atom for a finite list of atoms. *)

Fixpoint atom_max (L : list atom) : atom :=
  match L with
  | nil => 0
  | x :: L' => Nat.max x (atom_max L')
  end.

Definition fresh (L : list atom) : atom := S (atom_max L).

Lemma in_atom_max : forall L x, In x L -> x <= atom_max L.
Proof.
  induction L as [| y L IH]; intros x Hx; simpl in *.
  - contradiction.
  - destruct Hx as [-> | Hx].
    + apply Nat.le_max_l.
    + apply Nat.le_trans with (atom_max L);
        [apply IH; exact Hx | apply Nat.le_max_r].
Qed.

Lemma fresh_not_in : forall L, ~ In (fresh L) L.
Proof.
  intros L Hin. apply in_atom_max in Hin. unfold fresh in Hin. lia.
Qed.

Lemma fresh_pair : forall L1 L2, exists (x : atom), ~ In x L1 /\ ~ In x L2.
Proof.
  intros L1 L2. exists (fresh (L1 ++ L2)). split.
  - intro Hin. apply (fresh_not_in (L1 ++ L2)). apply in_app_iff. left. exact Hin.
  - intro Hin. apply (fresh_not_in (L1 ++ L2)). apply in_app_iff. right. exact Hin.
Qed.

(** A locally closed term is unaffected by opening at any index that
    does not reach its (bound) variables. *)

Lemma lc_open_rec : forall t k, lc_at k t -> forall j v, k <= j -> open_rec j v t = t.
Proof.
  intros t k H. induction H; intros j0 v0 Hle; simpl.
  - destruct (Nat.eqb j0 i) eqn:E.
    + apply Nat.eqb_eq in E. subst i. lia.
    + reflexivity.
  - reflexivity.
  - rewrite (IHlc_at1 j0 v0 Hle), (IHlc_at2 j0 v0 Hle). reflexivity.
  - f_equal. apply (IHlc_at (S j0) v0). lia.
  - reflexivity.
  - reflexivity.
Qed.

(** Opening and free-variable substitution commute, provided the
    substitution maps every atom to a locally closed term. *)

Lemma subst_fvar_open_rec : forall sigma t k u,
  (forall x, locally_closed (sigma x)) ->
  subst_fvar sigma (open_rec k u t) =
  open_rec k (subst_fvar sigma u) (subst_fvar sigma t).
Proof.
  intros sigma t.
  induction t as [i|x|t1 IH1 t2 IH2|T t IH| |]; intros k u Hlc; simpl.
  - destruct (Nat.eqb k i); reflexivity.
  - symmetry. apply lc_open_rec with (k := 0); [apply Hlc | lia].
  - rewrite (IH1 k u Hlc), (IH2 k u Hlc). reflexivity.
  - rewrite (IH (S k) u Hlc). reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma subst_fvar_open : forall sigma t u,
  (forall x, locally_closed (sigma x)) ->
  subst_fvar sigma (open t u) = open (subst_fvar sigma t) (subst_fvar sigma u).
Proof.
  intros. unfold open. apply subst_fvar_open_rec. exact H.
Qed.

Lemma subst_fvar_id : forall t, subst_fvar (fun x => tm_fvar x) t = t.
Proof.
  induction t as [i|x|t1 IH1 t2 IH2|T t IH| |]; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IH1, IH2; reflexivity.
  - rewrite IH; reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma subst_fvar_agree : forall sigma1 sigma2 t,
  (forall x, In x (fv t) -> sigma1 x = sigma2 x) ->
  subst_fvar sigma1 t = subst_fvar sigma2 t.
Proof.
  intros sigma1 sigma2 t.
  induction t as [i|x|t1 IH1 t2 IH2|T t IH| |]; intros Hagree; simpl.
  - reflexivity.
  - apply Hagree. simpl. auto.
  - f_equal.
    + apply IH1. intros x Hx. apply Hagree. apply in_app_iff. left. exact Hx.
    + apply IH2. intros x Hx. apply Hagree. apply in_app_iff. right. exact Hx.
  - f_equal. apply IH. intros x Hx. apply Hagree. exact Hx.
  - reflexivity.
  - reflexivity.
Qed.

(** Basic facts about values and the step relation. *)

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v Hv. induction Hv as [T t Hlc | | ].
  - exact Hlc.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma abs_no_step : forall T t t', ~ (tm_abs T t --> t').
Proof. intros T t t' H; inversion H. Qed.

Lemma value_no_step : forall v, value v -> forall t', ~ (v --> t').
Proof.
  intros v Hv. induction Hv as [T t Hlc | | ]; intros t' H.
  - apply (abs_no_step T t t'); exact H.
  - inversion H.
  - inversion H.
Qed.

Lemma app_not_value : forall t1 t2, ~ value (tm_app t1 t2).
Proof. intros t1 t2 H; inversion H. Qed.

Lemma SN_step : forall t t',
  strongly_normalizing t -> t --> t' -> strongly_normalizing t'.
Proof.
  intros t t' HSN Hstep. inversion HSN as [u Hred]. apply Hred. exact Hstep.
Qed.

Lemma SN_abs : forall T t, strongly_normalizing (tm_abs T t).
Proof.
  intros T t. apply SN_intro. intros t' H.
  exfalso. apply (abs_no_step T t t'). exact H.
Qed.

Lemma SN_true : strongly_normalizing tm_true.
Proof. apply SN_intro. intros t' H. inversion H. Qed.

Lemma SN_false : strongly_normalizing tm_false.
Proof. apply SN_intro. intros t' H. inversion H. Qed.

(** Deciding whether a term is a value. *)

Lemma lc_at_dec : forall t k, lc_at k t \/ ~ lc_at k t.
Proof.
  induction t as [i|x|t1 IH1 t2 IH2|T t IH| |]; intros k.
  - destruct (Nat.lt_ge_cases i k) as [Hlt | Hge].
    + left. apply lc_bvar. exact Hlt.
    + right. intro H. inversion H. lia.
  - left. apply lc_fvar.
  - destruct (IH1 k) as [H1 | H1]; destruct (IH2 k) as [H2 | H2].
    + left. apply lc_app; assumption.
    + right. intro H. inversion H; auto.
    + right. intro H. inversion H; auto.
    + right. intro H. inversion H; auto.
  - destruct (IH (S k)) as [H1 | H1].
    + left. apply lc_abs. exact H1.
    + right. intro H. inversion H; auto.
  - left. apply lc_true.
  - left. apply lc_false.
Qed.

Lemma value_abs_lc : forall T t, value (tm_abs T t) -> lc_at 1 t.
Proof.
  intros T t H. inversion H as [T' t' Hlc | | ]. inversion Hlc. assumption.
Qed.

Lemma value_dec : forall t, value t \/ ~ value t.
Proof.
  intros t. destruct t as [i|x|t1 t2|T t1| |].
  - right. intro H. inversion H.
  - right. intro H. inversion H.
  - right. intro H. inversion H.
  - destruct (lc_at_dec t1 1) as [Hlc | Hnlc].
    + left. apply v_abs. apply lc_abs. exact Hlc.
    + right. intro H. apply Hnlc. exact (value_abs_lc T t1 H).
  - left. apply v_true.
  - left. apply v_false.
Qed.

(** Case analysis for a step from an application. *)

Lemma step_app_cases : forall t1 t2 t' (P : Prop),
  tm_app t1 t2 --> t' ->
  (forall T body v, t1 = tm_abs T body -> t2 = v -> t' = open body v ->
     locally_closed (tm_abs T body) -> value v -> P) ->
  (forall t1', t1 --> t1' -> t' = tm_app t1' t2 -> locally_closed t2 -> P) ->
  (forall t2', value t1 -> t2 --> t2' -> t' = tm_app t1 t2' -> P) ->
  P.
Proof.
  intros t1 t2 t' P H H1 H2 H3.
  inversion H; subst; eauto.
Qed.

(** Update lemmas for the typing context. *)

Lemma update_eq : forall Gamma x T, update Gamma x T x = Some T.
Proof.
  intros. unfold update. simpl. rewrite Nat.eqb_refl. reflexivity.
Qed.

(** The logical relation.  At base type it is strong normalization; at
    function type it requires strong normalization and that application
    to every related argument is again related. *)

Fixpoint R (T : ty) (t : tm) : Prop :=
  match T with
  | Ty_Bool => strongly_normalizing t
  | Ty_Arrow T1 T2 =>
      strongly_normalizing t /\
      (forall v, value v -> R T1 v -> R T2 (tm_app t v))
  end.

Lemma R_SN : forall T t, R T t -> strongly_normalizing t.
Proof.
  induction T as [| T1 IH1 T2 IH2]; simpl; intros t H.
  - exact H.
  - destruct H as [HSN _]. exact HSN.
Qed.

(** Relatedness is preserved by a forward step. *)

Lemma R_step_fwd : forall T t t', R T t -> t --> t' -> R T t'.
Proof.
  induction T as [| T1 IH1 T2 IH2]; simpl; intros t t' HR Hstep.
  - apply SN_step with (t := t); assumption.
  - destruct HR as [HSN Happ]. split.
    + apply SN_step with (t := t); assumption.
    + intros v Hv HRv.
      apply IH2 with (t := tm_app t v).
      * apply Happ; assumption.
      * apply ST_App1; [exact Hstep | apply value_lc; exact Hv].
Qed.

(** A strongly normalizing, non-value term all of whose reducts are
    related is itself related. *)

Lemma R_of_neutral : forall T s,
  strongly_normalizing s ->
  ~ value s ->
  (forall s', s --> s' -> R T s') ->
  R T s.
Proof.
  induction T as [| T1 IH1 T2 IH2]; simpl; intros s HSN Hnv Hred.
  - exact HSN.
  - split.
    + exact HSN.
    + intros w Hwv HRw.
      apply IH2.
      * apply SN_intro. intros s' Hstep.
        refine (step_app_cases s w s' (strongly_normalizing s') Hstep _ _ _).
        -- intros T0 body v Hs Hw Hs' Hlc Hv. subst.
           exfalso. apply Hnv. apply v_abs. exact Hlc.
        -- intros s1' Hs1 Hs' Hlcw. subst s'.
           apply R_SN with (T := T2).
           destruct (Hred s1' Hs1) as [HSN1 Happ1]. apply Happ1; assumption.
        -- intros w' Hsv Hw' Hs'. subst. exfalso. apply Hnv. exact Hsv.
      * apply app_not_value.
      * intros s' Hstep.
        refine (step_app_cases s w s' (R T2 s') Hstep _ _ _).
        -- intros T0 body v Hs Hw Hs' Hlc Hv. subst.
           exfalso. apply Hnv. apply v_abs. exact Hlc.
        -- intros s1' Hs1 Hs' Hlcw. subst s'.
           destruct (Hred s1' Hs1) as [HSN1 Happ1]. apply Happ1; assumption.
        -- intros w' Hsv Hw' Hs'. subst. exfalso. apply Hnv. exact Hsv.
Qed.

(** An abstraction applied to a related argument is related. *)

Lemma R_abs_app : forall T1 T2 body u,
  (forall v, value v -> R T1 v -> R T2 (open body v)) ->
  R T1 u ->
  R T2 (tm_app (tm_abs T1 body) u).
Proof.
  intros T1 T2 body u Hbody Hu.
  assert (HSN : strongly_normalizing u) by (apply R_SN with (T := T1); exact Hu).
  revert Hu. induction HSN as [u Hsteps IH]; intros Hu.
  destruct (value_dec u) as [Hv | Hnv].
  - (* u is a value: beta reduction gives the body applied to u *)
    apply R_of_neutral with (s := tm_app (tm_abs T1 body) u).
    + apply SN_intro. intros s' Hstep.
      refine (step_app_cases (tm_abs T1 body) u s' (strongly_normalizing s') Hstep _ _ _).
      * intros T0 b v Hs Hw Hs' Hlc Hvv.
        injection Hs as HT Hb. subst T0. subst b. subst v. subst s'.
        apply R_SN with (T := T2). apply Hbody; [exact Hvv | exact Hu].
      * intros s1' Hs1 Hs' Hlcw. exfalso. apply (abs_no_step T1 body s1'). exact Hs1.
      * intros w' Hval Hw' Hs'. exfalso. apply (value_no_step u Hv w'). exact Hw'.
    + apply app_not_value.
    + intros s' Hstep.
      refine (step_app_cases (tm_abs T1 body) u s' (R T2 s') Hstep _ _ _).
      * intros T0 b v Hs Hw Hs' Hlc Hvv.
        injection Hs as HT Hb. subst T0. subst b. subst v. subst s'.
        apply Hbody; [exact Hvv | exact Hu].
      * intros s1' Hs1 Hs' Hlcw. exfalso. apply (abs_no_step T1 body s1'). exact Hs1.
      * intros w' Hval Hw' Hs'. exfalso. apply (value_no_step u Hv w'). exact Hw'.
  - (* u is not a value: proceed by the induction hypothesis on its reducts *)
    apply R_of_neutral with (s := tm_app (tm_abs T1 body) u).
    + apply SN_intro. intros s' Hstep.
      refine (step_app_cases (tm_abs T1 body) u s' (strongly_normalizing s') Hstep _ _ _).
      * intros T0 b v Hs Hw Hs' Hlc Hvv.
        injection Hs as HT Hb. subst T0. subst b. subst v.
        exfalso. apply Hnv. exact Hvv.
      * intros s1' Hs1 Hs' Hlcw. exfalso. apply (abs_no_step T1 body s1'). exact Hs1.
      * intros u' Hval Hu' Hs'. subst s'.
        apply R_SN with (T := T2).
        apply IH; [exact Hu' | apply R_step_fwd with (t := u); assumption].
    + apply app_not_value.
    + intros s' Hstep.
      refine (step_app_cases (tm_abs T1 body) u s' (R T2 s') Hstep _ _ _).
      * intros T0 b v Hs Hw Hs' Hlc Hvv.
        injection Hs as HT Hb. subst T0. subst b. subst v.
        exfalso. apply Hnv. exact Hvv.
      * intros s1' Hs1 Hs' Hlcw. exfalso. apply (abs_no_step T1 body s1'). exact Hs1.
      * intros u' Hval Hu' Hs'. subst s'.
        apply IH; [exact Hu' | apply R_step_fwd with (t := u); assumption].
Qed.

(** A related value of function type applied to a related argument. *)

Lemma R_app_value : forall A B v t2,
  value v ->
  R (Ty_Arrow A B) v ->
  R A t2 ->
  R B (tm_app v t2).
Proof.
  intros A B v t2 Hv HRv Ht2.
  assert (HSN : strongly_normalizing t2) by (apply R_SN with (T := A); exact Ht2).
  revert Ht2. induction HSN as [t2 Hsteps IH]; intros Ht2.
  destruct (value_dec t2) as [Hv2 | Hnv2].
  - destruct HRv as [HSNv Happ]. apply Happ; assumption.
  - apply R_of_neutral with (s := tm_app v t2).
    + apply SN_intro. intros s' Hstep.
      refine (step_app_cases v t2 s' (strongly_normalizing s') Hstep _ _ _).
      * intros T0 body v0 Hs Hw Hs' Hlc Hvv. subst v.
        exfalso. apply Hnv2. rewrite Hw. exact Hvv.
      * intros s1' Hs1 Hs' Hlcw. exfalso. apply (value_no_step v Hv s1'). exact Hs1.
      * intros t2' Hval Ht2' Hs'. subst s'.
        apply R_SN with (T := B).
        apply IH; [exact Ht2' | apply R_step_fwd with (t := t2); assumption].
    + apply app_not_value.
    + intros s' Hstep.
      refine (step_app_cases v t2 s' (R B s') Hstep _ _ _).
      * intros T0 body v0 Hs Hw Hs' Hlc Hvv. subst v.
        exfalso. apply Hnv2. rewrite Hw. exact Hvv.
      * intros s1' Hs1 Hs' Hlcw. exfalso. apply (value_no_step v Hv s1'). exact Hs1.
      * intros t2' Hval Ht2' Hs'. subst s'.
        apply IH; [exact Ht2' | apply R_step_fwd with (t := t2); assumption].
Qed.

(** Application of two related terms. *)

Lemma R_app : forall A B t1 t2,
  R (Ty_Arrow A B) t1 ->
  R A t2 ->
  R B (tm_app t1 t2).
Proof.
  intros A B t1 t2 H1 H2.
  assert (HSN : strongly_normalizing t1)
    by (apply R_SN with (T := Ty_Arrow A B); exact H1).
  revert H1 H2. induction HSN as [t1 Hsteps IH]; intros H1 H2.
  destruct (value_dec t1) as [Hv1 | Hnv1].
  - apply R_app_value with (A := A) (B := B); assumption.
  - apply R_of_neutral with (s := tm_app t1 t2).
    + apply SN_intro. intros s' Hstep.
      refine (step_app_cases t1 t2 s' (strongly_normalizing s') Hstep _ _ _).
      * intros T0 body v Hs Hw Hs' Hlc Hvv. subst t1.
        exfalso. apply Hnv1. apply v_abs. exact Hlc.
      * intros t1' Hs1 Hs' Hlcw. subst s'.
        apply R_SN with (T := B).
        apply IH; [exact Hs1 | apply R_step_fwd with (t := t1); assumption | exact H2].
      * intros t2' Hval Ht2' Hs'. exfalso. apply Hnv1. exact Hval.
    + apply app_not_value.
    + intros s' Hstep.
      refine (step_app_cases t1 t2 s' (R B s') Hstep _ _ _).
      * intros T0 body v Hs Hw Hs' Hlc Hvv. subst t1.
        exfalso. apply Hnv1. apply v_abs. exact Hlc.
      * intros t1' Hs1 Hs' Hlcw. subst s'.
        apply IH; [exact Hs1 | apply R_step_fwd with (t := t1); assumption | exact H2].
      * intros t2' Hval Ht2' Hs'. exfalso. apply Hnv1. exact Hval.
Qed.

(** The term-variable context interpretation. *)

Definition good (Gamma : context) (sigma : atom -> tm) : Prop :=
  (forall x, locally_closed (sigma x)) /\
  (forall x U, Gamma x = Some U -> R U (sigma x)).

(** Fundamental theorem: every well-typed term, under any related
    substitution, belongs to the logical relation at its type. *)

Lemma fundamental : forall Gamma t T,
  has_type Gamma t T ->
  forall sigma, good Gamma sigma -> R T (subst_fvar sigma t).
Proof.
  intros Gamma t T H.
  induction H as [Gamma0 x T0 Hlookup
                 | L Gamma0 T1 T2 t1 Hty IH
                 | Gamma0 t1 t2 T1 T2 H1 IH1 H2 IH2
                 | Gamma0 | Gamma0];
    intros sigma Hgood.
  - (* T_Var *)
    simpl. destruct Hgood as [_ Hrel_sigma]. apply Hrel_sigma. exact Hlookup.
  - (* T_Abs *)
    destruct Hgood as [Hlc_sigma Hrel_sigma].
    simpl. split.
    + apply SN_abs.
    + intros v Hvval HvR.
      apply R_abs_app with (body := subst_fvar sigma t1).
      * intros w Hwval HwR.
        destruct (fresh_pair L (fv t1)) as [x0 [Hx0L Hx0fv]].
        set (sigma' := fun y => if Nat.eqb x0 y then w else sigma y).
        assert (Hx0w : sigma' x0 = w).
        { unfold sigma'. rewrite Nat.eqb_refl. reflexivity. }
        assert (Hgood' : good (update Gamma0 x0 T1) sigma').
        { split.
          - intros y. unfold sigma'. destruct (Nat.eqb x0 y) eqn:E.
            + apply value_lc. exact Hwval.
            + apply Hlc_sigma.
          - intros y U Hy. unfold sigma'.
            destruct (Nat.eqb x0 y) eqn:E.
            + apply Nat.eqb_eq in E. subst y.
              rewrite update_eq in Hy. injection Hy as HU. subst U.
              exact HwR.
            + unfold update in Hy. rewrite E in Hy.
              apply Hrel_sigma. exact Hy. }
        specialize (IH x0 Hx0L sigma' Hgood').
        rewrite (subst_fvar_open sigma' t1 (tm_fvar x0) (proj1 Hgood')) in IH.
        simpl in IH.
        rewrite Hx0w in IH.
        assert (Hagree : subst_fvar sigma' t1 = subst_fvar sigma t1).
        { unfold sigma'. apply subst_fvar_agree. intros x Hx.
          destruct (Nat.eqb x0 x) eqn:E.
          - apply Nat.eqb_eq in E. subst x. exfalso. apply Hx0fv. exact Hx.
          - reflexivity. }
        rewrite Hagree in IH.
        exact IH.
      * exact HvR.
  - (* T_App *)
    simpl. apply R_app with (A := T1).
    + apply IH1. exact Hgood.
    + apply IH2. exact Hgood.
  - (* T_True *)
    simpl. apply SN_true.
  - (* T_False *)
    simpl. apply SN_false.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T H.
  assert (Hgood : good empty (fun x => tm_fvar x)).
  { split.
    - intros x. apply lc_fvar.
    - intros x U Hx. unfold empty in Hx. discriminate Hx. }
  pose proof (fundamental empty t T H (fun x => tm_fvar x) Hgood) as HR.
  rewrite subst_fvar_id in HR.
  apply R_SN with (T := T). exact HR.
Qed.

End STLCNormalizationNoneHardTask.
