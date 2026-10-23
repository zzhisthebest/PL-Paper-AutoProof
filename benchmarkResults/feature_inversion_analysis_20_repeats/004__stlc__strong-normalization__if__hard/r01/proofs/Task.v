(** STLC call-by-value strong-normalization benchmark task. *)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Relations.Relation_Definitions.

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

(* ================================================================ *)
(* Auxiliary development for the strong normalization proof.        *)
(* ================================================================ *)

(** ** Free variables of a term *)

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

(** ** A fresh atom for any finite list of atoms *)

Fixpoint max_list (L : list nat) : nat :=
  match L with
  | nil => 0
  | x :: xs => Nat.max x (max_list xs)
  end.

Lemma max_list_spec : forall L x, In x L -> x <= max_list L.
Proof.
  induction L as [| y ys IH]; intros x Hin; simpl in *.
  - contradiction.
  - destruct Hin as [-> | Hin].
    + apply Nat.le_max_l.
    + apply Nat.le_trans with (max_list ys).
      * apply IH; assumption.
      * apply Nat.le_max_r.
Qed.

Lemma fresh_atom : forall L : list atom, exists x, ~ In x L.
Proof.
  intros L. exists (S (max_list L)). intro Hin.
  pose proof (max_list_spec L (S (max_list L)) Hin) as H.
  apply Nat.nle_succ_diag_l in H. exact H.
Qed.

(** ** Substitution of free variables *)

Definition extend (rho : atom -> tm) (x : atom) (w : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then w else rho y.

Fixpoint subst_f (rho : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => rho x
  | tm_app t1 t2 => tm_app (subst_f rho t1) (subst_f rho t2)
  | tm_abs T t1 => tm_abs T (subst_f rho t1)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 =>
      tm_if (subst_f rho t1) (subst_f rho t2) (subst_f rho t3)
  end.

Lemma subst_f_id : forall t, subst_f (fun x => tm_fvar x) t = t.
Proof. induction t; simpl; congruence. Qed.

(** ** Local closure and opening *)

Lemma lc_at_mono : forall t i j, lc_at i t -> i <= j -> lc_at j t.
Proof.
  induction t; intros i j Hlc Hle; inversion Hlc; subst;
    auto using lc_fvar, lc_true, lc_false.
  - apply lc_bvar. eapply Nat.lt_le_trans; eassumption.
  - apply lc_app.
    + apply IHt1 with (i := i); assumption.
    + apply IHt2 with (i := i); assumption.
  - apply lc_abs. apply IHt with (i := S i).
    + assumption.
    + apply le_n_S. assumption.
  - apply lc_if.
    + apply IHt1 with (i := i); assumption.
    + apply IHt2 with (i := i); assumption.
    + apply IHt3 with (i := i); assumption.
Qed.

Lemma lc_at_any : forall t n, locally_closed t -> lc_at n t.
Proof.
  intros t n H. apply lc_at_mono with (i := 0); [assumption | apply Nat.le_0_l].
Qed.

Lemma open_rec_lc : forall t k v, lc_at k t -> open_rec k v t = t.
Proof.
  induction t; intros k v Hlc; simpl; auto.
  - destruct (Nat.eqb k n) eqn:E; auto.
    apply Nat.eqb_eq in E. subst n.
    inversion Hlc; subst. exfalso. eapply Nat.lt_irrefl. eassumption.
  - inversion Hlc; subst. rewrite IHt1, IHt2; auto.
  - f_equal. apply IHt. inversion Hlc; assumption.
  - inversion Hlc; subst. rewrite IHt1, IHt2, IHt3; auto.
Qed.

(** ** Basic properties of values and reduction *)

Lemma value_no_step : forall v t, value v -> ~ step v t.
Proof.
  intros v t Hv. induction Hv; intro Hstep; inversion Hstep.
Qed.

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v Hv. destruct Hv.
  - assumption.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma sn_value : forall v, value v -> strongly_normalizing v.
Proof.
  intros v Hv. constructor. intros t' Hstep.
  exfalso. eapply value_no_step; eassumption.
Qed.

Lemma sn_abs : forall T t, strongly_normalizing (tm_abs T t).
Proof. intros T t. constructor. intros t' Hstep. inversion Hstep. Qed.

Lemma sn_step : forall t t', strongly_normalizing t -> t --> t' ->
                 strongly_normalizing t'.
Proof.
  intros t t' Hsn Hstep. destruct Hsn as [t0 Hfun].
  apply Hfun. exact Hstep.
Qed.

Lemma value_multi_eq : forall v u, multi step v u -> value v -> u = v.
Proof.
  intros v u Hm. induction Hm as [x | x y z Hstep Hrest IH]; intro Hv.
  - reflexivity.
  - exfalso. eapply value_no_step; eassumption.
Qed.

Lemma abs_multi_eq : forall v u, multi step v u ->
                     (exists T t, v = tm_abs T t) -> u = v.
Proof.
  intros v u Hm. induction Hm as [x | x y z Hstep Hrest IH];
    intros [T [t Heq]].
  - reflexivity.
  - subst x. inversion Hstep.
Qed.

(** ** The logical relation *)

(** [V T t] is the value interpretation: it holds of values of type [T].
    [E T t] is the expression interpretation: [t] is strongly normalizing
    and every value it reduces to lies in [V T]. *)

Fixpoint V (T : ty) (t : tm) : Prop :=
  match T with
  | Ty_Bool => value t
  | Ty_Arrow T1 T2 =>
      locally_closed t /\
      (exists T' t1, t = tm_abs T' t1 /\
        (forall w, V T1 w ->
           strongly_normalizing (open t1 w) /\
           (forall u, multi step (open t1 w) u -> value u -> V T2 u)))
  end.

Definition E (T : ty) (t : tm) : Prop :=
  strongly_normalizing t /\
  (forall u, multi step t u -> value u -> V T u).

Lemma V_lc : forall T t, V T t -> locally_closed t.
Proof.
  intros T t. destruct T as [| T1 T2]; simpl.
  - intros H. apply value_lc. exact H.
  - intros H. exact (proj1 H).
Qed.

Lemma V_E : forall T t, V T t -> E T t.
Proof.
  intros T t HV. destruct T as [| T1 T2]; simpl in *.
  - split.
    + apply sn_value. exact HV.
    + intros u Hm Hvalu. exact Hvalu.
  - split.
    + destruct HV as [Hlc [T' [t1 [Heq _]]]].
      subst t. apply sn_abs.
    + intros u Hm Hvalu.
      assert (u = t) as ->.
      { destruct HV as [Hlc [T' [t1 [Heq _]]]].
        eapply abs_multi_eq.
        * exact Hm.
        * exists T'. exists t1. exact Heq. }
      exact HV.
Qed.

Lemma V_abs_beta : forall T1 T2 T' t1 w,
  V (Ty_Arrow T1 T2) (tm_abs T' t1) -> V T1 w -> E T2 (open t1 w).
Proof.
  intros T1 T2 T' t1 w HV HVw. simpl in HV.
  destruct HV as [_ [T'' [t'' [Heq Hbody]]]].
  inversion Heq; subst.
  apply Hbody. exact HVw.
Qed.

Lemma E_sn : forall T t, E T t -> strongly_normalizing t.
Proof. intros T t [H _]. exact H. Qed.

Lemma E_value_V : forall T t u, E T t -> multi step t u -> value u -> V T u.
Proof. intros T t u [_ H] Hm Hv. apply H; assumption. Qed.

Lemma E_step_fwd : forall T t t', E T t -> t --> t' -> E T t'.
Proof.
  intros T t t' [Hsn Hvr] Hstep. split.
  - eapply sn_step; eassumption.
  - intros u Hm Hval. apply Hvr.
    + eapply multi_step. exact Hstep. exact Hm.
    + exact Hval.
Qed.

Lemma E_multi_V : forall T (x z : tm), multi step x z -> E T x -> value z -> V T z.
Proof.
  intros T x z Hm. induction Hm as [x0 | x0 y z0 Hstep Hrest IH];
    intros HE Hval.
  - apply (proj2 HE). apply multi_refl. exact Hval.
  - apply IH.
    + eapply E_step_fwd; eassumption.
    + exact Hval.
Qed.

(** Closure of [E] under "all one-step reducts are in [E]" *)

Lemma E_intro : forall T t,
  strongly_normalizing t ->
  (value t -> V T t) ->
  (forall t', t --> t' -> E T t') ->
  E T t.
Proof.
  intros T t Hsn Hv Hs. split; [exact Hsn |].
  intros u Hm Hval.
  destruct Hm as [| t0 y u0 Hstep Hrest].
  - apply Hv. exact Hval.
  - eapply E_multi_V.
    + exact Hrest.
    + apply Hs. exact Hstep.
    + exact Hval.
Qed.

(** ** The application lemma *)

Lemma sn_app_value : forall T1 T2 (v1 : tm),
  value v1 -> V (Ty_Arrow T1 T2) v1 ->
  forall t2, E T1 t2 -> strongly_normalizing (tm_app v1 t2).
Proof.
  intros T1 T2 v1 Hval HV.
  enough (Hgen : forall t2, strongly_normalizing t2 ->
            E T1 t2 -> strongly_normalizing (tm_app v1 t2)).
  { intros t2 HE2. apply Hgen; [exact (proj1 HE2) | exact HE2]. }
  intros t2 Hsn2.
  induction Hsn2 as [t2 Hfun IH].
  intros HE2.
  constructor. intros u Hstep. inversion Hstep; subst.
  - (* ST_AppAbs *)
    eapply E_sn. eapply V_abs_beta.
    + exact HV.
    + apply (proj2 HE2). apply multi_refl. eassumption.
  - (* ST_App1 : impossible, v1 is a value *)
    exfalso. eapply value_no_step; eassumption.
  - (* ST_App2 *)
    apply IH.
    + eassumption.
    + eapply E_step_fwd; eassumption.
Qed.

Lemma E_app_value : forall T1 T2 (v1 : tm),
  value v1 -> V (Ty_Arrow T1 T2) v1 ->
  forall t2, E T1 t2 -> E T2 (tm_app v1 t2).
Proof.
  intros T1 T2 v1 Hval HV.
  enough (Hgen : forall t2, strongly_normalizing t2 ->
            E T1 t2 -> E T2 (tm_app v1 t2)).
  { intros t2 HE2. apply Hgen; [exact (proj1 HE2) | exact HE2]. }
  intros t2 Hsn2.
  induction Hsn2 as [t2 Hfun IH].
  intros HE2.
  apply E_intro.
  - apply sn_app_value with (T1 := T1) (T2 := T2); assumption.
  - intros Hv. inversion Hv.
  - intros u Hstep. inversion Hstep; subst.
    + (* ST_AppAbs *)
      eapply V_abs_beta.
      * exact HV.
      * apply (proj2 HE2). apply multi_refl. eassumption.
    + (* ST_App1 : impossible *)
      exfalso. eapply value_no_step; eassumption.
    + (* ST_App2 *)
      apply IH.
      * eassumption.
      * eapply E_step_fwd; eassumption.
Qed.

Lemma sn_app : forall T1 T2 t1 t2,
  E (Ty_Arrow T1 T2) t1 -> E T1 t2 -> strongly_normalizing (tm_app t1 t2).
Proof.
  intros T1 T2 t1 t2 HE1 HE2.
  enough (Hgen : forall t1, strongly_normalizing t1 ->
            E (Ty_Arrow T1 T2) t1 ->
            forall t2, E T1 t2 -> strongly_normalizing (tm_app t1 t2)).
  { apply Hgen; [exact (proj1 HE1) | exact HE1 | exact HE2]. }
  clear t1 t2 HE1 HE2.
  intros t1 Hsn1.
  induction Hsn1 as [t1 Hfun IH].
  intros HE1 t2 HE2.
  constructor. intros u Hstep. inversion Hstep; subst.
  - (* ST_AppAbs *)
    eapply E_sn. eapply V_abs_beta.
    + apply (proj2 HE1). apply multi_refl. apply v_abs. eassumption.
    + apply (proj2 HE2). apply multi_refl. eassumption.
  - (* ST_App1 *)
    apply IH.
    + eassumption.
    + eapply E_step_fwd; eassumption.
    + exact HE2.
  - (* ST_App2 *)
    eapply sn_app_value.
    + eassumption.
    + apply (proj2 HE1). apply multi_refl. eassumption.
    + eapply E_step_fwd; eassumption.
Qed.

Lemma E_app : forall T1 T2 t1 t2,
  E (Ty_Arrow T1 T2) t1 -> E T1 t2 -> E T2 (tm_app t1 t2).
Proof.
  intros T1 T2 t1 t2 HE1 HE2.
  enough (Hgen : forall t1, strongly_normalizing t1 ->
            E (Ty_Arrow T1 T2) t1 ->
            forall t2, E T1 t2 -> E T2 (tm_app t1 t2)).
  { apply Hgen; [exact (proj1 HE1) | exact HE1 | exact HE2]. }
  clear t1 t2 HE1 HE2.
  intros t1 Hsn1.
  induction Hsn1 as [t1 Hfun IH].
  intros HE1 t2 HE2.
  apply E_intro.
  - eapply sn_app; [exact HE1 | exact HE2].
  - intros Hv. inversion Hv.
  - intros u Hstep. inversion Hstep; subst.
    + (* ST_AppAbs *)
      eapply V_abs_beta.
      * apply (proj2 HE1). apply multi_refl. apply v_abs. eassumption.
      * apply (proj2 HE2). apply multi_refl. eassumption.
    + (* ST_App1 *)
      apply IH.
      * eassumption.
      * eapply E_step_fwd; eassumption.
      * exact HE2.
    + (* ST_App2 *)
      eapply E_app_value.
      * eassumption.
      * apply (proj2 HE1). apply multi_refl. eassumption.
      * eapply E_step_fwd; eassumption.
Qed.

(** ** The conditional lemma *)

Lemma sn_if : forall t1 t2 t3,
  strongly_normalizing t1 -> strongly_normalizing t2 ->
  strongly_normalizing t3 -> strongly_normalizing (tm_if t1 t2 t3).
Proof.
  intros t1 t2 t3 H1 H2 H3.
  enough (Hgen : forall t1, strongly_normalizing t1 ->
            forall t2 t3, strongly_normalizing t2 -> strongly_normalizing t3 ->
              strongly_normalizing (tm_if t1 t2 t3)).
  { apply Hgen; assumption. }
  clear t1 t2 t3 H1 H2 H3.
  intros t1 Hsn1.
  induction Hsn1 as [t1 Hfun IH].
  intros t2 t3 Hsn2 Hsn3.
  constructor. intros u Hstep. inversion Hstep; subst.
  - exact Hsn2.
  - exact Hsn3.
  - apply IH.
    + eassumption.
    + exact Hsn2.
    + exact Hsn3.
Qed.

Lemma E_if : forall T t1 t2 t3,
  E Ty_Bool t1 -> E T t2 -> E T t3 -> E T (tm_if t1 t2 t3).
Proof.
  intros T t1 t2 t3 HE1 HE2 HE3.
  enough (Hgen : forall t1, strongly_normalizing t1 -> E Ty_Bool t1 ->
            forall t2 t3, E T t2 -> E T t3 -> E T (tm_if t1 t2 t3)).
  { apply Hgen; [exact (proj1 HE1) | exact HE1 | exact HE2 | exact HE3]. }
  clear t1 t2 t3 HE1 HE2 HE3.
  intros t1 Hsn1.
  induction Hsn1 as [t1 Hfun IH].
  intros HE1 t2 t3 HE2 HE3.
  apply E_intro.
  - apply sn_if.
    + exact (proj1 HE1).
    + exact (proj1 HE2).
    + exact (proj1 HE3).
  - intros Hv. inversion Hv.
  - intros u Hstep. inversion Hstep; subst.
    + exact HE2.
    + exact HE3.
    + apply IH.
      * eassumption.
      * eapply E_step_fwd; eassumption.
      * exact HE2.
      * exact HE3.
Qed.

(** ** Basic facts about context update *)

Lemma update_eq : forall Gamma x T, update Gamma x T x = Some T.
Proof.
  intros Gamma x T. unfold update. simpl.
  rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma update_neq : forall Gamma x y T, x <> y -> update Gamma x T y = Gamma y.
Proof.
  intros Gamma x y T Hneq. unfold update. simpl.
  destruct (Nat.eqb x y) eqn:E; auto.
  exfalso. apply Hneq. apply Nat.eqb_eq. exact E.
Qed.

(** ** Semantic environments *)

Definition sem_env (Gamma : context) (rho : atom -> tm) : Prop :=
  (forall x, locally_closed (rho x)) /\
  (forall x T, Gamma x = Some T -> E T (rho x)).

Lemma not_in_app_l : forall (x : atom) l1 l2, ~ In x (l1 ++ l2) -> ~ In x l1.
Proof.
  intros x l1 l2 H Hin. apply H. apply in_app_iff. left. exact Hin.
Qed.

Lemma not_in_app_r : forall (x : atom) l1 l2, ~ In x (l1 ++ l2) -> ~ In x l2.
Proof.
  intros x l1 l2 H Hin. apply H. apply in_app_iff. right. exact Hin.
Qed.

(** ** Commutation of opening and free-variable substitution *)

Lemma subst_open_comm : forall rho x w t k,
  (forall y, locally_closed (rho y)) ->
  locally_closed w ->
  ~ In x (fvs t) ->
  subst_f (extend rho x w) (open_rec k (tm_fvar x) t) =
  open_rec k w (subst_f rho t).
Proof.
  intros rho x w t. induction t; intros k Hlc Hw Hfresh; simpl in *.
  - (* tm_bvar *)
    destruct (Nat.eqb k n) eqn:E; simpl.
    + apply Nat.eqb_eq in E. subst n.
      unfold extend. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - (* tm_fvar *)
    unfold extend. simpl.
    destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E. subst a. exfalso. apply Hfresh.
      simpl. left. reflexivity.
    + apply Nat.eqb_neq in E.
      symmetry. apply open_rec_lc. apply lc_at_any. apply Hlc.
  - (* tm_app *)
    assert (Hf1 : ~ In x (fvs t1)).
    { apply not_in_app_l with (l2 := fvs t2). exact Hfresh. }
    assert (Hf2 : ~ In x (fvs t2)).
    { apply not_in_app_r with (l1 := fvs t1). exact Hfresh. }
    rewrite (IHt1 k Hlc Hw Hf1).
    rewrite (IHt2 k Hlc Hw Hf2).
    reflexivity.
  - (* tm_abs *)
    simpl. f_equal. apply IHt; auto.
  - (* tm_true *)
    reflexivity.
  - (* tm_false *)
    reflexivity.
  - (* tm_if *)
    assert (Hf1 : ~ In x (fvs t1)).
    { apply not_in_app_l with (l2 := fvs t2 ++ fvs t3). exact Hfresh. }
    assert (Hf2 : ~ In x (fvs t2)).
    { apply not_in_app_l with (l2 := fvs t3).
      apply not_in_app_r with (l1 := fvs t1). exact Hfresh. }
    assert (Hf3 : ~ In x (fvs t3)).
    { apply not_in_app_r with (l1 := fvs t2).
      apply not_in_app_r with (l1 := fvs t1). exact Hfresh. }
    rewrite (IHt1 k Hlc Hw Hf1).
    rewrite (IHt2 k Hlc Hw Hf2).
    rewrite (IHt3 k Hlc Hw Hf3).
    reflexivity.
Qed.

(** ** The fundamental theorem *)

Lemma fundamental : forall Gamma t T,
  <{ Gamma |-- t \in T }> ->
  forall rho, sem_env Gamma rho -> E T (subst_f rho t).
Proof.
  intros Gamma t T Hty.
  induction Hty as
    [ Gamma x T Hx
    | L Gamma T1 T2 t1 Hty IH
    | Gamma t1 t2 T1 T2 Hty1 IH1 Hty2 IH2
    | Gamma
    | Gamma
    | Gamma t1 t2 t3 T Hty1 IH1 Hty2 IH2 Hty3 IH3 ];
    intros rho Hsem.
  - (* T_Var *)
    simpl. apply (proj2 Hsem). exact Hx.
  - (* T_Abs *)
    simpl. split.
    + apply sn_abs.
    + intros u Hm Hvalu.
      assert (Heq : u = tm_abs T1 (subst_f rho t1)).
      { eapply abs_multi_eq.
        - exact Hm.
        - exists T1. exists (subst_f rho t1). reflexivity. }
      subst u.
      split.
      * apply value_lc in Hvalu. exact Hvalu.
      * exists T1. exists (subst_f rho t1). split.
        { reflexivity. }
        intros w HVw.
        (* choose a fresh atom avoiding L and the free variables of t1 *)
        destruct (fresh_atom (L ++ fvs t1)) as [x Hx].
        assert (HxL : ~ In x L).
        { intro Hin. apply Hx. apply in_app_iff. left. exact Hin. }
        assert (Hxfvs : ~ In x (fvs t1)).
        { intro Hin. apply Hx. apply in_app_iff. right. exact Hin. }
        assert (Hsem' : sem_env (update Gamma x T1) (extend rho x w)).
        { split.
          - (* locality of the extended environment *)
            intro y. unfold extend.
            destruct (Nat.eqb x y) eqn:E.
            + apply V_lc in HVw. exact HVw.
            + apply (proj1 Hsem).
          - (* typing of the extended environment *)
            intros y S Hy. unfold extend. simpl.
            destruct (Nat.eqb x y) eqn:E.
            + apply Nat.eqb_eq in E. subst y.
              rewrite update_eq in Hy.
              inversion Hy; subst.
              apply V_E. exact HVw.
            + apply Nat.eqb_neq in E.
              rewrite (update_neq Gamma x y T1 E) in Hy.
              apply (proj2 Hsem). exact Hy. }
        pose proof (IH x HxL (extend rho x w) Hsem') as HE.
        assert (Hcomm :
          subst_f (extend rho x w) (open t1 (tm_fvar x)) =
          open (subst_f rho t1) w).
        { change (subst_f (extend rho x w) (open_rec 0 (tm_fvar x) t1) =
                  open_rec 0 w (subst_f rho t1)).
          apply subst_open_comm.
          - apply (proj1 Hsem).
          - apply V_lc in HVw. exact HVw.
          - exact Hxfvs. }
        rewrite Hcomm in HE.
        exact HE.
  - (* T_App *)
    simpl. eapply E_app.
    + apply IH1. exact Hsem.
    + apply IH2. exact Hsem.
  - (* T_True *)
    simpl. apply V_E. simpl. apply v_true.
  - (* T_False *)
    simpl. apply V_E. simpl. apply v_false.
  - (* T_If *)
    simpl. eapply E_if.
    + apply IH1. exact Hsem.
    + apply IH2. exact Hsem.
    + apply IH3. exact Hsem.
Qed.

(** Target theorem: strong normalization for the supplied CBV relation. *)

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  pose proof (fundamental empty t T Hty (fun x => tm_fvar x)) as HE.
  assert (Henv : sem_env empty (fun x => tm_fvar x)).
  { split.
    - intro x. apply lc_fvar.
    - intros x S Hx. unfold empty in Hx. discriminate. }
  specialize (HE Henv).
  rewrite subst_f_id in HE.
  apply E_sn in HE. exact HE.
Qed.

End STLCCBVNormalizationTask.
