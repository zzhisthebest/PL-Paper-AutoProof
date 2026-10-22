(** STLC call-by-value strong-normalization benchmark.
    No if-then-else, non-determinism, or recursion is included. *)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Relations.Relation_Definitions.

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

Fixpoint lc_at_dec (k : nat) (t : tm) {struct t} :
  {lc_at k t} + {~ lc_at k t}.
Proof.
  destruct t.
  - destruct (Nat.ltb n k) eqn:E.
    + left; constructor; apply Nat.ltb_lt; exact E.
    + right; intro H; inversion H; subst; apply Nat.ltb_ge in E; lia.
  - left; constructor.
  - destruct (lc_at_dec k t1), (lc_at_dec k t2).
    + left; econstructor; eassumption.
    + right; intro H; inversion H; contradiction.
    + right; intro H; inversion H; contradiction.
    + right; intro H; inversion H; contradiction.
  - destruct (lc_at_dec (S k) t0).
    + left; constructor; assumption.
    + right; intro H; inversion H; contradiction.
  - left; constructor.
  - left; constructor.
Defined.

(** Call-by-value operational semantics. *)

Inductive value : tm -> Prop :=
  | v_abs : forall T t,
      locally_closed (tm_abs T t) ->
      value (tm_abs T t)
  | v_true :
      value tm_true
  | v_false :
      value tm_false.

Definition value_dec (v : tm) : {value v} + {~ value v}.
Proof.
  destruct v.
  - right; intro H; inversion H.
  - right; intro H; inversion H.
  - right; intro H; inversion H.
  - destruct (lc_at_dec 1 v) as [Hlc|Hnot].
    + left; apply v_abs; constructor; exact Hlc.
    + right; intro H; inversion H; subst.
      inversion H1; apply Hnot; assumption.
  - left; constructor.
  - left; constructor.
Defined.

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

Fixpoint reducible (T : ty) (t : tm) : Prop :=
  strongly_normalizing t /\ locally_closed t /\
  match T with
  | Ty_Bool => True
  | Ty_Arrow A B => forall a, reducible A a ->
                     reducible B (tm_app t a)
  end.

Lemma value_lc : forall v, value v -> locally_closed v.
Proof. intros v H; inversion H; subst; try assumption; constructor. Qed.

Lemma value_no_step : forall v, value v -> forall u, ~ (v --> u).
Proof.
  intros v Hv; inversion Hv; subst; intros u Hs; inversion Hs; subst; try
  match goal with Hval : value _ |- _ => inversion Hval end.
Qed.

Fixpoint step_exists_dec (t : tm) {struct t} :
  (exists u, t --> u) \/ (forall u, ~ (t --> u)).
Proof.
  destruct t.
  - right; intros u H; inversion H.
  - right; intros u H; inversion H.
  - destruct (step_exists_dec t1) as [[t1' H1]|Hno1].
    + destruct (lc_at_dec 0 t2) as [Hlc2|Hnlc2].
      * left; exists (tm_app t1' t2); apply ST_App1; assumption.
      * right; intros u Hu; inversion Hu; subst.
        -- inversion H1.
        -- exfalso; apply Hnlc2; assumption.
        -- exfalso; match goal with
           | Hv : value ?v, Hs : ?v --> ?u |- _ => exact (value_no_step v Hv u Hs)
           end.
    + destruct (value_dec t1) as [Hv1|Hnv1].
      * destruct (step_exists_dec t2) as [[t2' H2]|Hno2].
        -- left; exists (tm_app t1 t2'); apply ST_App2; assumption.
        -- destruct t1.
           ++ inversion Hv1.
           ++ inversion Hv1.
           ++ inversion Hv1.
           ++ inversion Hv1; subst.
              destruct (value_dec t2) as [Hv2|Hnv2].
              ** left; exists (open t1 t2); apply ST_AppAbs; assumption.
              ** right; intros u Hu; inversion Hu; subst.
                 --- exfalso; apply Hnv2; assumption.
                 --- exfalso; eapply Hno1; eassumption.
                 --- exfalso; eapply Hno2; eassumption.
           ++ right; intros u Hu; inversion Hu; subst; try (eapply Hno1; eassumption); try (eapply Hno2; eassumption).
           ++ right; intros u Hu; inversion Hu; subst; try (eapply Hno1; eassumption); try (eapply Hno2; eassumption).
      * right; intros u Hu; inversion Hu; subst.
        -- exfalso; apply Hnv1; constructor; assumption.
        -- exfalso; eapply Hno1; eassumption.
        -- exfalso; apply Hnv1; assumption.
  - right; intros u H; inversion H.
  - right; intros u H; inversion H.
  - right; intros u H; inversion H.
Defined.

Lemma lc_mono : forall k t, lc_at k t -> forall j, k <= j -> lc_at j t.
Proof.
  intros k t H; induction H; intros j Hj.
  - constructor; lia.
  - constructor.
  - econstructor; eauto.
  - constructor; apply IHlc_at; lia.
  - constructor.
  - constructor.
Qed.

Lemma lc_open_rec : forall k t u,
  lc_at (S k) t -> locally_closed u -> lc_at k (open_rec k u t).
Proof.
  intros k0 t; revert k0; induction t; intros k0 u Ht Hu; simpl in *.
  - inversion Ht; subst. destruct (Nat.eqb k0 n) eqn:E.
    + apply Nat.eqb_eq in E; subst; apply lc_mono with (k:=0); [exact Hu|lia].
    + constructor; apply Nat.eqb_neq in E; lia.
  - inversion Ht; constructor.
  - inversion Ht; subst; econstructor; [eapply IHt1|eapply IHt2]; eassumption.
  - inversion Ht; subst; constructor; eapply IHt; eauto.
  - inversion Ht; constructor.
  - inversion Ht; constructor.
Qed.

Lemma lc_open_rec_inv : forall k t x,
  lc_at k (open_rec k (tm_fvar x) t) -> lc_at (S k) t.
Proof.
  intros k0 t; revert k0; induction t; intros k0 x H; simpl in *.
  - destruct (Nat.eqb k0 n) eqn:E.
    + apply Nat.eqb_eq in E; subst; constructor; lia.
    + inversion H; subst; constructor; apply Nat.eqb_neq in E; lia.
  - constructor.
  - inversion H; subst; econstructor; [eapply IHt1|eapply IHt2]; eassumption.
  - inversion H; subst; constructor; eapply IHt; eassumption.
  - constructor.
  - constructor.
Qed.

Lemma step_preserves_lc : forall t u, t --> u ->
  locally_closed t -> locally_closed u.
Proof.
  intros t u H; induction H; intros Hlc.
  - inversion Hlc; subst.
    inversion H4; subst.
    eapply lc_open_rec; [eassumption|apply value_lc; exact H0].
  - inversion Hlc; subst; econstructor; [eapply IHstep; eassumption|assumption].
  - inversion Hlc; subst; econstructor; [assumption|eapply IHstep; eassumption].
Qed.

Lemma sn_reduct : forall t u, t --> u -> strongly_normalizing t ->
  strongly_normalizing u.
Proof. intros t u H HS; inversion HS; eauto. Qed.

Lemma reducible_lc : forall T t, reducible T t -> locally_closed t.
Proof. induction T; simpl; intros t H; tauto. Qed.

Lemma reducible_sn : forall T t, reducible T t -> strongly_normalizing t.
Proof. induction T; simpl; intros t H; tauto. Qed.

Lemma sn_induction : forall (P : tm -> Prop) t,
  strongly_normalizing t ->
  (forall t, (forall u, t --> u -> P u) -> P t) -> P t.
Proof.
  intros P t Hsn; induction Hsn as [t Hnext IH]; intros HP.
  apply HP; intros u Hu; apply IH; assumption.
Qed.

Lemma reducible_step : forall T t u, t --> u -> reducible T t -> reducible T u.
Proof.
  induction T; simpl; intros t u Hstep [HS [Hlc HR]].
  - split.
    + eapply sn_reduct; eauto.
    + split; [eapply step_preserves_lc; eauto|exact I].
  - split.
    + eapply sn_reduct; eauto.
    + split.
      * eapply step_preserves_lc; eauto.
      * intros a Ha.
        eapply IHT2; [apply ST_App1; [exact Hstep|apply reducible_lc with (T:=T1); exact Ha]|].
        apply HR; exact Ha.
Qed.

Lemma step_deterministic : forall t u v,
  t --> u -> t --> v -> u = v.
Proof.
  intros t u v H1; revert v.
  induction H1; intros vout H2; inversion H2; subst; eauto.
  all: try match goal with Hred : tm_abs _ _ --> _ |- _ => inversion Hred end.
  all: try match goal with
    | Hv : value ?x, Hs : ?x --> _ |- _ => exfalso; eapply (value_no_step x Hv); exact Hs
    end.
  all: try (f_equal; eauto).
Qed.

Lemma sn_step_expand : forall t u,
  t --> u -> strongly_normalizing u -> strongly_normalizing t.
Proof.
  intros t u Hstep Hsn. constructor. intros t' Ht.
  assert (t' = u) by (eapply step_deterministic; eauto).
  subst; exact Hsn.
Qed.

Lemma reducible_step_expand : forall T t u,
  t --> u -> locally_closed t -> reducible T u -> reducible T t.
Proof.
  induction T; simpl; intros t u Hstep Hlc [HS [Hlu HR]].
  - split; [eapply sn_step_expand; eauto|].
    split; [exact Hlc|exact I].
  - split; [eapply sn_step_expand; eauto|].
    split; [exact Hlc|].
    intros a Ha.
    eapply IHT2.
    + apply ST_App1; [exact Hstep|apply reducible_lc with (T:=T1); exact Ha].
    + constructor; [exact Hlc|apply reducible_lc with (T:=T1); exact Ha].
    + apply HR; exact Ha.
Qed.

Lemma neutral_reducible : forall T t,
  locally_closed t -> (forall u, ~ (t --> u)) -> ~ value t -> reducible T t.
Proof.
  induction T; simpl; intros t Hlc Hnostep Hnval.
  - split.
    + constructor; intros u Hu; exfalso; eapply Hnostep; eassumption.
    + split; [exact Hlc|exact I].
  - split.
    + constructor; intros u Hu; exfalso; eapply Hnostep; eassumption.
    + split; [exact Hlc|].
      intros a Ha.
      apply IHT2.
      * constructor; [exact Hlc|apply reducible_lc with (T:=T1); exact Ha].
      * intros u Hu; inversion Hu; subst.
        -- exfalso; apply Hnval; constructor; assumption.
        -- exfalso; eapply Hnostep; eassumption.
        -- exfalso; apply Hnval; assumption.
      * intro Hv; inversion Hv.
Qed.

Lemma reducible_abs_application : forall A B body a,
  locally_closed (tm_abs A body) ->
  (forall v, reducible A v -> reducible B (open body v)) ->
  reducible A a ->
  reducible B (tm_app (tm_abs A body) a).
Proof.
  intros A B body a Habs Hbody Ha.
  assert (Haux : forall z, strongly_normalizing z -> reducible A z ->
      reducible B (tm_app (tm_abs A body) z)).
  { intros z Hsn.
    eapply (sn_induction
      (fun z => reducible A z -> reducible B (tm_app (tm_abs A body) z)) z Hsn).
    intros z0 IH Hz.
    destruct (value_dec z0) as [Hv|Hnv].
    + eapply reducible_step_expand.
      * apply ST_AppAbs; [exact Habs|exact Hv].
      * constructor; [exact Habs|apply reducible_lc with (T:=A); exact Hz].
      * apply Hbody; exact Hz.
    + destruct (step_exists_dec z0) as [[z' Hstep]|Hnone].
      * eapply reducible_step_expand.
        -- apply ST_App2; [apply v_abs; exact Habs|exact Hstep].
        -- constructor; [exact Habs|apply reducible_lc with (T:=A); exact Hz].
        -- apply IH; [exact Hstep|].
           eapply reducible_step; eauto.
      * apply neutral_reducible.
        -- constructor; [exact Habs|apply reducible_lc with (T:=A); exact Hz].
        -- intros u Hu; inversion Hu; subst.
           ++ exfalso; apply Hnv; exact H4.
           ++ inversion H1.
           ++ exfalso; apply (Hnone t2'); exact H3.
        -- intro Hv; inversion Hv. }
  eapply Haux; [apply reducible_sn with (T:=A); exact Ha|exact Ha].
Qed.

Fixpoint apply_subst (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_app t1 t2 => tm_app (apply_subst sigma t1) (apply_subst sigma t2)
  | tm_abs A t1 => tm_abs A (apply_subst sigma t1)
  | tm_true => tm_true
  | tm_false => tm_false
  end.

Definition extend_subst (sigma : atom -> tm) (x : atom) (v : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then v else sigma y.

Lemma open_rec_lc_at : forall d t, lc_at d t -> forall k u,
  open_rec (d + k) u t = t.
Proof.
  intros d t H; induction H; intros j u; simpl.
  - destruct (Nat.eqb (k + j) i) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - reflexivity.
  - rewrite IHlc_at1, IHlc_at2; reflexivity.
  - replace (S (k + j)) with (S k + j) by lia.
    f_equal; apply IHlc_at.
  - reflexivity.
  - reflexivity.
Qed.

Lemma apply_open_rec : forall t k u sigma,
  (forall x, locally_closed (sigma x)) ->
  apply_subst sigma (open_rec k u t) =
  open_rec k (apply_subst sigma u) (apply_subst sigma t).
Proof.
  induction t; intros k u sigma Hclosed; simpl; try (f_equal; eauto).
  - destruct (Nat.eqb k n); reflexivity.
  - assert (Hlc : open_rec k (apply_subst sigma u) (sigma a) = sigma a).
    { replace k with (0 + k) by lia.
      apply open_rec_lc_at; apply Hclosed. }
    rewrite Hlc; reflexivity.
Qed.

Lemma apply_open_fvar : forall t x sigma,
  (forall y, locally_closed (sigma y)) ->
  apply_subst sigma (open t (tm_fvar x)) =
  open (apply_subst sigma t) (sigma x).
Proof.
  intros t x sigma Hclosed; unfold open; rewrite apply_open_rec; simpl; auto.
Qed.

Lemma subst_extend_eq : forall sigma x v y,
  extend_subst sigma x v y = if Nat.eqb x y then v else sigma y.
Proof. reflexivity. Qed.

Fixpoint list_max (L : list nat) : nat :=
  match L with nil => 0 | cons x xs => Nat.max x (list_max xs) end.

Lemma in_list_le_max : forall x L, In x L -> x <= list_max L.
Proof.
  intros x L; induction L as [|a L IH]; simpl; intros H; [contradiction|].
  destruct H as [->|H]; [apply Nat.le_max_l|eapply Nat.le_trans; [eapply IH; eauto|apply Nat.le_max_r]].
Qed.

Lemma fresh_notin : forall L : list atom, exists x, ~ In x L.
Proof.
  intros L; exists (S (list_max L)); intros Hin.
  pose proof (in_list_le_max _ _ Hin); lia.
Qed.

Lemma sn_value : forall v, value v -> strongly_normalizing v.
Proof.
  intros v Hv; constructor; intros u Hs; exfalso; eapply value_no_step; eauto.
Qed.

Lemma typing_lc : forall Gamma t T, <{ Gamma |-- t \in T }> -> locally_closed t.
Proof.
  intros Gamma t T HT; induction HT.
  - constructor.
  - apply lc_abs.
    destruct (fresh_notin L) as [x Hx].
    apply lc_open_rec_inv with x.
    apply H0; exact Hx.
  - unfold locally_closed in *; eapply lc_app; eassumption.
  - constructor.
  - constructor.
Qed.

Lemma apply_subst_lc : forall k t, lc_at k t -> forall sigma,
  (forall x, locally_closed (sigma x)) -> lc_at k (apply_subst sigma t).
Proof.
  intros k t H; induction H; intros sigma Hsigma; simpl.
  - constructor; assumption.
  - apply lc_mono with (k:=0); [apply Hsigma|lia].
  - econstructor; [apply IHlc_at1|apply IHlc_at2]; assumption.
  - constructor; apply IHlc_at; assumption.
  - constructor.
  - constructor.
Qed.

Lemma sn_abstraction : forall A t, strongly_normalizing (tm_abs A t).
Proof.
  intros; constructor; intros u H; inversion H.
Qed.

Lemma sn_application_abs : forall A t v,
  value v -> strongly_normalizing (open t v) ->
  strongly_normalizing (tm_app (tm_abs A t) v).
Proof.
  intros A t v Hv Hbody; constructor; intros u Hstep; inversion Hstep; subst.
  - exact Hbody.
  - inversion H1.
  - exfalso; eapply (value_no_step v Hv); eassumption.
Qed.

Fixpoint fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ => nil
  | tm_fvar x => cons x nil
  | tm_app t1 t2 => fv t1 ++ fv t2
  | tm_abs _ t1 => fv t1
  | tm_true => nil
  | tm_false => nil
  end.

Lemma apply_subst_extend_fresh : forall sigma x v t,
  ~ In x (fv t) ->
  apply_subst (extend_subst sigma x v) t = apply_subst sigma t.
Proof.
  intros sigma x v t; induction t; simpl; intros Hfresh; try reflexivity.
  - destruct (Nat.eqb x a) eqn:E; [apply Nat.eqb_eq in E; subst; exfalso; apply Hfresh; simpl; auto|unfold extend_subst; rewrite E; reflexivity].
  - assert (H1 : ~ In x (fv t1)).
    { intro Hin; apply Hfresh; apply in_or_app; left; exact Hin. }
    assert (H2 : ~ In x (fv t2)).
    { intro Hin; apply Hfresh; apply in_or_app; right; exact Hin. }
    rewrite IHt1, IHt2; auto.
  - rewrite IHt; auto.
Qed.

Definition env_reducible (Gamma : context) (sigma : atom -> tm) : Prop :=
  (forall x, locally_closed (sigma x)) /\
  (forall x T, Gamma x = Some T -> reducible T (sigma x)).

Lemma fundamental : forall Gamma t T,
  <{ Gamma |-- t \in T }> ->
  forall sigma, env_reducible Gamma sigma ->
  reducible T (apply_subst sigma t).
Proof.
  intros Gamma t T HT.
  pose proof (typing_lc Gamma t T HT) as Htypedlc.
  induction HT; intros sigma Henv; simpl.
  - destruct Henv as [_ Htyped]. apply Htyped with (T:=T); exact H.
  - split.
    + apply sn_abstraction.
    + split.
      * unfold locally_closed; simpl; apply lc_abs.
        apply apply_subst_lc with (k:=1).
        -- inversion Htypedlc; assumption.
        -- intros y; apply (proj1 Henv).
      * intros v HRv.
        assert (Habs : locally_closed (tm_abs T1 (apply_subst sigma t1))).
        { unfold locally_closed; simpl; apply lc_abs.
          apply apply_subst_lc with (k:=1).
          - inversion Htypedlc; assumption.
          - intros y; apply (proj1 Henv). }
        assert (Hopen : forall w, reducible T1 w ->
            reducible T2 (open (apply_subst sigma t1) w)).
        { intros w HRw.
          destruct (fresh_notin (L ++ fv t1)) as [x Hx].
          assert (HxL : ~ In x L) by (intro Hin; apply Hx; apply in_or_app; left; exact Hin).
          assert (HxF : ~ In x (fv t1)) by (intro Hin; apply Hx; apply in_or_app; right; exact Hin).
          pose proof (H x HxL) as Htyping.
          pose proof (typing_lc (update Gamma x T1) (open t1 (tm_fvar x)) T2 Htyping) as Hbodylc.
          set (sigma' := extend_subst sigma x w).
          assert (Henv' : env_reducible (update Gamma x T1) sigma').
          { split.
            - intros y; unfold sigma', extend_subst; destruct (Nat.eqb x y).
              + apply reducible_lc with (T:=T1); exact HRw.
              + apply (proj1 Henv).
            - intros y U Hy; unfold sigma', extend_subst in *; simpl in *.
              unfold update in Hy; simpl in Hy.
              destruct (Nat.eqb x y); [inversion Hy; subst; exact HRw|].
              apply (proj2 Henv) with (T:=U); exact Hy. }
          specialize (H0 x HxL Hbodylc sigma' Henv').
          simpl in H0; rewrite apply_open_fvar in H0.
          2:{ intros y; unfold sigma', extend_subst; destruct (Nat.eqb x y).
              - apply reducible_lc with (T:=T1); exact HRw.
              - apply (proj1 Henv). }
          unfold sigma', extend_subst in H0; rewrite Nat.eqb_refl in H0.
          change (reducible T2 (open (apply_subst (extend_subst sigma x w) t1) w)) in H0.
          rewrite apply_subst_extend_fresh in H0 by exact HxF.
          exact H0. }
        eapply reducible_abs_application.
        -- exact Habs.
        -- exact Hopen.
        -- exact HRv.
  - pose proof (IHHT1 (typing_lc Gamma t1 (Ty_Arrow T1 T2) HT1) sigma Henv) as Hfun.
    pose proof (IHHT2 (typing_lc Gamma t2 T1 HT2) sigma Henv) as Harg.
    simpl in Hfun; apply Hfun; exact Harg.
  - split; [apply sn_value; constructor|].
    split; [unfold locally_closed; constructor|exact I].
  - split; [apply sn_value; constructor|].
    split; [unfold locally_closed; constructor|exact I].
Qed.

Lemma fv_open_rec_preserve : forall t k x y,
  In y (fv t) -> In y (fv (open_rec k (tm_fvar x) t)).
Proof.
  induction t; simpl; intros k x y Hin.
  - contradiction.
  - simpl in Hin; destruct Hin as [<-|[]]; simpl; auto.
  - apply in_app_iff in Hin as [Hin|Hin]; apply in_app_iff.
    + left; eapply IHt1; eauto.
    + right; eapply IHt2; eauto.
  - eapply IHt; eauto.
  - contradiction.
  - contradiction.
Qed.

Lemma typing_fv : forall Gamma t T x,
  <{ Gamma |-- t \in T }> -> In x (fv t) -> exists U, Gamma x = Some U.
Proof.
  intros Gamma t T x HT; induction HT; simpl; intros Hin.
  - simpl in Hin; destruct Hin as [<-|[]]; eauto.
  - destruct (fresh_notin (cons x L)) as [y Hy].
    assert (HyL : ~ In y L) by (intro Hnot; apply Hy; simpl; auto).
    assert (Hyx : y <> x) by (intro Hnot; subst; apply Hy; simpl; auto).
    assert (Hin' : In x (fv (open t1 (tm_fvar y)))).
    { unfold open; eapply fv_open_rec_preserve; exact Hin. }
    destruct (H0 y HyL Hin') as [U HU].
    unfold update in HU; destruct (Nat.eqb y x) eqn:E.
    + apply Nat.eqb_eq in E; contradiction.
    + exists U; exact HU.
  - apply in_app_iff in Hin as [Hin|Hin].
    + apply IHHT1 in Hin; destruct Hin as [U HU]; eauto.
    + apply IHHT2 in Hin; destruct Hin as [U HU]; eauto.
  - contradiction.
  - contradiction.
Qed.

Lemma apply_subst_const_true_empty_fv : forall t,
  (forall x, ~ In x (fv t)) ->
  apply_subst (fun _ => tm_true) t = t.
Proof.
  induction t; simpl; intros H; try reflexivity.
  - exfalso; apply (H a); simpl; auto.
  - f_equal.
    + apply IHt1; intros x Hin; apply (H x); apply in_or_app; left; exact Hin.
    + apply IHt2; intros x Hin; apply (H x); apply in_or_app; right; exact Hin.
  - f_equal; apply IHt; exact H.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T H.
  assert (Hfv : forall x, ~ In x (fv t)).
  { intros x Hin.
    destruct (typing_fv empty t T x H Hin) as [U HU].
    unfold empty in HU; discriminate. }
  pose proof (fundamental empty t T H (fun _ => tm_true)) as Hfund.
  assert (Henv : env_reducible empty (fun _ => tm_true)).
  { split.
    - intros; unfold locally_closed; constructor.
    - intros x U Hx; unfold empty in Hx; discriminate. }
  specialize (Hfund Henv).
  rewrite apply_subst_const_true_empty_fv in Hfund by exact Hfv.
  eapply reducible_sn; exact Hfund.
Qed.

End STLCNormalizationNoneHardTask.
