(** STLC call-by-value normalization benchmark task. *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import Logic.FunctionalExtensionality.

Module STLCCBVNormalizationTask.

(** [multi] is needed to state multi-step evaluation. *)
Inductive multi {X : Type} (R : X -> X -> Prop) : X -> X -> Prop :=
  | multi_refl : forall x, multi R x x
  | multi_step : forall x y z,
      R x y ->
      multi R y z ->
      multi R x z.

(** Language syntax. *)

Inductive ty : Type :=
  | Ty_Bool : ty
  | Ty_Arrow : ty -> ty -> ty.

Inductive tm : Type :=
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm.

Declare Scope stlc_scope.
Delimit Scope stlc_scope with stlc.
Open Scope stlc_scope.

Declare Custom Entry stlc_ty.
Declare Custom Entry stlc_tm.

Notation "x" := x
  (in custom stlc_ty at level 0, x global) : stlc_scope.
Notation "S -> T" := (Ty_Arrow S T)
  (in custom stlc_ty at level 99, right associativity) : stlc_scope.
Notation "'Bool'" := Ty_Bool
  (in custom stlc_ty at level 0) : stlc_scope.

Notation "'if' x 'then' y 'else' z" :=
  (tm_if x y z)
  (in custom stlc_tm at level 200,
   x custom stlc_tm,
   y custom stlc_tm,
   z custom stlc_tm at level 200,
   left associativity).
Notation "'true'" := tm_true
  (in custom stlc_tm at level 0).
Notation "'false'" := tm_false
  (in custom stlc_tm at level 0).
Notation "x" := x
  (in custom stlc_tm at level 0, x constr at level 0) : stlc_scope.
Notation "<{ e }>" := e
  (e custom stlc_tm at level 200) : stlc_scope.
Notation "( x )" := x
  (in custom stlc_tm at level 0, x custom stlc_tm) : stlc_scope.
Notation "x y" := (tm_app x y)
  (in custom stlc_tm at level 10, left associativity) : stlc_scope.
Notation "\ x : t , y" := (tm_abs x t y)
  (in custom stlc_tm at level 200,
   x global,
   t custom stlc_ty,
   y custom stlc_tm at level 200,
   left associativity).

Coercion tm_var : string >-> tm.
Arguments tm_var _%_string.

(** Call-by-value operational semantics. *)

Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
      value <{ \x:T, t }>
  | v_true :
      value <{ true }>
  | v_false :
      value <{ false }>.

Reserved Notation "'[' x ':=' s ']' t"
  (in custom stlc_tm at level 5,
   x global,
   s custom stlc_tm,
   t custom stlc_tm at next level,
   right associativity).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if String.eqb x y then s else t
  | <{ \y:T, t1 }> =>
      if String.eqb x y then t else <{ \y:T, [x:=s] t1 }>
  | <{ t1 t2 }> =>
      <{ [x:=s] t1 [x:=s] t2 }>
  | <{ true }> =>
      <{ true }>
  | <{ false }> =>
      <{ false }>
  | <{ if t1 then t2 else t3 }> =>
      <{ if [x:=s] t1 then [x:=s] t2 else [x:=s] t3 }>
  end

where "'[' x ':=' s ']' t" := (subst x s t)
  (in custom stlc_tm).

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t v,
      value v ->
      <{ (\x:T, t) v }> --> <{ [x:=v] t }>
  | ST_App1 : forall t1 t1' t2,
      t1 --> t1' ->
      <{ t1 t2 }> --> <{ t1' t2 }>
  | ST_App2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      <{ v1 t2 }> --> <{ v1 t2' }>
  | ST_IfTrue : forall t1 t2,
      <{ if true then t1 else t2 }> --> t1
  | ST_IfFalse : forall t1 t2,
      <{ if false then t1 else t2 }> --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      <{ if t1 then t2 else t3 }> --> <{ if t1' then t2 else t3 }>

where "t '-->' t'" := (step t t').

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

(** Typing rules. *)

Definition context := string -> option ty.

Definition empty : context :=
  fun _ => None.

Definition update (Gamma : context) (x : string) (T : ty) : context :=
  fun y => if String.eqb x y then Some T else Gamma y.

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
      <{ Gamma |-- x \in T }>
  | T_Abs : forall Gamma x T1 T2 t,
      <{ x |-> T1 ; Gamma |-- t \in T2 }> ->
      <{ Gamma |-- \x:T1, t \in T1 -> T2 }>
  | T_App : forall Gamma t1 t2 T1 T2,
      <{ Gamma |-- t1 \in T1 -> T2 }> ->
      <{ Gamma |-- t2 \in T1 }> ->
      <{ Gamma |-- t1 t2 \in T2 }>
  | T_True : forall Gamma,
      <{ Gamma |-- true \in Bool }>
  | T_False : forall Gamma,
      <{ Gamma |-- false \in Bool }>
  | T_If : forall Gamma t1 t2 t3 T,
      <{ Gamma |-- t1 \in Bool }> ->
      <{ Gamma |-- t2 \in T }> ->
      <{ Gamma |-- t3 \in T }> ->
      <{ Gamma |-- if t1 then t2 else t3 \in T }>

where "<{ Gamma '|--' t '\in' T }>" := (has_type Gamma t T)
  : stlc_scope.

(** Target theorem. *)

Definition halts (t : tm) : Prop :=
  exists v, t -->* v /\ value v.

(** Basic facts about contexts and typing. *)

Lemma update_eq : forall Gamma x T,
  update Gamma x T x = Some T.
Proof.
  intros. unfold update. now rewrite String.eqb_refl.
Qed.

Lemma update_neq : forall Gamma x y T,
  x <> y -> update Gamma x T y = Gamma y.
Proof.
  intros. unfold update. apply String.eqb_neq in H. now rewrite H.
Qed.

Lemma update_shadow : forall Gamma x T1 T2,
  update (update Gamma x T1) x T2 = update Gamma x T2.
Proof.
  intros. apply functional_extensionality. intros y.
  unfold update. destruct (String.eqb x y); reflexivity.
Qed.

Lemma update_permute : forall Gamma x y Tx Ty,
  x <> y ->
  update (update Gamma x Tx) y Ty =
  update (update Gamma y Ty) x Tx.
Proof.
  intros. apply functional_extensionality. intros z.
  unfold update.
  destruct (String.eqb y z) eqn:Ey;
  destruct (String.eqb x z) eqn:Ex; try reflexivity.
  apply String.eqb_eq in Ey. apply String.eqb_eq in Ex. subst. contradiction.
Qed.

Definition includedin (Gamma Gamma' : context) : Prop :=
  forall x T, Gamma x = Some T -> Gamma' x = Some T.

Lemma weakening : forall Gamma Gamma' t T,
  includedin Gamma Gamma' ->
  <{ Gamma |-- t \in T }> ->
  <{ Gamma' |-- t \in T }>.
Proof.
  intros Gamma Gamma' t T Hinc Hty.
  generalize dependent Gamma'.
  induction Hty; intros Delta Hinc; eauto using has_type.
  apply T_Abs. apply IHHty. intros y U Hy.
  unfold update in Hy |- *.
  destruct (String.eqb x y); eauto.
Qed.

Lemma empty_typing_weakening : forall Gamma t T,
  <{ empty |-- t \in T }> ->
  <{ Gamma |-- t \in T }>.
Proof.
  intros. eapply weakening; eauto.
  intros x U Hnone. discriminate.
Qed.

Lemma substitution_preserves_typing : forall Gamma x U t T s,
  <{ x |-> U ; Gamma |-- t \in T }> ->
  <{ empty |-- s \in U }> ->
  <{ Gamma |-- [x:=s] t \in T }>.
Proof.
  intros Gamma x U t.
  generalize dependent Gamma. generalize dependent x. generalize dependent U.
  induction t; intros U x Gamma T r Hty Hr; inversion Hty; subst; simpl.
  - match goal with H : update _ _ _ _ = Some _ |- _ =>
      rename H into Hlookup
    end.
    unfold update in Hlookup.
    destruct (String.eqb x s) eqn:Ex.
    + apply String.eqb_eq in Ex. subst. inversion Hlookup. subst.
      exact (empty_typing_weakening Gamma r _ Hr).
    + apply T_Var. exact Hlookup.
  - eapply T_App; eauto.
  - destruct (String.eqb x s) eqn:Ex.
    + apply String.eqb_eq in Ex. subst.
      apply T_Abs.
      match goal with H : has_type (update (update _ _ _) _ _) _ _ |- _ =>
        rename H into Hbody
      end.
      rewrite update_shadow in Hbody. exact Hbody.
    + apply String.eqb_neq in Ex.
      apply T_Abs. apply IHt with (U := U).
      * rewrite update_permute; eauto.
      * exact Hr.
  - constructor.
  - constructor.
  - eapply T_If; eauto.
Qed.

Lemma subst_unchanged : forall Gamma t T,
  <{ Gamma |-- t \in T }> ->
  forall x s, Gamma x = None -> subst x s t = t.
Proof.
  intros Gamma t T Hty. induction Hty; intros y u Hnone; simpl.
  - destruct (String.eqb y x) eqn:E; auto.
    apply String.eqb_eq in E. subst. rewrite H in Hnone. discriminate.
  - destruct (String.eqb y x) eqn:E; auto. f_equal.
    apply IHHty. apply String.eqb_neq in E.
    rewrite update_neq; congruence.
  - f_equal; eauto.
  - reflexivity.
  - reflexivity.
  - f_equal; eauto.
Qed.

Lemma empty_typing_closed : forall t T,
  <{ empty |-- t \in T }> ->
  forall x s, subst x s t = t.
Proof.
  intros. eapply subst_unchanged; eauto.
Qed.

Lemma preservation : forall t t' T,
  <{ empty |-- t \in T }> ->
  t --> t' ->
  <{ empty |-- t' \in T }>.
Proof.
  intros t t' T Hty Hstep.
  generalize dependent T.
  induction Hstep; intros U Hty; inversion Hty; subst; eauto using has_type.
  inversion H3; subst.
  eapply substitution_preserves_typing; eauto.
Qed.

(** Multi-step evaluation facts. *)

Lemma multi_transitive : forall t1 t2 t3,
  t1 -->* t2 -> t2 -->* t3 -> t1 -->* t3.
Proof.
  intros t1 t2 t3 H12 H23. induction H12; eauto using multi.
Qed.

Lemma multi_one : forall t t', t --> t' -> t -->* t'.
Proof.
  intros. eapply multi_step; eauto. constructor.
Qed.

Lemma multi_app1 : forall t1 t1' t2,
  t1 -->* t1' -> tm_app t1 t2 -->* tm_app t1' t2.
Proof.
  intros. induction H; eauto using multi, step.
Qed.

Lemma multi_app2 : forall v1 t2 t2',
  value v1 -> t2 -->* t2' -> tm_app v1 t2 -->* tm_app v1 t2'.
Proof.
  intros. induction H0; eauto using multi, step.
Qed.

Lemma multi_if : forall t1 t1' t2 t3,
  t1 -->* t1' ->
  tm_if t1 t2 t3 -->* tm_if t1' t2 t3.
Proof.
  intros. induction H; eauto using multi, step.
Qed.

Lemma preservation_multi : forall t t' T,
  <{ empty |-- t \in T }> ->
  t -->* t' ->
  <{ empty |-- t' \in T }>.
Proof.
  intros t t' T Hty Hmulti. induction Hmulti; eauto using preservation.
Qed.

Lemma value_no_step : forall v,
  value v -> forall t, ~ (v --> t).
Proof.
  intros v Hv t Hs. inversion Hv; subst; inversion Hs.
Qed.

Lemma step_deterministic : forall t t1 t2,
  t --> t1 -> t --> t2 -> t1 = t2.
Proof.
  intros t t1 t2 H1. generalize dependent t2.
  induction H1; intros u H2; inversion H2; subst; try reflexivity.
  all: try solve [
    exfalso;
    match goal with
    | Hv : value ?v, Hs : step ?v _ |- _ =>
        exact (value_no_step v Hv _ Hs)
    end].
  all: f_equal; eauto.
  all: match goal with
       | Hs : step (tm_abs _ _ _) _ |- _ => inversion Hs
       | Hs : step tm_true _ |- _ => inversion Hs
       | Hs : step tm_false _ |- _ => inversion Hs
       end.
Qed.

Lemma halts_after_step : forall t t',
  halts t -> t --> t' -> halts t'.
Proof.
  intros t t' [v [Hmulti Hv]] Hstep.
  inversion Hmulti; subst.
  - exfalso. eapply value_no_step; eauto.
  - assert (t' = y) by (eapply step_deterministic; eauto). subst.
    exists v. auto.
Qed.

(** Simultaneous substitutions.  [mask sigma x] leaves the variable bound by
    an abstraction untouched. *)

Definition replacement := string -> tm.

Definition override (sigma : replacement) (x : string) (v : tm) : replacement :=
  fun y => if String.eqb x y then v else sigma y.

Definition mask (sigma : replacement) (x : string) : replacement :=
  override sigma x (tm_var x).

Fixpoint msubst (sigma : replacement) (t : tm) : tm :=
  match t with
  | tm_var x => sigma x
  | tm_app t1 t2 => tm_app (msubst sigma t1) (msubst sigma t2)
  | tm_abs x T t1 => tm_abs x T (msubst (mask sigma x) t1)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 =>
      tm_if (msubst sigma t1) (msubst sigma t2) (msubst sigma t3)
  end.

Lemma msubst_ext : forall t sigma tau,
  (forall x, sigma x = tau x) ->
  msubst sigma t = msubst tau t.
Proof.
  induction t; intros sigma tau Heq; simpl; f_equal; eauto.
  apply IHt. intros y. unfold mask, override.
  destruct (String.eqb s y); auto.
Qed.

Lemma subst_msubst : forall t sigma x v,
  (forall y, subst x v (sigma y) = sigma y) ->
  subst x v (msubst (mask sigma x) t) =
  msubst (override sigma x v) t.
Proof.
  induction t; intros sigma x v Hclosed; simpl.
  - unfold mask, override.
    destruct (String.eqb x s) eqn:E.
    + apply String.eqb_eq in E. subst. simpl. now rewrite String.eqb_refl.
    + simpl. apply Hclosed.
  - rewrite IHt1, IHt2; auto.
  - destruct (String.eqb x s) eqn:E.
    + f_equal. apply msubst_ext. intros y.
      apply String.eqb_eq in E. subst.
      unfold mask, override.
      destruct (String.eqb s y); reflexivity.
    + f_equal.
      assert (Hm :
        msubst (mask (mask sigma x) s) t0 =
        msubst (mask (mask sigma s) x) t0).
      { apply msubst_ext. intros y. unfold mask, override.
        destruct (String.eqb s y) eqn:Es;
        destruct (String.eqb x y) eqn:Ex; try reflexivity.
        apply String.eqb_eq in Es. apply String.eqb_eq in Ex. subst.
        rewrite String.eqb_refl in E. discriminate. }
      rewrite Hm. rewrite IHt.
      * apply msubst_ext. intros y.
        unfold mask, override.
        destruct (String.eqb s y) eqn:Es;
        destruct (String.eqb x y) eqn:Ex; try reflexivity.
        apply String.eqb_eq in Es. apply String.eqb_eq in Ex. subst.
        rewrite String.eqb_refl in E. discriminate.
      * intros y. unfold mask, override.
        destruct (String.eqb s y) eqn:Es.
        -- apply String.eqb_eq in Es. subst. simpl. now rewrite E.
        -- apply Hclosed.
  - reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2, IHt3; auto.
Qed.

(** The required logical relation. *)

Fixpoint R (T : ty) (t : tm) : Prop :=
  <{ empty |-- t \in T }> /\ halts t /\
  (match T with
   | Ty_Bool => True
   | Ty_Arrow T1 T2 =>
       forall t1, R T1 t1 -> R T2 (tm_app t t1)
   end).

Lemma R_typing : forall T t, R T t -> <{ empty |-- t \in T }>.
Proof. destruct T; simpl; tauto. Qed.

Lemma R_halts : forall T t, R T t -> halts t.
Proof. destruct T; simpl; tauto. Qed.

(** [env_R] is the interpretation of a typing context requested in the
    statement: every typed variable is replaced by a term in [R]. *)

Definition env_R (Gamma : context) (sigma : replacement) : Prop :=
  (forall x T, Gamma x = Some T -> R T (sigma x)) /\
  (forall x y v, subst x v (sigma y) = sigma y).

(** A typing-only invariant for simultaneous substitutions.  Images are
    either closed terms or the variables deliberately exposed by [mask]. *)

Definition env_ok (Gamma Delta : context) (sigma : replacement) : Prop :=
  forall x T, Gamma x = Some T ->
    (sigma x = tm_var x /\ Delta x = Some T) \/
    has_type empty (sigma x) T.

Lemma env_ok_update : forall Gamma Delta sigma x T,
  env_ok Gamma Delta sigma ->
  env_ok (update Gamma x T) (update Delta x T) (mask sigma x).
Proof.
  unfold env_ok. intros Gamma Delta sigma x T Hok y U Hy.
  unfold update in Hy. unfold mask, override.
  destruct (String.eqb x y) eqn:E.
  - apply String.eqb_eq in E. subst. inversion Hy. subst.
    left. split; [reflexivity | apply update_eq].
  - specialize (Hok y U Hy). destruct Hok as [[Hs Hd] | Hclosed].
    + left. split; [exact Hs |].
      unfold update. rewrite E. exact Hd.
    + right. exact Hclosed.
Qed.

Lemma msubst_typing : forall Gamma t T,
  <{ Gamma |-- t \in T }> ->
  forall Delta sigma, env_ok Gamma Delta sigma ->
  has_type Delta (msubst sigma t) T.
Proof.
  intros Gamma t T Hty.
  induction Hty; intros Delta sigma Hok; simpl.
  - specialize (Hok x T H). destruct Hok as [[Heq Hlookup] | Hclosed].
    + rewrite Heq. constructor. exact Hlookup.
    + eapply empty_typing_weakening. exact Hclosed.
  - apply T_Abs. apply IHHty. now apply env_ok_update.
  - eapply T_App; eauto.
  - constructor.
  - constructor.
  - eapply T_If; eauto.
Qed.

Lemma env_R_env_ok : forall Gamma sigma,
  env_R Gamma sigma -> env_ok Gamma empty sigma.
Proof.
  unfold env_R, env_ok. intros Gamma sigma [HR _] x T Hlookup.
  right. specialize (HR x T Hlookup). now apply R_typing in HR.
Qed.

(** Closure properties of the logical relation. *)

Lemma R_step_forward : forall T t t',
  R T t -> t --> t' -> R T t'.
Proof.
  induction T as [|T1 IH1 T2 IH2]; intros t t' HR Hstep; simpl in *.
  - destruct HR as [Hty [Hhalt _]].
    split; [eapply preservation; eauto |].
    split; [eapply halts_after_step; eauto | exact I].
  - destruct HR as [Hty [Hhalt Happ]].
    split; [eapply preservation; eauto |].
    split; [eapply halts_after_step; eauto |].
    intros a Ha. apply IH2 with (t := tm_app t a).
    + apply Happ. exact Ha.
    + apply ST_App1. exact Hstep.
Qed.

Lemma R_multi_forward : forall T t t',
  R T t -> t -->* t' -> R T t'.
Proof.
  intros T t t' HR Hmulti. induction Hmulti; eauto using R_step_forward.
Qed.

Lemma halts_before_multi : forall t t',
  t -->* t' -> halts t' -> halts t.
Proof.
  intros t t' Hmulti [v [Htv Hv]].
  exists v. split; eauto using multi_transitive.
Qed.

Lemma R_multi_back : forall T t t',
  <{ empty |-- t \in T }> ->
  t -->* t' -> R T t' -> R T t.
Proof.
  induction T as [|T1 IH1 T2 IH2]; intros t t' Hty Hmulti HR; simpl in *.
  - split; [exact Hty |]. split.
    + eapply halts_before_multi; eauto. exact (R_halts Ty_Bool t' HR).
    + exact I.
  - destruct HR as [Hty' [Hhalt' Happ]].
    split; [exact Hty |]. split.
    + eapply halts_before_multi; eauto.
    + intros a Ha. apply IH2 with (t' := tm_app t' a).
      * eapply T_App; eauto. exact (R_typing T1 a Ha).
      * apply multi_app1. exact Hmulti.
      * apply Happ. exact Ha.
Qed.

Lemma canonical_bool : forall v,
  value v -> <{ empty |-- v \in Bool }> ->
  v = tm_true \/ v = tm_false.
Proof.
  intros v Hv Hty. inversion Hv; subst; inversion Hty; auto.
Qed.

Lemma env_R_update : forall Gamma sigma x T v,
  env_R Gamma sigma -> R T v ->
  env_R (update Gamma x T) (override sigma x v).
Proof.
  unfold env_R. intros Gamma sigma x T v [HR Hclosed] Hv.
  split.
  - intros y U Hy. unfold update in Hy. unfold override.
    destruct (String.eqb x y) eqn:E.
    + inversion Hy. subst. exact Hv.
    + apply HR with (x := y). exact Hy.
  - intros z y u. unfold override.
    destruct (String.eqb x y) eqn:E.
    + eapply empty_typing_closed. exact (R_typing T v Hv).
    + apply Hclosed.
Qed.

Lemma app_abs_multistep : forall x T body a v,
  a -->* v -> value v ->
  tm_app (tm_abs x T body) a -->* subst x v body.
Proof.
  intros. eapply multi_transitive.
  - apply multi_app2; [constructor | exact H].
  - apply multi_one. constructor. exact H0.
Qed.

Lemma if_true_multistep : forall g t2 t3,
  g -->* tm_true -> tm_if g t2 t3 -->* t2.
Proof.
  intros. eapply multi_transitive.
  - apply multi_if. exact H.
  - apply multi_one. constructor.
Qed.

Lemma if_false_multistep : forall g t2 t3,
  g -->* tm_false -> tm_if g t2 t3 -->* t3.
Proof.
  intros. eapply multi_transitive.
  - apply multi_if. exact H.
  - apply multi_one. constructor.
Qed.

(** Fundamental theorem of the logical relation.  Its induction has exactly
    the six cases of [has_type]. *)

Lemma fundamental : forall Gamma t T,
  <{ Gamma |-- t \in T }> ->
  forall sigma, env_R Gamma sigma -> R T (msubst sigma t).
Proof.
  intros Gamma t T Hty.
  induction Hty; intros sigma Henv; simpl.
  - destruct Henv as [Hmap _]. eapply Hmap; eauto.
  - assert (Habs_ty :
        has_type empty (msubst sigma (tm_abs x T1 t)) (Ty_Arrow T1 T2)).
    { apply msubst_typing with (Gamma := Gamma).
      - apply T_Abs. exact Hty.
      - now apply env_R_env_ok. }
    simpl in Habs_ty. simpl.
    split; [exact Habs_ty |]. split.
    + exists (tm_abs x T1 (msubst (mask sigma x) t)).
      split; [constructor | constructor].
    + intros a Ha.
      destruct (R_halts T1 a Ha) as [v [Hav Hv]].
      pose proof (R_multi_forward T1 a v Ha Hav) as HvR.
      pose proof (IHHty (override sigma x v)
                   (env_R_update _ _ _ _ _ Henv HvR)) as HbodyR.
      assert (Hclosed : forall y, subst x v (sigma y) = sigma y).
      { destruct Henv as [_ Hc]. exact (fun y => Hc x y v). }
      rewrite <- (subst_msubst t sigma x v Hclosed) in HbodyR.
      eapply R_multi_back.
      * eapply T_App; eauto. exact (R_typing T1 a Ha).
      * apply app_abs_multistep; [exact Hav | exact Hv].
      * exact HbodyR.
  - destruct (IHHty1 sigma Henv) as [Ht1 [Hh1 Happ]].
    apply Happ. apply IHHty2. exact Henv.
  - simpl. split; [constructor |]. split.
    + exists tm_true. split; constructor.
    + exact I.
  - simpl. split; [constructor |]. split.
    + exists tm_false. split; constructor.
    + exact I.
  - pose proof (IHHty1 sigma Henv) as Hg.
    pose proof (IHHty2 sigma Henv) as Hthen.
    pose proof (IHHty3 sigma Henv) as Helse.
    destruct (R_halts Ty_Bool (msubst sigma t1) Hg) as [v [Hgv Hv]].
    pose proof (preservation_multi _ _ Ty_Bool (R_typing _ _ Hg) Hgv) as Hvt.
    destruct (canonical_bool v Hv Hvt) as [Heq | Heq]; subst.
    + eapply R_multi_back.
      * eapply T_If; eauto using R_typing.
      * apply if_true_multistep. exact Hgv.
      * exact Hthen.
    + eapply R_multi_back.
      * eapply T_If; eauto using R_typing.
      * apply if_false_multistep. exact Hgv.
      * exact Helse.
Qed.

Lemma msubst_identity : forall Gamma t T,
  <{ Gamma |-- t \in T }> ->
  forall sigma,
    (forall x U, Gamma x = Some U -> sigma x = tm_var x) ->
    msubst sigma t = t.
Proof.
  intros Gamma t T Hty.
  induction Hty; intros sigma Hid; simpl.
  - now apply Hid with (U := T).
  - f_equal. apply IHHty. intros y U Hy.
    unfold update in Hy. unfold mask, override.
    destruct (String.eqb x y) eqn:E.
    + apply String.eqb_eq in E. subst. reflexivity.
    + apply Hid with (U := U). exact Hy.
  - f_equal; eauto.
  - reflexivity.
  - reflexivity.
  - f_equal; eauto.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  halts t.
Proof.
  intros t T Hty.
  set (sigma0 := (fun _ : string => tm_true)).
  assert (Henv : env_R empty sigma0).
  { split.
    - intros x U Hlookup. discriminate.
    - intros x y v. reflexivity. }
  pose proof (fundamental empty t T Hty sigma0 Henv) as HR.
  assert (Hsame : msubst sigma0 t = t).
  { apply msubst_identity with (Gamma := empty) (T := T); auto.
    intros x U Hlookup. discriminate. }
  rewrite Hsame in HR. exact (R_halts T t HR).
Qed.

End STLCCBVNormalizationTask.
