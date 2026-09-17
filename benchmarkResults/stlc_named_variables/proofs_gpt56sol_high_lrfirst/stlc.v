(** STLC call-by-value normalization benchmark task. *)

From Stdlib Require Import Strings.String.

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

(** A term is closed when substituting for any variable has no effect.  This
    extensional definition is particularly convenient for the named syntax
    used in this file. *)
Definition closed (t : tm) : Prop :=
  forall x s, subst x s t = t.

Definition renaming := string -> tm.

Definition rupdate (rho : renaming) (x : string) (u : tm) : renaming :=
  fun y => if String.eqb x y then u else rho y.

Fixpoint msubst (rho : renaming) (t : tm) : tm :=
  match t with
  | tm_var x => rho x
  | tm_app t1 t2 => tm_app (msubst rho t1) (msubst rho t2)
  | tm_abs x A b =>
      tm_abs x A (msubst (rupdate rho x (tm_var x)) b)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 =>
      tm_if (msubst rho t1) (msubst rho t2) (msubst rho t3)
  end.

(** [proper rho] says that [rho x] has no free variables other than possibly
    [x].  Thus the identity renaming is proper, and replacing an entry by a
    closed term preserves properness. *)
Definition proper (rho : renaming) : Prop :=
  forall x y s, x <> y -> subst x s (rho y) = rho y.

Lemma multi_trans : forall (X : Type) (Q : X -> X -> Prop) x y z,
  multi Q x y -> multi Q y z -> multi Q x z.
Proof.
  intros X Q x y z Hxy Hyz. induction Hxy.
  - exact Hyz.
  - eapply multi_step; eauto.
Qed.

Lemma multi_app1 : forall t t' u,
  t -->* t' -> tm_app t u -->* tm_app t' u.
Proof.
  intros t t' u H. induction H.
  - constructor.
  - eapply multi_step. apply ST_App1; eauto. exact IHmulti.
Qed.

Lemma multi_app2 : forall v u u',
  value v -> u -->* u' -> tm_app v u -->* tm_app v u'.
Proof.
  intros v u u' Hv H. induction H.
  - constructor.
  - eapply multi_step. apply ST_App2; eauto. exact IHmulti.
Qed.

Lemma multi_if : forall t t' u v,
  t -->* t' -> tm_if t u v -->* tm_if t' u v.
Proof.
  intros t t' u v H. induction H.
  - constructor.
  - eapply multi_step. apply ST_If; eauto. exact IHmulti.
Qed.

Lemma closed_true : closed tm_true.
Proof. intros x s; reflexivity. Qed.

Lemma closed_false : closed tm_false.
Proof. intros x s; reflexivity. Qed.

Lemma closed_app : forall t u,
  closed t -> closed u -> closed (tm_app t u).
Proof.
  unfold closed. intros t u Ht Hu x s. simpl. rewrite Ht, Hu. reflexivity.
Qed.

Lemma closed_if : forall t u v,
  closed t -> closed u -> closed v -> closed (tm_if t u v).
Proof.
  unfold closed. intros t u v Ht Hu Hv x s. simpl.
  rewrite Ht, Hu, Hv. reflexivity.
Qed.

Lemma proper_update_closed : forall rho x u,
  proper rho -> closed u -> proper (rupdate rho x u).
Proof.
  unfold proper, closed, rupdate.
  intros rho x u Hr Hu y z s Hneq.
  destruct (String.eqb x z) eqn:Hxz.
  - apply Hu.
  - apply Hr; assumption.
Qed.

Lemma proper_protect : forall rho x,
  proper rho -> proper (rupdate rho x (tm_var x)).
Proof.
  unfold proper, rupdate. intros rho x Hr y z s Hneq.
  destruct (String.eqb x z) eqn:Hxz.
  - apply String.eqb_eq in Hxz. subst z. simpl.
    destruct (String.eqb y x) eqn:Hyx; [|reflexivity].
    apply String.eqb_eq in Hyx. contradiction.
  - apply Hr; assumption.
Qed.

Lemma msubst_ext : forall rho sigma t,
  (forall x, rho x = sigma x) -> msubst rho t = msubst sigma t.
Proof.
  intros rho sigma t. revert rho sigma.
  induction t; intros rho sigma Heq; simpl.
  - apply Heq.
  - rewrite (IHt1 rho sigma Heq), (IHt2 rho sigma Heq). reflexivity.
  - f_equal. apply IHt. intros y. unfold rupdate.
    destruct (String.eqb s y); [reflexivity | apply Heq].
  - reflexivity.
  - reflexivity.
  - rewrite (IHt1 rho sigma Heq), (IHt2 rho sigma Heq),
      (IHt3 rho sigma Heq). reflexivity.
Qed.

(** The beta-substitution lemma.  Protecting [x] while descending under the
    outer abstraction and then beta-substituting is the same as extending the
    simultaneous substitution by [x := v]. *)
Lemma subst_msubst_protect : forall t rho x v,
  proper rho -> closed v ->
  subst x v (msubst (rupdate rho x (tm_var x)) t) =
  msubst (rupdate rho x v) t.
Proof.
  induction t; intros rho x v Hproper Hclosed; simpl.
  - unfold rupdate. destruct (String.eqb x s) eqn:Hxs.
    + apply String.eqb_eq in Hxs. subst s. simpl.
      rewrite String.eqb_refl. reflexivity.
    + apply String.eqb_neq in Hxs. apply Hproper; assumption.
  - rewrite IHt1, IHt2; auto.
  - destruct (String.eqb x s) eqn:Hxs.
    + f_equal. apply msubst_ext. intros y. unfold rupdate.
      apply String.eqb_eq in Hxs. subst s.
      destruct (String.eqb x y); reflexivity.
    + f_equal.
      transitivity
        (subst x v
           (msubst
              (rupdate (rupdate rho s (tm_var s)) x (tm_var x)) t0)).
      * f_equal. apply msubst_ext. intros y. unfold rupdate.
        destruct (String.eqb s y) eqn:Hsy;
        destruct (String.eqb x y) eqn:Hxy; try reflexivity.
        apply String.eqb_eq in Hsy. apply String.eqb_eq in Hxy.
        apply String.eqb_neq in Hxs. congruence.
      * rewrite IHt; [|apply proper_protect; assumption|assumption].
        apply msubst_ext. intros y. unfold rupdate.
        destruct (String.eqb s y) eqn:Hsy;
        destruct (String.eqb x y) eqn:Hxy; try reflexivity.
        apply String.eqb_eq in Hsy. apply String.eqb_eq in Hxy.
        apply String.eqb_neq in Hxs. congruence.
  - reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2, IHt3; auto.
Qed.

(** Substitution of a variable not supplied by a typing context cannot affect
    a well-typed simultaneous instance. *)
Lemma typed_msubst_invariant : forall Gamma t T rho x s,
  has_type Gamma t T ->
  (forall y U, Gamma y = Some U -> subst x s (rho y) = rho y) ->
  subst x s (msubst rho t) = msubst rho t.
Proof.
  intros Gamma t T rho x s HT. revert rho x s.
  induction HT; intros rho y u Henv; simpl.
  - eapply Henv; eauto.
  - destruct (String.eqb y x) eqn:Hyx; [reflexivity|].
    f_equal. apply IHHT. intros z U Hz.
    unfold rupdate. destruct (String.eqb x z) eqn:Hxz.
    + apply String.eqb_eq in Hxz. subst z. simpl. rewrite Hyx. reflexivity.
    + eapply Henv with (U := U). unfold update in Hz.
      rewrite Hxz in Hz. exact Hz.
  - rewrite IHHT1, IHHT2; eauto.
  - reflexivity.
  - reflexivity.
  - rewrite IHHT1, IHHT2, IHHT3; eauto.
Qed.

Lemma typed_msubst_closed : forall Gamma t T rho,
  has_type Gamma t T ->
  (forall x U, Gamma x = Some U -> closed (rho x)) ->
  closed (msubst rho t).
Proof.
  unfold closed. intros Gamma t T rho HT Henv x s.
  eapply typed_msubst_invariant; eauto.
Qed.

(** The type-indexed logical relation.  At base type it records which boolean
    is reached.  At function type it records an abstraction reached by CBV
    evaluation and its action on every reducible value. *)
Fixpoint R (T : ty) (t : tm) : Prop :=
  closed t /\
  match T with
  | Ty_Bool => t -->* tm_true \/ t -->* tm_false
  | Ty_Arrow A B =>
      exists x body,
        t -->* tm_abs x A body /\
        closed (tm_abs x A body) /\
        forall v, value v -> R A v -> R B (subst x v body)
  end.

Lemma R_closed : forall T t, R T t -> closed t.
Proof. destruct T; simpl; intros t [H _]; exact H. Qed.

Lemma R_halts : forall T t, R T t -> halts t.
Proof.
  destruct T; intros t [Hc HR].
  - destruct HR as [H | H].
    + exists tm_true. split; [assumption | constructor].
    + exists tm_false. split; [assumption | constructor].
  - destruct HR as [x [body [Hev [Hcl Hfun]]]].
    exists (tm_abs x T1 body). split; [assumption | constructor].
Qed.

Lemma R_value : forall T t,
  R T t -> exists v, t -->* v /\ value v /\ R T v.
Proof.
  destruct T; intros t [Hc HR].
  - destruct HR as [Ht | Hf].
    + exists tm_true. split; [exact Ht|]. split; [constructor|].
      split; [apply closed_true|]. left; constructor.
    + exists tm_false. split; [exact Hf|]. split; [constructor|].
      split; [apply closed_false|]. right; constructor.
  - destruct HR as [x [body [Hev [Hcl Hfun]]]].
    exists (tm_abs x T1 body). split; [assumption|]. split; [constructor|].
    split; [exact Hcl|]. exists x, body. split; [constructor|].
    split; assumption.
Qed.

Lemma R_back : forall T t t',
  closed t -> t -->* t' -> R T t' -> R T t.
Proof.
  induction T; intros t t' Hclosed Hsteps [Hclosed' HR]; split.
  - assumption.
  - destruct HR as [H | H]; [left | right];
      eapply multi_trans; eauto.
  - assumption.
  - destruct HR as [x [body [Hev [Hbody Hfun]]]].
    exists x, body. repeat split; try assumption.
    eapply multi_trans; eauto.
Qed.

Definition env_R (Gamma : context) (rho : renaming) : Prop :=
  proper rho /\
  forall x T, Gamma x = Some T -> R T (rho x).

Lemma env_R_update : forall Gamma rho x A v,
  env_R Gamma rho -> R A v ->
  env_R (update Gamma x A) (rupdate rho x v).
Proof.
  intros Gamma rho x A v [Hproper Henv] Hv. split.
  - apply proper_update_closed; [assumption | eapply R_closed; eauto].
  - intros y T Hy. unfold update in Hy. unfold rupdate.
    destruct (String.eqb x y) eqn:Hxy.
    + inversion Hy; subst. exact Hv.
    + apply Henv. exact Hy.
Qed.

Lemma fundamental : forall Gamma t T,
  has_type Gamma t T ->
  forall rho, env_R Gamma rho -> R T (msubst rho t).
Proof.
  intros Gamma t T HT. induction HT; intros rho Henv; simpl.
  - destruct Henv as [_ Henv]. eapply Henv; eauto.
  - assert (Habsclosed :
        closed (tm_abs x T1 (msubst (rupdate rho x (tm_var x)) t))).
    { unfold closed. intros y u. simpl.
      destruct (String.eqb y x) eqn:Hyx; [reflexivity|].
      f_equal. eapply typed_msubst_invariant; [exact HT|].
      intros z U Hz. unfold update in Hz. unfold rupdate.
      destruct (String.eqb x z) eqn:Hxz.
      - apply String.eqb_eq in Hxz. subst z. simpl. rewrite Hyx. reflexivity.
      - eapply R_closed. eapply (proj2 Henv). exact Hz. }
    split.
    + exact Habsclosed.
    + exists x, (msubst (rupdate rho x (tm_var x)) t).
      split; [constructor|]. split.
      * exact Habsclosed.
      * intros v Hv HRv.
        specialize (IHHT (rupdate rho x v) (env_R_update _ _ _ _ _ Henv HRv)).
        rewrite (subst_msubst_protect t rho x v).
        -- exact IHHT.
        -- exact (proj1 Henv).
        -- eapply R_closed; eauto.
  - destruct (IHHT1 rho Henv) as [Hcl1 HR1].
    destruct HR1 as [x [body [Hfunsteps [Hclabs Haction]]]].
    pose proof (IHHT2 rho Henv) as HRarg.
    destruct (R_value _ _ HRarg) as [v [Hargsteps [Hv HRv]]].
    apply (R_back T2 (tm_app (msubst rho t1) (msubst rho t2))
              (subst x v body)).
    + apply closed_app; [exact Hcl1 | eapply R_closed; eauto].
    + eapply multi_trans.
      * apply multi_app1. exact Hfunsteps.
      * eapply multi_trans.
        -- apply multi_app2; [constructor | exact Hargsteps].
        -- eapply multi_step. apply ST_AppAbs; exact Hv. constructor.
    + apply Haction; assumption.
  - split; [apply closed_true | left; constructor].
  - split; [apply closed_false | right; constructor].
  - pose proof (IHHT1 rho Henv) as HRguard.
    pose proof (IHHT2 rho Henv) as HRthen.
    pose proof (IHHT3 rho Henv) as HRelse.
    destruct HRguard as [Hclg [Hg | Hg]].
    + apply (R_back T (tm_if (msubst rho t1) (msubst rho t2)
                         (msubst rho t3)) (msubst rho t2)).
      * apply closed_if; [exact Hclg | eapply R_closed; eauto |
                          eapply R_closed; eauto].
      * eapply multi_trans. apply multi_if; exact Hg.
        eapply multi_step. apply ST_IfTrue. constructor.
      * exact HRthen.
    + apply (R_back T (tm_if (msubst rho t1) (msubst rho t2)
                         (msubst rho t3)) (msubst rho t3)).
      * apply closed_if; [exact Hclg | eapply R_closed; eauto |
                          eapply R_closed; eauto].
      * eapply multi_trans. apply multi_if; exact Hg.
        eapply multi_step. apply ST_IfFalse. constructor.
      * exact HRelse.
Qed.

Definition id_renaming : renaming := fun x => tm_var x.

Lemma proper_id : proper id_renaming.
Proof.
  unfold proper, id_renaming. intros x y s Hxy. simpl.
  destruct (String.eqb x y) eqn:H;
    [apply String.eqb_eq in H; contradiction | reflexivity].
Qed.

Lemma msubst_id : forall t, msubst id_renaming t = t.
Proof.
  induction t as
      [x | t1 IH1 t2 IH2 | x A body IH | | | g IHg u IHu v IHv]; simpl.
  - reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - f_equal. transitivity (msubst id_renaming body).
    + apply msubst_ext. intros y. unfold rupdate, id_renaming.
      destruct (String.eqb x y) eqn:Hxy; [|reflexivity].
      apply String.eqb_eq in Hxy. subst y. reflexivity.
    + exact IH.
  - reflexivity.
  - reflexivity.
  - rewrite IHg, IHu, IHv. reflexivity.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  halts t.
Proof.
  intros t T HT.
  assert (Henv : env_R empty id_renaming).
  { split; [apply proper_id|]. intros x U H. discriminate. }
  pose proof (fundamental _ _ _ HT _ Henv) as HR.
  rewrite msubst_id in HR.
  eapply R_halts; eauto.
Qed.

End STLCCBVNormalizationTask.
