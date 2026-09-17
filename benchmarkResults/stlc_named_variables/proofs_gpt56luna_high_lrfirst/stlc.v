(** STLC call-by-value normalization benchmark task. *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Logic.Classical_Prop.

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

Inductive free_in (x : string) : tm -> Prop :=
  | FI_Var : free_in x <{ x }>
  | FI_AppL : forall t1 t2, free_in x t1 -> free_in x <{ t1 t2 }>
  | FI_AppR : forall t1 t2, free_in x t2 -> free_in x <{ t1 t2 }>
  | FI_Abs : forall y T t,
      x <> y -> free_in x t -> free_in x <{ \y:T, t }>
  | FI_If1 : forall t1 t2 t3, free_in x t1 ->
      free_in x <{ if t1 then t2 else t3 }>
  | FI_If2 : forall t1 t2 t3, free_in x t2 ->
      free_in x <{ if t1 then t2 else t3 }>
  | FI_If3 : forall t1 t2 t3, free_in x t3 ->
      free_in x <{ if t1 then t2 else t3 }>.

Definition closed (t : tm) : Prop := forall x, ~ free_in x t.

Definition renv := string -> tm.

Definition rupdate (rho : renv) (x : string) (s : tm) : renv :=
  fun y => if String.eqb x y then s else rho y.

Fixpoint msubst (rho : renv) (t : tm) : tm :=
  match t with
  | tm_var x => rho x
  | <{ t1 t2 }> => tm_app (msubst rho t1) (msubst rho t2)
  | <{ \x:T, t1 }> =>
      tm_abs x T (msubst (rupdate rho x (tm_var x)) t1)
  | <{ true }> => <{ true }>
  | <{ false }> => <{ false }>
  | <{ if t1 then t2 else t3 }> =>
      tm_if (msubst rho t1) (msubst rho t2) (msubst rho t3)
  end.

Fixpoint R (T : ty) (t : tm) : Prop :=
  match T with
  | Ty_Bool => halts t
  | Ty_Arrow T1 T2 =>
      halts t /\ forall s, closed s -> R T1 s -> halts (tm_app t s)
  end.

Lemma R_halts : forall T t, R T t -> halts t.
Proof.
  intros T t H; destruct T; simpl in H.
  - exact H.
  - exact (proj1 H).
Qed.

Definition closed_env (rho : renv) : Prop := forall x, closed (rho x).

Definition sem_env (rho : renv) (Gamma : context) : Prop :=
  forall x T, Gamma x = Some T -> R T (rho x).

Lemma free_in_typing : forall Gamma t T x,
  <{ Gamma |-- t \in T }> -> free_in x t ->
  exists U, Gamma x = Some U.
Proof.
  intros Gamma t T x Hty.
  induction Hty; intros Hfree; inversion Hfree; subst; eauto.
  - destruct (IHHty H3) as [U HU].
    unfold update in HU.
    destruct (String.eqb x0 x) eqn:E.
    + apply String.eqb_eq in E; subst; contradiction.
    + exists U; exact HU.
Qed.

Lemma rupdate_same : forall rho x a b,
  rupdate (rupdate rho x a) x b = rupdate rho x b.
Proof.
  intros rho x a b; apply functional_extensionality; intros y.
  unfold rupdate.
  destruct (String.eqb x y); reflexivity.
Qed.

Lemma rupdate_comm : forall rho x y a b,
  x <> y ->
  rupdate (rupdate rho x a) y b = rupdate (rupdate rho y b) x a.
Proof.
  intros rho x y a b Hxy; apply functional_extensionality; intros z.
  unfold rupdate.
  destruct (String.eqb y z) eqn:Eyz;
    destruct (String.eqb x z) eqn:Exz; simpl.
  - apply String.eqb_eq in Eyz; apply String.eqb_eq in Exz; subst; contradiction.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma msubst_agree : forall rho1 rho2 t,
  (forall x, free_in x t -> rho1 x = rho2 x) ->
  msubst rho1 t = msubst rho2 t.
Proof.
  intros rho1 rho2 t; revert rho1 rho2.
  induction t as [v | t1 IH1 t2 IH2 | y T b IH |
                   | | t1 IH1 t2 IH2 t3 IH3];
    intros rho1 rho2 Hagree; simpl.
  - apply Hagree; apply FI_Var.
  - f_equal.
    + apply IH1; intros x Hx; apply Hagree; apply FI_AppL; exact Hx.
    + apply IH2; intros x Hx; apply Hagree; apply FI_AppR; exact Hx.
  - f_equal; apply IH; intros z Hz.
    unfold rupdate.
    destruct (String.eqb y z) eqn:E.
    + reflexivity.
    + apply Hagree; apply FI_Abs.
      * apply String.eqb_neq in E; congruence.
      * exact Hz.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply IH1; intros x Hx; apply Hagree; apply FI_If1; exact Hx.
    + apply IH2; intros x Hx; apply Hagree; apply FI_If2; exact Hx.
    + apply IH3; intros x Hx; apply Hagree; apply FI_If3; exact Hx.
Qed.

Lemma msubst_rupdate_closed : forall rho y s,
  closed s ->
  msubst (rupdate rho y (tm_var y)) s = msubst rho s.
Proof.
  intros rho y s Hs; apply msubst_agree; intros z Hz.
  unfold rupdate.
  destruct (String.eqb y z) eqn:E.
  - apply String.eqb_eq in E; subst.
    exfalso; apply (Hs z); exact Hz.
  - reflexivity.
Qed.

Lemma msubst_id : forall t,
  msubst (fun x => tm_var x) t = t.
Proof.
  induction t as [v | t1 IH1 t2 IH2 | y T b IH |
                   | | t1 IH1 t2 IH2 t3 IH3]; simpl.
  - reflexivity.
  - rewrite IH1, IH2; reflexivity.
  - f_equal.
    assert (E : rupdate (fun x => tm_var x) y (tm_var y) =
      (fun x => tm_var x)).
    { apply functional_extensionality; intros z; unfold rupdate.
      destruct (String.eqb y z) eqn:Eyz.
      - apply String.eqb_eq in Eyz; subst; reflexivity.
      - reflexivity. }
    rewrite E; apply IH.
  - reflexivity.
  - reflexivity.
  - rewrite IH1, IH2, IH3; reflexivity.
Qed.

Lemma msubst_closed_identity : forall rho s,
  closed s -> msubst rho s = s.
Proof.
  intros rho s Hs.
  assert (E : msubst rho s = msubst (fun x => tm_var x) s).
  { apply msubst_agree; intros x Hx.
    exfalso; apply (Hs x); exact Hx. }
  rewrite E; apply msubst_id.
Qed.

Lemma msubst_subst : forall rho x s t,
  closed s ->
  msubst rho (subst x s t) =
  msubst (rupdate rho x (msubst rho s)) t.
Proof.
  intros rho x s t; revert rho x s.
  induction t as [v | t1 IH1 t2 IH2 | y T b IH |
                   | | t1 IH1 t2 IH2 t3 IH3];
    intros rho x s Hs; simpl.
  - destruct (String.eqb x v) eqn:E; unfold rupdate; rewrite E; reflexivity.
  - rewrite IH1, IH2; auto.
  - destruct (String.eqb x y) eqn:E.
    + apply String.eqb_eq in E; subst.
      rewrite rupdate_same; reflexivity.
    + simpl.
      f_equal.
      rewrite rupdate_comm; [ | apply String.eqb_neq in E; exact E ].
      rewrite <- (msubst_rupdate_closed rho y s Hs).
      apply IH; auto.
  - reflexivity.
  - reflexivity.
  - rewrite IH1, IH2, IH3; auto.
Qed.

Lemma subst_closed_except : forall bad x s t,
  (forall z, free_in z t -> In z bad) ->
  ~ In x bad -> subst x s t = t.
Proof.
  intros bad x s t; revert bad x s.
  induction t as [v | t1 IH1 t2 IH2 | y T b IH |
                   | | t1 IH1 t2 IH2 t3 IH3];
    intros bad x s Hfree Hx; simpl.
  - destruct (String.eqb x v) eqn:E.
    + apply String.eqb_eq in E; subst; exfalso; apply Hx; apply Hfree; apply FI_Var.
    + reflexivity.
  - f_equal.
    + apply IH1 with (bad := bad) (x := x) (s := s).
      * intros z Hz; apply Hfree; apply FI_AppL; exact Hz.
      * exact Hx.
    + apply IH2 with (bad := bad) (x := x) (s := s).
      * intros z Hz; apply Hfree; apply FI_AppR; exact Hz.
      * exact Hx.
  - destruct (String.eqb x y) eqn:E; [reflexivity |].
    f_equal.
    apply IH with (bad := y :: bad) (x := x) (s := s).
    + intros z Hz.
      simpl.
      destruct (classic (z = y)); [left; symmetry; assumption | right].
      apply Hfree; apply FI_Abs; [assumption | exact Hz].
    + intro Hin; inversion Hin; subst; [apply String.eqb_neq in E; contradiction | eauto].
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply IH1 with (bad := bad) (x := x) (s := s).
      * intros z Hz; apply Hfree; apply FI_If1; exact Hz.
      * exact Hx.
    + apply IH2 with (bad := bad) (x := x) (s := s).
      * intros z Hz; apply Hfree; apply FI_If2; exact Hz.
      * exact Hx.
    + apply IH3 with (bad := bad) (x := x) (s := s).
      * intros z Hz; apply Hfree; apply FI_If3; exact Hz.
      * exact Hx.
Qed.

Lemma subst_msubst_gen : forall bad rho x s t,
  (forall z, ~ In z bad -> closed (rho z)) ->
  (forall z, In z bad -> rho z = tm_var z) ->
  In x bad ->
  subst x s (msubst rho t) = msubst (rupdate rho x s) t.
Proof.
  intros bad rho x s t; revert bad rho x s.
  induction t as [v | t1 IH1 t2 IH2 | y T b IH |
                   | | t1 IH1 t2 IH2 t3 IH3];
    intros bad rho x s Hclosed Hbad Hx; simpl.
  - destruct (String.eqb x v) eqn:E.
    + apply String.eqb_eq in E; subst.
      rewrite (Hbad v Hx); unfold rupdate; rewrite String.eqb_refl.
      simpl; rewrite String.eqb_refl; reflexivity.
    + destruct (classic (In v bad)) as [Hv | Hv].
      * unfold rupdate; rewrite E; rewrite (Hbad v Hv); simpl; rewrite E; reflexivity.
      * assert (Esub : subst x s (rho v) = rho v).
        { apply subst_closed_except with (bad := nil) (x := x) (s := s).
          - intros z Hz; exfalso; apply ((Hclosed v Hv) z); exact Hz.
          - intros Hz; inversion Hz.
          }
        rewrite Esub; unfold rupdate; rewrite E; reflexivity.
  - f_equal.
    + apply IH1 with (bad := bad) (rho := rho) (x := x) (s := s); auto.
    + apply IH2 with (bad := bad) (rho := rho) (x := x) (s := s); auto.
  - destruct (String.eqb x y) eqn:E.
    + apply String.eqb_eq in E; subst; rewrite rupdate_same; reflexivity.
    + simpl; f_equal.
      rewrite rupdate_comm; [ | apply String.eqb_neq in E; exact E ].
      apply IH with (bad := y :: bad)
        (rho := rupdate rho y (tm_var y)) (x := x) (s := s).
      * intros z Hz; unfold rupdate.
        destruct (String.eqb y z) eqn:Eyz.
        -- apply String.eqb_eq in Eyz; subst.
           exfalso; apply Hz; simpl; left; reflexivity.
        -- apply Hclosed; intro Hin; apply Hz; right; exact Hin.
      * intros z Hz; unfold rupdate.
        destruct Hz as [-> | Hz].
        -- rewrite String.eqb_refl; reflexivity.
        -- destruct (String.eqb y z) eqn:Eyz.
           ++ apply String.eqb_eq in Eyz; subst; reflexivity.
           ++ apply Hbad; exact Hz.
      * simpl; right; exact Hx.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply IH1 with (bad := bad) (rho := rho) (x := x) (s := s); auto.
    + apply IH2 with (bad := bad) (rho := rho) (x := x) (s := s); auto.
    + apply IH3 with (bad := bad) (rho := rho) (x := x) (s := s); auto.
Qed.

Lemma subst_msubst : forall rho x s t,
  closed_env rho ->
  subst x s (msubst (rupdate rho x (tm_var x)) t) =
  msubst (rupdate rho x s) t.
Proof.
  intros rho x s t Hrho.
  rewrite <- (rupdate_same rho x (tm_var x) s).
  apply (subst_msubst_gen (x :: nil) (rupdate rho x (tm_var x)) x s t).
  - intros z Hz.
    unfold rupdate.
    destruct (String.eqb x z) eqn:E.
    + apply String.eqb_eq in E; subst; exfalso; apply Hz; simpl; left; reflexivity.
    + apply Hrho.
  - intros z Hz; destruct Hz as [-> | Hz]; [unfold rupdate; rewrite String.eqb_refl; reflexivity | inversion Hz].
  - simpl; left; reflexivity.
Qed.

Lemma R_bool_true : R Ty_Bool <{ true }>.
Proof.
  exists <{ true }>; split; [constructor | constructor].
Qed.

Lemma R_bool_false : R Ty_Bool <{ false }>.
Proof.
  exists <{ false }>; split; [constructor | constructor].
Qed.

Lemma multi_trans : forall a b c, a -->* b -> b -->* c -> a -->* c.
Proof.
  intros a b c Hab Hbc; induction Hab; eauto using multi_step.
Qed.

Lemma multi_app2 : forall f a b,
  value f -> a -->* b -> <{ f a }> -->* <{ f b }>.
Proof.
  intros f a b Hf H; induction H.
  - constructor.
  - eapply multi_step; [apply ST_App2; [exact Hf | exact H] | exact IHmulti].
Qed.

Lemma multi_if : forall a b t1 t2,
  a -->* b ->
  <{ if a then t1 else t2 }> -->* <{ if b then t1 else t2 }>.
Proof.
  intros a b t1 t2 H; induction H.
  - constructor.
  - eapply multi_step; [apply ST_If; exact H | exact IHmulti].
Qed.

Lemma R_value : forall T s v,
  R T s -> s -->* v -> value v -> R T v.
Proof.
  intros T s v Hs Hsv Hv; destruct T; simpl in *.
  - exists v; split; [constructor | exact Hv].
  - split.
    + exists v; split; [constructor | exact Hv].
    + intros a Hca Ha.
      destruct (proj2 Hs a Hca Ha) as [w [Haw Hw]].
      exists w; split.
      * eapply multi_trans; [apply multi_app2; [constructor | exact Hsv] | exact Haw].
      * exact Hw.
Qed.

Lemma free_in_msubst : forall rho t x,
  free_in x (msubst rho t) ->
  exists y, free_in y t /\ free_in x (rho y).
Proof.
  intros rho t; revert rho.
  induction t as [v | t1 IH1 t2 IH2 | y T b IH |
                   | | t1 IH1 t2 IH2 t3 IH3]; simpl; intros rho x H.
  - exists v; split; [apply FI_Var | exact H].
  - inversion H; subst.
    + destruct (IH1 rho _ H1) as [z [Hz Hz']].
      exists z; split; [apply FI_AppL; exact Hz | exact Hz'].
    + destruct (IH2 rho _ H1) as [z [Hz Hz']].
      exists z; split; [apply FI_AppR; exact Hz | exact Hz'].
  - inversion H; subst.
    specialize (IH (rupdate rho y (tm_var y)) _ H4).
    destruct IH as [z [Hz Hz']].
    destruct (String.eqb y z) eqn:E.
    + apply String.eqb_eq in E; subst.
      unfold rupdate in Hz'.
      destruct (String.eqb z z) eqn:E0.
      * simpl in Hz'; inversion Hz'.
        try (exfalso; apply H2; congruence).
      * apply String.eqb_neq in E0; contradiction.
    + exists z; split.
      * apply FI_Abs.
        intro Ezy.
        exact ((proj1 (String.eqb_neq y z)) E (eq_sym Ezy)).
        exact Hz.
      * unfold rupdate in Hz'.
        rewrite E in Hz'; exact Hz'.
  - inversion H.
  - inversion H.
  - inversion H; subst.
    + destruct (IH1 rho _ H1) as [z [Hz Hz']].
      exists z; split; [apply FI_If1; exact Hz | exact Hz'].
    + destruct (IH2 rho _ H1) as [z [Hz Hz']].
      exists z; split; [apply FI_If2; exact Hz | exact Hz'].
    + destruct (IH3 rho _ H1) as [z [Hz Hz']].
      exists z; split; [apply FI_If3; exact Hz | exact Hz'].
Qed.

Lemma closed_msubst_typed : forall Gamma t T rho,
  <{ Gamma |-- t \in T }> ->
  closed_env rho -> sem_env rho Gamma ->
  closed (msubst rho t).
Proof.
  intros Gamma t T rho Hty Hrho Henv x Hfree.
  apply free_in_msubst in Hfree.
  destruct Hfree as [y [Hy Hz]].
  destruct (free_in_typing Gamma t T y Hty Hy) as [U HU].
  exact ((proj1 (Henv y U HU)) x Hz).
Qed.

Lemma closed_abs_msubst : forall Gamma x T1 t T2 rho,
  <{ x |-> T1 ; Gamma |-- t \in T2 }> ->
  closed_env rho -> sem_env rho Gamma ->
  closed (msubst rho (tm_abs x T1 t)).
Proof.
  intros Gamma x T1 t T2 rho Hty Hrho Henv z Hfree.
  simpl in Hfree.
  inversion Hfree; subst.
  apply free_in_msubst in H3.
  destruct H3 as [y [Hy Hz]].
  destruct (free_in_typing (update Gamma x T1) t T2 y Hty Hy) as [U HU].
  unfold rupdate in Hz.
  destruct (String.eqb x y) eqn:E.
  - apply String.eqb_eq in E; subst.
    simpl in Hz; inversion Hz; subst; contradiction.
  - unfold update in HU; rewrite E in HU.
    eapply ((proj1 (Henv y U HU)) z); eauto.
Qed.

Lemma fundamental : forall Gamma t T,
  <{ Gamma |-- t \in T }> ->
  forall rho, closed_env rho -> sem_env rho Gamma -> R T (msubst rho t).
Proof.
  intros Gamma t T Hty.
  induction Hty; intros rho Hrho Henv.
  - unfold sem_env in Henv; simpl; apply Henv; assumption.
  - split.
    + apply closed_abs_msubst with (Gamma := Gamma) (T1 := T1)
        (T2 := T2); assumption.
    + simpl; intros s Hs.
      assert (Hclosed_s : closed s).
      { apply R_closed with (T := T1); exact Hs. }
      assert (Hrho' : closed_env (rupdate rho x s)).
      { unfold closed_env; intros y; unfold rupdate.
        destruct (String.eqb x y); auto. }
      assert (Henv' : sem_env (rupdate rho x s) (update Gamma x T1)).
      { unfold sem_env; intros y U HU; unfold update in HU.
        destruct (String.eqb x y) eqn:E.
        - apply String.eqb_eq in E; subst; simpl in HU; inversion HU; subst U.
          unfold rupdate; rewrite String.eqb_refl; exact Hs.
        - unfold rupdate; rewrite E; apply Henv; exact HU. }
      rewrite msubst_subst with (rho := rupdate rho x (tm_var x))
        (x := x) (s := s) (t := t); auto.
      apply IHHty; assumption.
  - simpl.
    destruct (IHHty1 rho Hrho Henv) as [Hc1 Hr1].
    destruct (IHHty2 rho Hrho Henv) as [Hc2 Hr2].
    split.
    + intros x H; inversion H; eauto.
    + simpl in Hr1; apply Hr1; exact Hr2.
  - apply R_bool_true.
  - apply R_bool_false.
  - destruct (IHHty1 rho Hrho Henv) as [Hc1 Hr1].
    destruct (IHHty2 rho Hrho Henv) as [Hc2 Hr2].
    destruct (IHHty3 rho Hrho Henv) as [Hc3 Hr3].
    split.
    + intros x H; inversion H; eauto.
    + simpl in Hr1.
      destruct Hr1 as [v [Hmulti Hv]].
      inversion Hv; subst.
      * eexists; split; eauto using multi_refl.
      * eexists; split; eauto using multi_refl.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  halts t.
Proof.
  (* The proof is supplied below. *)
Admitted.

End STLCCBVNormalizationTask.
