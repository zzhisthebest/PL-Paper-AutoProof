(** STLC call-by-value normalization benchmark task. *)

From Stdlib Require Import Strings.String List FunctionalExtensionality.

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

Inductive closed_in : list string -> tm -> Prop :=
  | CI_Var : forall xs x, In x xs -> closed_in xs (tm_var x)
  | CI_App : forall xs t1 t2,
      closed_in xs t1 -> closed_in xs t2 -> closed_in xs <{ t1 t2 }>
  | CI_Abs : forall xs x T t,
      closed_in (x :: xs) t -> closed_in xs <{ \x:T, t }>
  | CI_True : forall xs, closed_in xs <{ true }>
  | CI_False : forall xs, closed_in xs <{ false }>
  | CI_If : forall xs t1 t2 t3,
      closed_in xs t1 -> closed_in xs t2 -> closed_in xs t3 ->
      closed_in xs <{ if t1 then t2 else t3 }>.

Definition closed (t : tm) : Prop := closed_in nil t.

Lemma closed_in_weaken : forall xs ys t,
    (forall x, In x xs -> In x ys) -> closed_in xs t -> closed_in ys t.
Proof.
  intros xs ys t Hsub Hc. revert ys Hsub. induction Hc; intros ys Hsub.
  - constructor. eauto.
  - constructor; eauto.
  - constructor. apply IHHc. intros z Hz. simpl in Hz.
    destruct Hz as [<-|Hz]. simpl; auto. simpl; right; eauto.
  - constructor.
  - constructor.
  - constructor; eauto.
Qed.

Lemma closed_in_subst : forall xs x s t,
    closed_in (x :: xs) t -> closed s -> closed_in xs (subst x s t).
Proof.
  intros xs x s t. revert xs. induction t; intros xs Ht Hs.
  - simpl. inversion Ht as [ys y Hy | | | | | ]. destruct (String.eqb x s0) eqn:E.
    + apply closed_in_weaken with (xs := nil).
      * intros z Hz; contradiction.
      * apply Hs.
    + constructor. simpl in Hy. destruct Hy as [<-|Hy].
      * exfalso. rewrite String.eqb_refl in E. discriminate.
      * exact Hy.
  - simpl. inversion Ht. constructor; [apply IHt1 | apply IHt2]; assumption.
  - simpl. inversion Ht. destruct (String.eqb x s0) eqn:E.
    + apply String.eqb_eq in E. subst s0. constructor.
      apply closed_in_weaken with (xs := x :: x :: xs).
      * intros z Hz. simpl in Hz. destruct Hz as [<-|[<-|Hz]].
        -- simpl; left; exact (eq_sym E).
        -- simpl; left; exact (eq_sym E).
        -- simpl; right; exact Hz.
      * rewrite <- E in H1. exact H1.
    + constructor. apply IHt.
      apply closed_in_weaken with (xs := s0 :: x :: xs).
      * intros z Hz. simpl in Hz. destruct Hz as [<-|[<-|Hz]].
        -- simpl; auto.
        -- simpl; auto.
        -- simpl; right; right; exact Hz.
      * exact H1.
      * exact Hs.
  - constructor.
  - constructor.
  - simpl. inversion Ht. constructor; [apply IHt1 | apply IHt2 | apply IHt3]; assumption.
Qed.

Lemma subst_noop : forall xs x s t,
    closed_in xs t -> ~ In x xs -> subst x s t = t.
Proof.
  intros xs x s t. revert xs. induction t; intros xs Ht Hnot.
  - simpl. inversion Ht as [ys y Hy | | | | | ].
    destruct (String.eqb x y) eqn:E.
    + exfalso. apply Hnot. apply String.eqb_eq in E. rewrite E, H0. exact Hy.
    + rewrite <- H0. rewrite E. reflexivity.
  - simpl. inversion Ht. f_equal; [apply (IHt1 xs) | apply (IHt2 xs)]; assumption.
  - simpl. inversion Ht. destruct (String.eqb x s0) eqn:E.
    + reflexivity.
    + f_equal. apply (IHt (s0 :: xs)).
      * exact H1.
      * intro Hz. apply Hnot. simpl in Hz. destruct Hz as [<-|Hz].
        -- rewrite String.eqb_refl in E. discriminate.
        -- exact Hz.
  - reflexivity.
  - reflexivity.
  - simpl. inversion Ht. f_equal; [apply (IHt1 xs) | apply (IHt2 xs) | apply (IHt3 xs)]; assumption.
Qed.

Lemma closed_subst_noop : forall x s t, closed t -> subst x s t = t.
Proof.
  intros x s t H. apply subst_noop with (xs := nil); auto.
Qed.

Definition env := string -> tm.
Definition env_update (rho : env) (x : string) (s : tm) : env :=
  fun y => if String.eqb x y then s else rho y.

Fixpoint interp (rho : env) (t : tm) : tm :=
  match t with
  | tm_var x => rho x
  | tm_app t1 t2 => tm_app (interp rho t1) (interp rho t2)
  | tm_abs x T t1 => tm_abs x T (interp (env_update rho x (tm_var x)) t1)
  | tm_true => <{ true }>
  | tm_false => <{ false }>
  | tm_if t1 t2 t3 =>
      tm_if (interp rho t1) (interp rho t2) (interp rho t3)
  end.

Lemma interp_id : forall t, interp (fun x => tm_var x) t = t.
Proof.
  induction t; simpl; try rewrite IHt; try rewrite IHt1; try rewrite IHt2;
    try rewrite IHt3; auto.
  - f_equal. assert (E : env_update (fun x => tm_var x) s (tm_var s) =
      (fun x => tm_var x)).
    { apply functional_extensionality. intro y. unfold env_update.
      destruct (String.eqb s y) eqn:H.
      - apply String.eqb_eq in H. subst y. reflexivity.
      - apply String.eqb_neq in H. reflexivity. }
    rewrite E. exact IHt.
Qed.

Lemma interp_closed_in : forall xs rho t,
    (forall x, In x xs -> rho x = tm_var x) ->
    (forall x, ~ In x xs -> closed (rho x)) ->
    closed_in xs (interp rho t).
Proof.
  intros xs rho t. revert xs rho. induction t; intros xs rho Hbound Hclosed; simpl.
  - destruct (in_dec String.string_dec s xs) as [Hin|Hnin].
    + rewrite (Hbound s Hin). constructor; exact Hin.
    + apply closed_in_weaken with (xs := nil).
      * intros z Hz; contradiction.
      * apply Hclosed; exact Hnin.
  - constructor; [apply IHt1 | apply IHt2]; assumption.
  - constructor. apply IHt.
    + intros z Hz. simpl in Hz. destruct Hz as [<-|Hz].
      * unfold env_update. rewrite String.eqb_refl. reflexivity.
      * destruct (String.eqb s z) eqn:E.
        -- apply String.eqb_eq in E. subst z. unfold env_update. rewrite String.eqb_refl; reflexivity.
        -- unfold env_update. rewrite E. apply Hbound; exact Hz.
    + intros z Hz. destruct (String.eqb s z) eqn:E.
      * apply String.eqb_eq in E. subst z. exfalso. apply Hz. simpl; auto.
      * unfold env_update. rewrite E. apply Hclosed. intro Hz'. apply Hz. simpl; right; exact Hz'.
  - constructor.
  - constructor.
  - constructor; [apply IHt1 | apply IHt2 | apply IHt3]; assumption.
Qed.

Lemma interp_closed : forall rho t,
    (forall x, closed (rho x)) -> closed (interp rho t).
Proof.
  intros rho t H. apply interp_closed_in with (xs := nil); auto.
  intros x Hx; contradiction.
Qed.

Fixpoint R (T : ty) (t : tm) : Prop :=
  match T with
  | Ty_Bool => t -->* <{ true }> \/ t -->* <{ false }>
  | Ty_Arrow A B =>
      exists x U b, t -->* <{ \x:U, b }> /\
        (forall s, R A s -> R B (<{ [x:=s] b }>))
  end.

Lemma multi_trans : forall t1 t2 t3, t1 -->* t2 -> t2 -->* t3 -> t1 -->* t3.
Proof.
  intros t1 t2 t3 H12 H23. induction H12; eauto using multi_step.
Qed.

Lemma R_back : forall T t t', t -->* t' -> R T t' -> R T t.
Proof.
  intros T t t' Hstep. destruct T as [|A B]; simpl; intros H.
  - destruct H as [H|H]; [left|right]; eapply multi_trans; eauto.
  - destruct H as [x [U [b [Habs Hbody]]]].
    exists x, U, b. split; [eapply multi_trans; eauto|exact Hbody].
Qed.

Lemma R_value : forall T t, R T t ->
    exists v, t -->* v /\ value v /\ R T v.
Proof.
  intros T t HR. destruct T as [|A B]; simpl in HR.
  - destruct HR as [H|H].
    + exists <{ true }>. split; [exact H|]. split; [apply v_true|].
      left; apply multi_refl.
    + exists <{ false }>. split; [exact H|]. split; [apply v_false|].
      right; apply multi_refl.
  - destruct HR as [x [U [b [H Hbody]]]].
    exists <{ \x:U, b }>. split; [exact H|]. split; [apply v_abs|].
    exists x, U, b; split; [apply multi_refl|exact Hbody].
Qed.

Lemma multi_app1 : forall t1 t1' t2,
    t1 -->* t1' -> <{ t1 t2 }> -->* <{ t1' t2 }>.
Proof.
  intros t1 t1' t2 H. induction H; eauto using multi_refl, multi_step, ST_App1.
Qed.

Lemma multi_app2 : forall v t2 t2', value v ->
    t2 -->* t2' -> <{ v t2 }> -->* <{ v t2' }>.
Proof.
  intros v t2 t2' Hv H. induction H; eauto using multi_refl, multi_step, ST_App2.
Qed.

Lemma multi_if_true : forall t1 t2 t,
    t -->* <{ true }> -> <{ if t then t1 else t2 }> -->* t1.
Proof.
  intros t1 t2 t H. apply multi_trans with (t2 := <{ if true then t1 else t2 }>).
  - induction H; eauto using multi_refl, multi_step, ST_If.
  - apply multi_step with (y := t1); [apply ST_IfTrue|constructor].
Qed.

Lemma multi_if_false : forall t1 t2 t,
    t -->* <{ false }> -> <{ if t then t1 else t2 }> -->* t2.
Proof.
  intros t1 t2 t H. apply multi_trans with (t2 := <{ if false then t1 else t2 }>).
  - induction H; eauto using multi_refl, multi_step, ST_If.
  - apply multi_step with (y := t2); [apply ST_IfFalse|constructor].
Qed.

Definition good (rho : env) (xs : list string) : Prop :=
  (forall y, In y xs -> rho y = tm_var y) /\
  (forall y, ~ In y xs -> closed (rho y)).

Lemma interp_subst_gen : forall xs rho x s t,
    ~ In x xs -> good rho xs -> closed s ->
    interp (env_update rho x s) t =
      subst x s (interp (env_update rho x (tm_var x)) t).
Proof.
  intros xs rho x q t. revert xs rho x q. induction t;
    intros xs rho x q Hx Hg Hq; simpl.
  - destruct (String.eqb x s) eqn:E.
    + apply String.eqb_eq in E. subst s. unfold env_update.
      rewrite String.eqb_refl. simpl. rewrite String.eqb_refl. reflexivity.
    + destruct Hg as [Hb Hc].
      destruct (in_dec String.string_dec s xs) as [Hin|Hnin].
      * unfold env_update. rewrite (Hb s Hin). unfold subst.
        destruct (String.eqb x s) eqn:E'.
        -- discriminate E.
        -- rewrite E'. reflexivity.
      * unfold env_update.
        destruct (String.eqb x s) eqn:E'.
        -- destruct (String.eqb x x) eqn:E''.
           ++ unfold subst; rewrite E''; reflexivity.
           ++ rewrite String.eqb_refl in E''. discriminate.
        -- pose proof (closed_subst_noop x q (rho s) (Hc s Hnin)) as E0.
           rewrite E0. reflexivity.
  - f_equal.
    + apply (IHt1 xs rho x q); assumption.
    + apply (IHt2 xs rho x q); assumption.
  - destruct (String.eqb x s) eqn:E.
    + f_equal. assert (E0 :
          env_update (env_update rho x q) s (tm_var s) =
          env_update (env_update rho x (tm_var x)) s (tm_var s)).
      { apply String.eqb_eq in E. subst s. apply functional_extensionality. intro y.
        unfold env_update. destruct (String.eqb x y); reflexivity. }
      rewrite E0. reflexivity.
    + f_equal.
      assert (E1 : env_update (env_update rho x q) s (tm_var s) =
          env_update (env_update rho s (tm_var s)) x q).
      { apply functional_extensionality. intro y. unfold env_update.
        destruct (String.eqb s y) eqn:E1'.
        - apply String.eqb_eq in E1'. subst y. rewrite E. reflexivity.
        - destruct (String.eqb x y) eqn:E2'.
          + apply String.eqb_eq in E2'. subst y. reflexivity.
          + reflexivity. }
      assert (E2 : env_update (env_update rho x (tm_var x)) s (tm_var s) =
          env_update (env_update rho s (tm_var s)) x (tm_var x)).
      { apply functional_extensionality. intro y. unfold env_update.
        destruct (String.eqb s y) eqn:E1'.
        - apply String.eqb_eq in E1'. subst y. rewrite E. reflexivity.
        - destruct (String.eqb x y) eqn:E2'.
          + apply String.eqb_eq in E2'. subst y. reflexivity.
          + reflexivity. }
      rewrite E1, E2. apply (IHt (s :: xs) (env_update rho s (tm_var s)) x q).
      * intro Hz. simpl in Hz. destruct Hz as [<-|Hz].
        -- rewrite String.eqb_refl in E. discriminate.
        -- apply Hx. exact Hz.
      * split.
        -- intros y Hy. simpl in Hy. destruct Hy as [<-|Hy].
           ++ unfold env_update. rewrite String.eqb_refl. reflexivity.
           ++ unfold env_update. destruct (String.eqb s y) eqn:E'.
              ** apply String.eqb_eq in E'. subst y. reflexivity.
              ** apply (proj1 Hg); exact Hy.
        -- intros y Hy. unfold env_update. destruct (String.eqb s y) eqn:E'.
           ++ apply String.eqb_eq in E'. subst y. exfalso. apply Hy. simpl; auto.
           ++ apply (proj2 Hg). intro Hy'. apply Hy. simpl. right; exact Hy'.
      * exact Hq.
  - reflexivity.
  - reflexivity.
  - f_equal; [apply (IHt1 xs rho x q) | apply (IHt2 xs rho x q) |
              apply (IHt3 xs rho x q)]; assumption.
Qed.

Lemma interp_subst : forall rho x s t,
    (forall y, closed (rho y)) -> closed s ->
    interp (env_update rho x s) t =
      subst x s (interp (env_update rho x (tm_var x)) t).
Proof.
  intros rho x s t Hr Hs. apply interp_subst_gen with (xs := nil); auto.
  split; [intros; contradiction|intros; apply Hr].
Qed.

Definition env_ok (Gamma : context) (rho : env) : Prop :=
  forall x T, Gamma x = Some T -> R T (rho x) /\ closed (rho x).

Lemma env_ok_update : forall Gamma rho x T s,
    env_ok Gamma rho -> R T s -> closed s ->
    env_ok (update Gamma x T) (env_update rho x s).
Proof.
  intros Gamma rho x T s Hrho Hs Hcs y U H. unfold update in H.
  unfold env_update. destruct (String.eqb x y) eqn:E.
  - apply String.eqb_eq in E. subst y. inversion H. subst U. split; [exact Hs|exact Hcs].
  - specialize (Hrho y U H). split; [exact (proj1 Hrho)|].
    apply (proj2 Hrho).
Qed.

Lemma closed_step : forall t t', t --> t' -> closed t -> closed t'.
Proof.
  intros t t' Hs Hc. unfold closed in *.
  inversion Hs; inversion Hc; subst; eauto using CI_App, CI_If, closed_in_subst.
  all: repeat constructor; eauto using closed_in_subst.
Qed.

Lemma closed_multi : forall t t', t -->* t' -> closed t -> closed t'.
Proof.
  intros t t' H. induction H; eauto using closed_step.
Qed.

Lemma fundamental : forall Gamma t T,
    has_type Gamma t T -> forall rho, env_ok Gamma rho -> R T (interp rho t).
Proof.
  intros Gamma t T H. induction H; intros rho Hrho.
  - simpl. exact (proj1 (Hrho x T H)).
  - simpl. exists x, T1, t. split; [apply multi_refl|].
    intros s Hs Hcs. apply IH.
    apply env_ok_update; assumption.
  - simpl. pose proof (IH1 rho Hrho) as Hfun.
    pose proof (IH2 rho Hrho) as Harg.
    destruct (R_value T1 Harg) as [v [Hv [Hvv HRv]]].
    assert (Hcv : closed v). { eapply closed_multi; eauto using (proj2 (Hrho _ _ (eq_refl _))). }
    destruct Hfun as [xf [Uf [bf [Hf Hbody]]]].
    apply R_back with (t' := <{ [xf:=v] bf }>).
    + apply multi_trans with (t2 := tm_app (tm_abs xf Uf bf) (interp rho t2)).
      * apply multi_trans with (t2 := tm_app (tm_abs xf Uf bf) v).
        -- apply multi_trans with (t2 := tm_app (interp rho t1) (interp rho t2)).
           ++ apply multi_app1; exact Hf.
           ++ apply multi_app2; exact Hv.
        -- apply multi_step with (y := <{ [xf:=v] bf }>).
           ++ apply ST_AppAbs; exact Hvv.
           ++ apply multi_refl.
      * apply multi_refl.
    + apply Hbody; assumption.
  - simpl. left; apply multi_refl.
  - simpl. right; apply multi_refl.
  - simpl. pose proof (IH1 rho Hrho) as Hg.
    pose proof (IH2 rho Hrho) as H2.
    pose proof (IH3 rho Hrho) as H3.
    destruct Hg as [Hg|Hg].
    + apply R_back with (t' := interp rho t2).
      * apply multi_if_true; exact Hg.
      * exact H2.
    + apply R_back with (t' := interp rho t3).
      * apply multi_if_false; exact Hg.
      * exact H3.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  halts t.
Proof.
  intros t T H.
  pose proof (fundamental empty t T H (fun x => tm_var x)) as Hr.
  - unfold env_ok. intros x U Hx. discriminate.
  - rewrite interp_id in Hr.
    destruct (R_value T t Hr) as [v [Htv [Hval _]]].
    exists v; split; assumption.
Qed.

End STLCCBVNormalizationTask.
