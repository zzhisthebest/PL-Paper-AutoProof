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

Inductive free_in (x : string) : tm -> Prop :=
  | FI_Var : free_in x (tm_var x)
  | FI_App1 : forall t1 t2, free_in x t1 -> free_in x <{ t1 t2 }>
  | FI_App2 : forall t1 t2, free_in x t2 -> free_in x <{ t1 t2 }>
  | FI_If1 : forall t1 t2 t3, free_in x t1 -> free_in x <{ if t1 then t2 else t3 }>
  | FI_If2 : forall t1 t2 t3, free_in x t2 -> free_in x <{ if t1 then t2 else t3 }>
  | FI_If3 : forall t1 t2 t3, free_in x t3 -> free_in x <{ if t1 then t2 else t3 }>
  | FI_Abs : forall y T t, x <> y -> free_in x t -> free_in x <{ \y:T, t }>.

Definition closed_tm (t : tm) : Prop := forall x, ~ free_in x t.

Lemma update_eq : forall Gamma x T, update Gamma x T x = Some T.
Proof. intros; unfold update; rewrite String.eqb_refl; reflexivity. Qed.

Lemma update_neq : forall Gamma x y T, x <> y -> update Gamma x T y = Gamma y.
Proof. intros; unfold update; rewrite (proj2 (String.eqb_neq x y) H); reflexivity. Qed.

Lemma free_typing : forall Gamma t T x,
    <{ Gamma |-- t \in T }> -> free_in x t -> exists U, Gamma x = Some U.
Proof.
  intros Gamma t T x Hty; induction Hty; intro Hfree.
  - inversion Hfree; subst; eauto.
  - inversion Hfree; subst.
    assert (Hex : exists U, update Gamma x0 T1 x = Some U).
    { apply IHHty; assumption. }
    destruct Hex as [U HU].
    exists U. assert (Hneq : x0 <> x) by congruence.
    rewrite (update_neq Gamma x0 x T1 Hneq) in HU; exact HU.
  - inversion Hfree; subst; eauto.
  - inversion Hfree.
  - inversion Hfree.
  - inversion Hfree; subst; eauto.
Qed.

Lemma typed_closed : forall t T, <{ empty |-- t \in T }> -> closed_tm t.
Proof.
  intros t T Hty x Hfree.
  destruct (free_typing empty t T x Hty Hfree) as [U HU]. discriminate HU.
Qed.

Lemma subst_not_free : forall x s t, ~ free_in x t -> subst x s t = t.
Proof.
  intros x s t; induction t as [y|t1 IH1 t2 IH2|y T t IH| | |t1 IH1 t2 IH3 t3 IH4];
    intro Hnf; simpl.
  - destruct (String.eqb x y) eqn:E.
    + exfalso; apply Hnf; apply (proj1 (String.eqb_eq x y)) in E; subst y; constructor.
    + reflexivity.
  - f_equal; [apply IH1|apply IH2]; intro F; apply Hnf;
      [apply FI_App1|apply FI_App2]; exact F.
  - destruct (String.eqb x y) eqn:E.
    + apply (proj1 (String.eqb_eq x y)) in E; subst y; reflexivity.
    + f_equal. apply IH. intro F. apply Hnf.
      apply FI_Abs; [exact (proj1 (String.eqb_neq x y) E)|exact F].
  - reflexivity.
  - reflexivity.
  - f_equal; [apply IH1|apply IH3|apply IH4]; intro F; apply Hnf;
      [apply FI_If1|apply FI_If2|apply FI_If3]; exact F.
Qed.

Lemma subst_closed : forall x s t, closed_tm t -> subst x s t = t.
Proof. intros; apply subst_not_free; apply H. Qed.

Definition env_update (sigma : string -> tm) (x : string) (s : tm) : string -> tm :=
  fun y => if String.eqb x y then s else sigma y.

Fixpoint esubst (sigma : string -> tm) (t : tm) : tm :=
  match t with
  | tm_var x => sigma x
  | <{ t1 t2 }> => tm_app (esubst sigma t1) (esubst sigma t2)
  | <{ \x:T, t1 }> => tm_abs x T (esubst (env_update sigma x (tm_var x)) t1)
  | <{ true }> => <{ true }>
  | <{ false }> => <{ false }>
  | <{ if t1 then t2 else t3 }> =>
      tm_if (esubst sigma t1) (esubst sigma t2) (esubst sigma t3)
  end.

Lemma env_update_shadow : forall sigma x a b,
    env_update (env_update sigma x a) x b = env_update sigma x b.
Proof.
  intros; apply functional_extensionality; intro y; unfold env_update.
  destruct (String.eqb x y); reflexivity.
Qed.

Lemma env_update_comm : forall sigma x y a b, x <> y ->
    env_update (env_update sigma x a) y b = env_update (env_update sigma y b) x a.
Proof.
  intros; apply functional_extensionality; intro z; unfold env_update.
  destruct (String.eqb x z) eqn:Ex; destruct (String.eqb y z) eqn:Ey;
    try reflexivity.
  exfalso. apply H. rewrite (proj1 (String.eqb_eq x z) Ex),
    (proj1 (String.eqb_eq y z) Ey). reflexivity.
Qed.

Lemma subst_esubst : forall sigma x s t,
    (forall y, y <> x -> subst x s (sigma y) = sigma y) ->
    subst x s (esubst (env_update sigma x (tm_var x)) t) =
    esubst (env_update sigma x s) t.
Proof.
  intros sigma x s t; revert sigma x s;
  induction t as [y|t1 IH1 t2 IH2|y T t IH| | |t1 IH1 t2 IH3 t3 IH4];
    intros sigma x s Hfixed; simpl.
  - unfold env_update. destruct (String.eqb x y) eqn:E.
    + apply (proj1 (String.eqb_eq x y)) in E; subst y; simpl.
      rewrite String.eqb_refl; reflexivity.
    + apply Hfixed; intro Hyx; apply (proj1 (String.eqb_neq x y) E); symmetry; exact Hyx.
  - f_equal; [apply IH1|apply IH2]; exact Hfixed.
  - destruct (String.eqb x y) eqn:E.
    * apply (proj1 (String.eqb_eq x y)) in E; subst y.
      rewrite !env_update_shadow; reflexivity.
    * apply (proj1 (String.eqb_neq x y)) in E.
      rewrite (env_update_comm sigma x y (tm_var x) (tm_var y) E).
      rewrite (env_update_comm sigma x y s (tm_var y) E).
      f_equal. apply IH. intros z Hz. unfold env_update.
      destruct (String.eqb x z) eqn:Ez.
      + exfalso; apply Hz; apply (proj1 (String.eqb_eq x z)) in Ez; symmetry; exact Ez.
      + destruct (String.eqb y z) eqn:Ez';
        [ assert (Hxy : x <> y) by
            (intro Hxy; subst y; rewrite Ez in Ez'; discriminate);
          apply subst_not_free; intro F; inversion F; subst; contradiction
        | apply Hfixed; intro Hzx; apply (proj1 (String.eqb_neq x z) Ez);
          symmetry; exact Hzx ].
  - reflexivity.
  - reflexivity.
  - f_equal; [apply IH1|apply IH3|apply IH4]; exact Hfixed.
Qed.

Definition ctx_incl (Gamma Delta : context) : Prop :=
  forall x T, Gamma x = Some T -> Delta x = Some T.

Lemma typing_weaken : forall Gamma t T, <{ Gamma |-- t \in T }> ->
    forall Delta, ctx_incl Gamma Delta -> <{ Delta |-- t \in T }>.
Proof.
  intros Gamma t T Hty; induction Hty; intros Delta Hinc.
  - apply T_Var; apply Hinc; assumption.
  - apply T_Abs. apply IHHty. intros y U Hy.
    unfold update in Hy; destruct (String.eqb x y) eqn:E.
    * apply (proj1 (String.eqb_eq x y)) in E; subst y.
      inversion Hy; subst U; apply update_eq.
    * rewrite (update_neq Delta x y T1 (proj1 (String.eqb_neq x y) E)).
      apply Hinc. exact Hy.
  - eapply T_App; [eapply IHHty1; exact Hinc|eapply IHHty2; exact Hinc].
  - apply T_True.
  - apply T_False.
  - apply T_If; [apply IHHty1|apply IHHty2|apply IHHty3]; assumption.
Qed.

Lemma update_comm : forall Gamma x y S U, x <> y ->
    update (update Gamma x S) y U = update (update Gamma y U) x S.
Proof.
  intros; apply functional_extensionality; intro z; unfold update.
  destruct (String.eqb x z) eqn:Ex; destruct (String.eqb y z) eqn:Ey;
    try reflexivity.
  exfalso; apply H. rewrite (proj1 (String.eqb_eq x z) Ex),
    (proj1 (String.eqb_eq y z) Ey); reflexivity.
Qed.

Lemma typing_weaken_avoid : forall Gamma t T, <{ Gamma |-- t \in T }> ->
    forall Delta z S, ctx_incl Gamma Delta -> ~ free_in z t ->
    has_type (update Delta z S) t T.
Proof.
  intros Gamma t T Hty; induction Hty; intros Delta z S Hinc Hnf.
  - apply T_Var. unfold update. destruct (String.eqb x z) eqn:E.
    + apply (proj1 (String.eqb_eq x z)) in E; subst z.
      exfalso. apply Hnf. constructor.
    + assert (Hzx : z <> x).
      { intro Hzx; apply (proj1 (String.eqb_neq x z) E); symmetry; exact Hzx. }
      rewrite (proj2 (String.eqb_neq z x) Hzx).
      apply Hinc; assumption.
  - destruct (String.eqb x z) eqn:Ez.
    + apply (proj1 (String.eqb_eq x z)) in Ez; subst z.
      apply T_Abs. apply typing_weaken with (Gamma := update Gamma x T1).
      * assumption.
      * unfold ctx_incl; intros y U Hy. unfold update in Hy.
        destruct (String.eqb x y) eqn:E.
        -- apply (proj1 (String.eqb_eq x y)) in E; subst y.
           inversion Hy; subst U; apply update_eq.
        -- unfold update; rewrite (proj2 (String.eqb_neq x y)
           (proj1 (String.eqb_neq x y) E)); apply Hinc; exact Hy.
    + apply T_Abs.
      assert (Hbody : ~ free_in z t).
      { intro F; apply Hnf. apply FI_Abs;
        [ intro Hzx; apply (proj1 (String.eqb_neq x z) Ez); symmetry; exact Hzx
        | exact F ]. }
      rewrite <- (update_comm Delta x z T1 S (proj1 (String.eqb_neq x z) Ez)).
      eapply IHHty with (Delta := update Delta x T1) (z := z) (S := S).
      * unfold ctx_incl; intros y U Hy. unfold update in Hy.
        destruct (String.eqb x y) eqn:E.
        -- apply (proj1 (String.eqb_eq x y)) in E; subst y.
           inversion Hy; subst U; apply update_eq.
        -- unfold update; rewrite (proj2 (String.eqb_neq x y)
           (proj1 (String.eqb_neq x y) E)); apply Hinc; exact Hy.
      * exact Hbody.
  - assert (Hnf1 : ~ free_in z t1).
    { intro F; apply Hnf; apply FI_App1; exact F. }
    assert (Hnf2 : ~ free_in z t2).
    { intro F; apply Hnf; apply FI_App2; exact F. }
    eapply T_App; [apply IHHty1 with (Delta := Delta) (z := z) (S := S);
                    [exact Hinc|exact Hnf1]|
                   apply IHHty2 with (Delta := Delta) (z := z) (S := S);
                    [exact Hinc|exact Hnf2]].
  - apply T_True.
  - apply T_False.
  - assert (Hnf1 : ~ free_in z t1).
    { intro F; apply Hnf; apply FI_If1; exact F. }
    assert (Hnf2 : ~ free_in z t2).
    { intro F; apply Hnf; apply FI_If2; exact F. }
    assert (Hnf3 : ~ free_in z t3).
    { intro F; apply Hnf; apply FI_If3; exact F. }
    eapply T_If; [apply IHHty1 with (Delta := Delta) (z := z) (S := S);
                    [exact Hinc|exact Hnf1]|
                   apply IHHty2 with (Delta := Delta) (z := z) (S := S);
                    [exact Hinc|exact Hnf2]|
                   apply IHHty3 with (Delta := Delta) (z := z) (S := S);
                    [exact Hinc|exact Hnf3]].
Qed.

Definition env_avoid (sigma : string -> tm) : Prop :=
  forall x y, x <> y -> ~ free_in x (sigma y).

Lemma env_avoid_update : forall sigma x,
    env_avoid sigma -> env_avoid (env_update sigma x (tm_var x)).
Proof.
  intros sigma x Havoid a b Hab; unfold env_update.
  destruct (String.eqb x b) eqn:E.
  - apply (proj1 (String.eqb_eq x b)) in E; subst b.
    intro F; inversion F; subst; contradiction.
  - apply Havoid; exact Hab.
Qed.

Definition env_typed (Gamma Delta : context) (sigma : string -> tm) : Prop :=
  forall x T, Gamma x = Some T -> has_type Delta (sigma x) T.

Lemma esubst_typing : forall Gamma t T, <{ Gamma |-- t \in T }> ->
    forall Delta sigma, env_typed Gamma Delta sigma -> env_avoid sigma ->
    has_type Delta (esubst sigma t) T.
Proof.
  intros Gamma t T Hty; induction Hty; intros Delta sigma Henv Havoid; simpl.
  - exact (Henv x T H).
  - apply T_Abs. eapply IHHty with
      (Delta := update Delta x T1)
      (sigma := env_update sigma x (tm_var x)).
    intros y U Hy. unfold env_update.
    destruct (String.eqb x y) eqn:E.
    + apply (proj1 (String.eqb_eq x y)) in E; subst y.
      rewrite update_eq in Hy; inversion Hy; subst U.
      apply T_Var. apply update_eq.
    + assert (HyG : Gamma y = Some U).
      { rewrite (update_neq Gamma x y T1 (proj1 (String.eqb_neq x y) E)) in Hy.
        exact Hy. }
      eapply typing_weaken_avoid with (Gamma := Delta) (Delta := Delta)
        (z := x) (S := T1).
      * apply Henv; exact HyG.
      * intros q V Hq; exact Hq.
      * apply Havoid; exact (proj1 (String.eqb_neq x y) E).
  + apply env_avoid_update; exact Havoid.
  - eapply T_App; [apply IHHty1 with (Delta := Delta) (sigma := sigma);
                    [exact Henv|exact Havoid]|
                   apply IHHty2 with (Delta := Delta) (sigma := sigma);
                    [exact Henv|exact Havoid]].
  - apply T_True.
  - apply T_False.
  - apply T_If; [apply IHHty1|apply IHHty2|apply IHHty3]; assumption.
Qed.

Lemma subst_typing : forall Gamma x S t T s,
    <{ x |-> S; Gamma |-- t \in T }> ->
    <{ Gamma |-- s \in S }> ->
    <{ Gamma |-- [x:=s] t \in T }>.
Proof.
  intros Gamma x S t T s Hty; induction Hty; intro Hs; simpl.
  - unfold update in H; destruct (String.eqb x0 x) eqn:E.
    + apply (proj1 (String.eqb_eq x0 x)) in E; subst x0.
      inversion H; subst T0; exact Hs.
    + apply T_Var. rewrite (proj2 (String.eqb_neq x x0)
        (proj1 (String.eqb_neq x0 x) E)); exact H.
  - destruct (String.eqb x x0) eqn:E.
    + apply (proj1 (String.eqb_eq x x0)) in E; subst x0.
      apply T_Abs. exact Hty.
    + apply T_Abs. apply IHHty.
      * rewrite (update_comm Gamma x x0 S T1
          (proj1 (String.eqb_neq x x0) E)). exact Hty.
      * apply typing_weaken with (Gamma := Gamma); [exact Hs|].
        intros y U Hy; exact Hy.
  - apply T_App; [apply IHHty1|apply IHHty2]; assumption.
  - apply T_True.
  - apply T_False.
  - apply T_If; [apply IHHty1|apply IHHty2|apply IHHty3]; assumption.
Qed.

Lemma preservation_step : forall Gamma t t' T,
    <{ Gamma |-- t \in T }> -> t --> t' -> <{ Gamma |-- t' \in T }>.
Proof.
  intros Gamma t t' T Hty Hstep; induction Hstep.
  - inversion Hty as [| |? ? ? ? Hfun Harg| | |].
    eapply subst_typing; eauto.
  - inversion Hty; subst; eauto.
  - inversion Hty; subst; eauto.
  - inversion Hty; eauto.
  - inversion Hty; eauto.
  - inversion Hty; eauto.
Qed.

Lemma preservation_multi : forall Gamma t t' T,
    <{ Gamma |-- t \in T }> -> t -->* t' -> <{ Gamma |-- t' \in T }>.
Proof.
  intros Gamma t t' T Hty H; induction H; eauto using preservation_step.
Qed.

Lemma multi_trans : forall (X : Type) (Q : X -> X -> Prop) x y z,
    multi Q x y -> multi Q y z -> multi Q x z.
Proof.
  intros X Q x y z Hxy Hyz.
  induction Hxy as [x0 | x0 y0 z0 Hxy IH].
  - exact Hyz.
  - eapply multi_step; [exact Hxy|exact (IHIH Hyz)].
Qed.

Lemma multi_app1 : forall t1 t1' t2, t1 -->* t1' ->
    <{ t1 t2 }> -->* <{ t1' t2 }>.
Proof.
  intros t1 t1' t2 H; revert t2.
  induction H as [x0|x0 y0 z0 Hxy IH]; intro t2.
  - apply multi_refl.
  - eapply multi_step; [apply ST_App1; exact Hxy|apply IHIH].
Qed.

Lemma multi_app2 : forall v t2 t2', value v -> t2 -->* t2' ->
    <{ v t2 }> -->* <{ v t2' }>.
Proof.
  intros v t2 t2' Hv H.
  induction H as [x0|x0 y0 z0 Hxy IH].
  - apply multi_refl.
  - eapply multi_step; [apply ST_App2; [exact Hv|exact Hxy]|apply IHIH].
Qed.

Lemma multi_if : forall c c' t2 t3, c -->* c' ->
    <{ if c then t2 else t3 }> -->* <{ if c' then t2 else t3 }>.
Proof.
  intros c c' t2 t3 H; revert t2 t3.
  induction H as [x0|x0 y0 z0 Hxy IH]; intros t2 t3.
  - apply multi_refl.
  - eapply multi_step; [apply ST_If; exact Hxy|apply IHIH].
Qed.

Lemma if_to_true : forall c t2 t3, c -->* <{ true }> ->
    <{ if c then t2 else t3 }> -->* t2.
Proof.
  intros; eapply multi_trans; [apply multi_if; eassumption|].
  eapply multi_step; [apply ST_IfTrue|apply multi_refl].
Qed.

Lemma if_to_false : forall c t2 t3, c -->* <{ false }> ->
    <{ if c then t2 else t3 }> -->* t3.
Proof.
  intros; eapply multi_trans; [apply multi_if; eassumption|].
  eapply multi_step; [apply ST_IfFalse|apply multi_refl].
Qed.

Fixpoint R (T : ty) (t : tm) : Prop :=
  <{ empty |-- t \in T }> /\ halts t /\
  (match T with
   | Ty_Bool => True
   | Ty_Arrow T1 T2 => forall t1, R T1 t1 -> R T2 (tm_app t t1)
   end).

Lemma R_typing : forall T t, R T t -> <{ empty |-- t \in T }>.
Proof.
  intros T t H; destruct T; simpl in H; exact (proj1 H).
Qed.

Lemma value_bool : forall v, value v -> <{ empty |-- v \in Bool }> ->
    v = <{ true }> \/ v = <{ false }>.
Proof.
  intros v Hv; inversion Hv; intro Hty; try (inversion Hty).
  - left; reflexivity.
  - right; reflexivity.
Qed.

Lemma R_back : forall T t u, t -->* u -> <{ empty |-- t \in T }> ->
    R T u -> R T t.
Proof.
  induction T as [|T1 IH1 T2 IH2]; intros t u Hstep Hty Hru.
  - destruct Hru as [Huty [Hhalt _]]. split; [exact Hty|]. split.
    + destruct Hhalt as [v [Huv Hv]]; exists v; split;
        [eapply multi_trans; eassumption|exact Hv].
    + exact I.
  - destruct Hru as [Huty [Hhalt Hfun]]. split; [exact Hty|]. split.
    + destruct Hhalt as [v [Huv Hv]]; exists v; split;
        [eapply multi_trans; eassumption|exact Hv].
    + intros a Ha. apply IH2 with (u := <{ u a }>).
      * apply multi_app1; exact Hstep.
      * apply T_App with (T1 := T1); [exact Hty|apply R_typing with (T := T1); exact Ha].
      * apply Hfun; exact Ha.
Qed.

Lemma R_if : forall T c t2 t3, R Ty_Bool c -> R T t2 -> R T t3 ->
    <{ empty |-- if c then t2 else t3 \in T }> ->
    R T <{ if c then t2 else t3 }>.
Proof.
  induction T as [|T1 IH1 T2 IH2]; intros c t2 t3 Hc H2 H3 Hty.
  - destruct Hc as [Hcty [Hch _]]. split; [exact Hty|]. split.
    + destruct Hch as [v [Hcv Hv]]; destruct (value_bool v Hv Hcty) as [Heq|Heq].
      * subst v; exists <{ true }>; split; [apply if_to_true; exact Hcv|constructor].
      * subst v; exists <{ false }>; split; [apply if_to_false; exact Hcv|constructor].
    + exact I.
  - destruct Hc as [Hcty [Hch Hcf]]. destruct H2 as [H2ty [H2h H2f]].
    destruct H3 as [H3ty [H3h H3f]]. split; [exact Hty|]. split.
    + destruct Hch as [v [Hcv Hv]]; destruct (value_bool v Hv Hcty) as [Heq|Heq].
      * subst v; destruct H2h as [w [H2w Hw]]; exists w; split;
          [eapply multi_trans; [apply if_to_true; exact Hcv|exact H2w]|exact Hw].
      * subst v; destruct H3h as [w [H3w Hw]]; exists w; split;
          [eapply multi_trans; [apply if_to_false; exact Hcv|exact H3w]|exact Hw].
    + intros a Ha. destruct Hch as [v [Hcv Hv]].
      destruct (value_bool v Hv Hcty) as [Heq|Heq].
      * subst v; eapply R_back with (u := <{ t2 a }>).
        -- apply multi_app1; apply if_to_true; exact Hcv.
        -- apply T_App; [exact H2ty|apply R_typing with (T := T1); exact Ha].
        -- apply H2f; exact Ha.
      * subst v; eapply R_back with (u := <{ t3 a }>).
        -- apply multi_app1; apply if_to_false; exact Hcv.
        -- apply T_App; [exact H3ty|apply R_typing with (T := T1); exact Ha].
        -- apply H3f; exact Ha.
Qed.

Definition env_rel (Gamma : context) (sigma : string -> tm) : Prop :=
  (forall x T, Gamma x = Some T -> R T (sigma x)) /\
  (forall x, closed_tm (sigma x)).

Lemma env_rel_update : forall Gamma sigma x T a, env_rel Gamma sigma -> R T a ->
    env_rel (update Gamma x T) (env_update sigma x a).
Proof.
  intros Gamma sigma x T a [Hrel Hclosed] Ha; split.
  - intros y U Hy; unfold update in Hy; destruct (String.eqb x y) eqn:E.
    + apply (proj1 (String.eqb_eq x y)) in E; subst y; exact Ha.
    + apply Hrel; exact Hy.
  - intros y; unfold env_update; destruct (String.eqb x y) eqn:E.
    + apply typed_closed with (T := T). apply R_typing with (T := T); exact Ha.
    + apply Hclosed.
Qed.

Lemma fundamental : forall Gamma t T, <{ Gamma |-- t \in T }> ->
    forall sigma, env_rel Gamma sigma -> R T (esubst sigma t).
Proof.
  intros Gamma t T Hty; induction Hty; intros sigma Hsigma.
  - simpl; apply (proj1 Hsigma); assumption.
  - simpl. split.
    + apply esubst_typing with (Gamma := update Gamma x T1) (sigma := sigma); [assumption|].
      intros y U Hy; apply (proj1 (proj1 Hsigma)); exact Hy.
    + split.
      * exists <{ \x:T1, esubst (env_update sigma x (tm_var x)) t }>;
          split; [apply multi_refl|constructor].
      * intros a Ha.
        assert (Hbody : R T2 (esubst (env_update sigma x a) t)).
        { apply IHHty. apply env_rel_update; assumption. }
        destruct (proj2 (proj1 Ha)) as [v [Hav Hv]].
        eapply R_back with
          (t := <{ (\x:T1, esubst (env_update sigma x (tm_var x)) t) a }>)
          (u := esubst (env_update sigma x a) t).
        eapply multi_trans.
        { apply multi_app2; [constructor|exact Hav]. }
        eapply multi_trans.
        { eapply multi_step; [apply ST_AppAbs; exact Hv|apply multi_refl]. }
        rewrite (subst_esubst sigma x v t).
        2:{ intros y Hy; apply subst_closed; apply typed_closed with (T := _).
            apply (proj2 Hsigma). }
        apply multi_refl.
        apply T_App.
        -- This typing is the function component of the abstraction's relation.
        apply esubst_typing with (Gamma := Gamma) (sigma := sigma); [assumption|].
        intros y U Hy; apply (proj1 (proj1 Hsigma)); exact Hy.
        apply R_typing with (T := T1); exact Ha.
        exact Hbody.
  - simpl. apply R_back with (u := tm_app (esubst sigma t1) (esubst sigma t2)).
    + apply multi_refl.
    + apply T_App; [apply IHHty1|apply IHHty2]; exact Hsigma.
    + apply (IHHty1 sigma Hsigma).
  - simpl. split; [apply T_True|]. split.
    + exists <{ true }>; split; [apply multi_refl|constructor].
    + exact I.
  - simpl. split; [apply T_False|]. split.
    + exists <{ false }>; split; [apply multi_refl|constructor].
    + exact I.
  - simpl. apply R_if.
    + apply IHHty1; exact Hsigma.
    + apply IHHty2; exact Hsigma.
    + apply IHHty3; exact Hsigma.
    + apply esubst_typing with (Gamma := Gamma) (sigma := sigma); [assumption|].
      intros y U Hy; apply (proj1 (proj1 Hsigma)); exact Hy.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  halts t.
Proof.
  intros t T Hty.
  pose (sigma := fun _ : string => <{ true }>).
  assert (Henv : env_rel empty sigma).
  { split.
    - intros x U Hx; discriminate Hx.
    - intros x; unfold sigma; intros y Hy; inversion Hy. }
  assert (HR : R T (esubst sigma t)) by
    (apply fundamental with (Gamma := empty); assumption).
  unfold sigma in HR. simpl in HR. exact (proj2 (proj1 HR)).
Qed.

End STLCCBVNormalizationTask.
