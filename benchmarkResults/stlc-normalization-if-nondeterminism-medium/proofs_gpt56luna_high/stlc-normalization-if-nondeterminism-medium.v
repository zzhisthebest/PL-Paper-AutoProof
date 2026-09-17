(** STLC CBV strong-normalization benchmark, Medium variant.
    Features: if-nondeterminism. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Relations.Relation_Definitions Lia.
Import ListNotations.

Module STLCNormalizationIfNondeterminismMediumTask.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
      R x y ->
      multi R y z ->
      multi R x z.

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

  | tm_if : tm -> tm -> tm -> tm
  | tm_choice : tm -> tm -> tm.

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

Notation "'if' t1 'then' t2 'else' t3" := (tm_if t1 t2 t3)
  (in custom stlc_tm at level 200,
   t1 custom stlc_tm, t2 custom stlc_tm, t3 custom stlc_tm at level 200) : stlc_scope.
Notation "'choice' t1 'or' t2" := (tm_choice t1 t2)
  (in custom stlc_tm at level 200,
   t1 custom stlc_tm, t2 custom stlc_tm at level 200) : stlc_scope.

Fixpoint open_rec (k : nat) (u : tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => if Nat.eqb k i then u else tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_app t1 t2 => tm_app (open_rec k u t1) (open_rec k u t2)
  | tm_abs T t1 => tm_abs T (open_rec (S k) u t1)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (open_rec k u t1) (open_rec k u t2) (open_rec k u t3)
  | tm_choice t1 t2 => tm_choice (open_rec k u t1) (open_rec k u t2)
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
      lc_at k t1 -> lc_at k t2 -> lc_at k t3 -> lc_at k (tm_if t1 t2 t3)
  | lc_choice : forall k t1 t2,
      lc_at k t1 -> lc_at k t2 -> lc_at k (tm_choice t1 t2).

Definition locally_closed (t : tm) : Prop := lc_at 0 t.

Hint Constructors lc_at : core.

Inductive value : tm -> Prop :=
  | v_abs : forall T t,
      locally_closed (tm_abs T t) ->
      value (tm_abs T t)
  | v_true :
      value tm_true
  | v_false :
      value tm_false.

Hint Constructors value : core.

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
  | ST_ChoiceLeft : forall t1 t2,
      locally_closed t1 ->
      locally_closed t2 ->
      tm_choice t1 t2 --> t1
  | ST_ChoiceRight : forall t1 t2,
      locally_closed t1 ->
      locally_closed t2 ->
      tm_choice t1 t2 --> t2
where "t '-->' t'" := (step t t').

Hint Constructors step : core.

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

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
  | T_Choice : forall Gamma t1 t2 T,
      <{ Gamma |-- $(t1) \in T }> ->
      <{ Gamma |-- $(t2) \in T }> ->
      <{ Gamma |-- choice $(t1) or $(t2) \in T }>
where "<{ Gamma '|--' t '\in' T }>" := (has_type Gamma t T)
  : stlc_scope.

Hint Constructors has_type : core.

Inductive strongly_normalizing : tm -> Prop :=

  | SN_intro : forall t,
      (forall t', t --> t' -> strongly_normalizing t') ->
      strongly_normalizing t.

Definition term_substitution := atom -> tm.

Definition id_substitution : term_substitution :=
  fun x => tm_fvar x.

Definition subst_update
    (rho : term_substitution) (x : atom) (v : tm) : term_substitution :=
  fun y => if Nat.eqb x y then v else rho y.

Fixpoint msubst (rho : term_substitution) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => rho x
  | tm_app t1 t2 => tm_app (msubst rho t1) (msubst rho t2)
  | tm_abs T t1 => tm_abs T (msubst rho t1)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (msubst rho t1) (msubst rho t2) (msubst rho t3)
  | tm_choice t1 t2 => tm_choice (msubst rho t1) (msubst rho t2)
  end.

Definition proper_substitution (rho : term_substitution) : Prop :=
  forall x, locally_closed (rho x).

Fixpoint strong_value_relation (T : ty) (v : tm) : Prop :=
  value v /\
  match T with
  | Ty_Bool =>
      v = tm_true \/ v = tm_false
  | Ty_Arrow T1 T2 =>
      exists body,
        v = tm_abs T1 body /\
        forall arg,
          strong_value_relation T1 arg ->
          locally_closed (open body arg) /\
          strongly_normalizing (open body arg) /\
          forall result,
            open body arg -->* result ->
            value result ->
            strong_value_relation T2 result
  end.

Definition strong_expression_relation (T : ty) (t : tm) : Prop :=
  locally_closed t /\
  strongly_normalizing t /\
  forall v,
    t -->* v ->
    value v ->
    strong_value_relation T v.

Definition strong_related_substitution
    (Gamma : context) (rho : term_substitution) : Prop :=
  forall x T,
    Gamma x = Some T ->
    strong_value_relation T (rho x).

Fixpoint list_max (xs : list nat) : nat :=
  match xs with
  | nil => 0
  | x :: xs' => Nat.max x (list_max xs')
  end.

Lemma in_list_max : forall x xs, In x xs -> x <= list_max xs.
Proof.
  induction xs as [|a xs IH]; simpl; intros H.
  - contradiction.
  - destruct H as [->|H].
    + lia.
    + pose proof (IH H); lia.
Qed.

Definition fresh_for (xs : list nat) := S (list_max xs).

Lemma fresh_for_notin : forall xs, ~ In (fresh_for xs) xs.
Proof.
  intros xs H.
  unfold fresh_for in H.
  pose proof (in_list_max _ _ H); lia.
Qed.

Lemma notin_app : forall (x : atom) (xs ys : list atom),
  ~ In x xs -> ~ In x ys -> ~ In x (xs ++ ys).
Proof.
  intros x xs ys Hx Hy H.
  apply in_app_or in H; intuition.
Qed.

Lemma notin_app_left : forall (x : atom) xs ys,
  ~ In x (xs ++ ys) -> ~ In x xs.
Proof.
  intros x xs ys H Hx. apply H. apply in_or_app; left; assumption.
Qed.

Lemma notin_app_right : forall (x : atom) xs ys,
  ~ In x (xs ++ ys) -> ~ In x ys.
Proof.
  intros x xs ys H Hy. apply H. apply in_or_app; right; assumption.
Qed.

Fixpoint fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ => nil
  | tm_fvar x => x :: nil
  | tm_app t1 t2 => fv t1 ++ fv t2
  | tm_abs _ t1 => fv t1
  | tm_true => nil
  | tm_false => nil
  | tm_if t1 t2 t3 => fv t1 ++ fv t2 ++ fv t3
  | tm_choice t1 t2 => fv t1 ++ fv t2
  end.

Lemma lc_at_mono : forall k l t, k <= l -> lc_at k t -> lc_at l t.
Proof.
  intros k l t Hkl H.
  revert l Hkl.
  induction H; intros l Hkl.
  - apply lc_bvar; lia.
  - apply lc_fvar.
  - apply lc_app; eauto.
  - apply lc_abs. eapply IHlc_at; lia.
  - apply lc_true.
  - apply lc_false.
  - apply lc_if; eauto.
  - apply lc_choice; eauto.
Qed.

Lemma open_rec_lc : forall k u t, lc_at k t -> open_rec k u t = t.
Proof.
  intros k u t.
  revert k u.
  induction t as [i|x|t1 IH1 t2 IH2|T t1 IH| | |t1 IH1 t2 IH2 t3 IH3|t1 IH1 t2 IH2];
    intros k u H; inversion H; simpl.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E; lia.
    + reflexivity.
  - reflexivity.
  - f_equal.
    + apply IH1; assumption.
    + apply IH2; assumption.
  - f_equal. apply IH with (k:=S k) (u:=u); assumption.
  - reflexivity.
  - reflexivity.
  - apply f_equal3; [apply IH1; assumption|apply IH2; assumption|apply IH3; assumption].
  - f_equal.
    + apply IH1; assumption.
    + apply IH2; assumption.
Qed.

Lemma lc_open_rec : forall k t u,
  lc_at (S k) t -> lc_at k u -> lc_at k (open_rec k u t).
Proof.
  intros k t.
  revert k.
  induction t as [i|x|t1 IH1 t2 IH2|T t1 IH| | |t1 IH1 t2 IH2 t3 IH3|t1 IH1 t2 IH2];
    intros k u Ht Hu; inversion Ht; simpl.
  - destruct (Nat.eqb k i) eqn:E.
    + exact Hu.
    + constructor. apply Nat.eqb_neq in E; lia.
  - constructor.
  - constructor; [apply IH1 with (k:=k)|apply IH2 with (k:=k)]; assumption.
  - constructor. apply IH with (k:=S k).
    + assumption.
    + apply (lc_at_mono k (S k) u); [lia|exact Hu].
  - constructor.
  - constructor.
  - constructor; [apply IH1 with (k:=k)|apply IH2 with (k:=k)|apply IH3 with (k:=k)]; assumption.
  - constructor; [apply IH1 with (k:=k)|apply IH2 with (k:=k)]; assumption.
Qed.

Lemma lc_open_rec_inv : forall k t u,
  lc_at k (open_rec k u t) -> lc_at (S k) t.
Proof.
  intros k t.
  revert k.
  induction t as [i|x|t1 IH1 t2 IH2|T t1 IH| | |t1 IH1 t2 IH2 t3 IH3|t1 IH1 t2 IH2];
    intros k u H; simpl in H.
  - destruct (Nat.eqb k i) eqn:E.
    + constructor; apply Nat.eqb_eq in E; lia.
    + inversion H; constructor; apply Nat.eqb_neq in E; lia.
  - constructor.
  - inversion H; apply lc_app; [apply IH1 with (k:=k) (u:=u)|apply IH2 with (k:=k) (u:=u)]; assumption.
  - inversion H; apply lc_abs. apply IH with (k:=S k) (u:=u); assumption.
  - constructor.
  - constructor.
  - inversion H; apply lc_if; [apply IH1 with (k:=k) (u:=u)|apply IH2 with (k:=k) (u:=u)|apply IH3 with (k:=k) (u:=u)]; assumption.
  - inversion H; apply lc_choice; [apply IH1 with (k:=k) (u:=u)|apply IH2 with (k:=k) (u:=u)]; assumption.
Qed.

Lemma fv_open_update : forall rho x u k t,
  proper_substitution rho ->
  ~ In x (fv t) ->
  msubst (subst_update rho x u) (open_rec k (tm_fvar x) t) =
  open_rec k u (msubst rho t).
Proof.
  intros rho x u k t.
  revert k.
  induction t as [i|y|t1 IH1 t2 IH2|T t1 IH| | |t1 IH1 t2 IH2 t3 IH3|t1 IH1 t2 IH2];
    intros k Hr Hfresh; simpl in *.
  - destruct (Nat.eqb k i) eqn:E; simpl.
    + unfold subst_update. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - destruct (Nat.eqb x y) eqn:E; simpl.
    + apply Nat.eqb_eq in E. exfalso. apply Hfresh. simpl; left; symmetry; assumption.
    + unfold subst_update. rewrite E.
      symmetry. apply open_rec_lc.
      apply lc_at_mono with (k:=0); [lia|apply Hr].
  - apply f_equal2.
    + apply IH1; [exact Hr|apply notin_app_left with (ys:=fv t2); exact Hfresh].
    + apply IH2; [exact Hr|apply notin_app_right with (xs:=fv t1); exact Hfresh].
  - f_equal. apply IH with (k:=S k); [exact Hr|exact Hfresh].
  - reflexivity.
  - reflexivity.
  - change (~ In x (fv t1 ++ (fv t2 ++ fv t3))) in Hfresh.
    apply f_equal3.
    + apply IH1; [exact Hr|apply notin_app_left with (ys:=fv t2 ++ fv t3); exact Hfresh].
    + apply IH2; [exact Hr|apply notin_app_left with (ys:=fv t3);
        apply notin_app_right with (xs:=fv t1); exact Hfresh].
    + apply IH3; [exact Hr|apply notin_app_right with (xs:=fv t2);
        apply notin_app_right with (xs:=fv t1); exact Hfresh].
  - apply f_equal2.
    + apply IH1; [exact Hr|apply notin_app_left with (ys:=fv t2); exact Hfresh].
    + apply IH2; [exact Hr|apply notin_app_right with (xs:=fv t1); exact Hfresh].
Qed.

Lemma msubst_lc : forall k rho t,
  proper_substitution rho -> lc_at k t -> lc_at k (msubst rho t).
Proof.
  intros k rho t. revert k rho.
  induction t as [i|x|t1 IH1 t2 IH2|T t1 IH| | |t1 IH1 t2 IH2 t3 IH3|t1 IH1 t2 IH2];
    intros k rho Hr H; simpl in *.
  - inversion H. constructor; assumption.
  - apply (lc_at_mono 0 k (rho x)); [lia|apply Hr].
  - inversion H; apply lc_app; [apply IH1|apply IH2]; assumption.
  - inversion H; apply lc_abs. apply IH; assumption.
  - constructor.
  - constructor.
  - inversion H; apply lc_if; [apply IH1|apply IH2|apply IH3]; assumption.
  - inversion H; apply lc_choice; [apply IH1|apply IH2]; assumption.
Qed.

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v H; inversion H; assumption || constructor.
Qed.

Lemma lc_app_abs_body : forall T b v,
  locally_closed (tm_app (tm_abs T b) v) -> lc_at 1 b.
Proof.
  intros T b v H. unfold locally_closed in H.
  inversion H; eauto.
  inversion H3; assumption.
Qed.

Lemma lc_app_arg : forall f v,
  locally_closed (tm_app f v) -> locally_closed v.
Proof.
  intros f v H. unfold locally_closed in H. inversion H; assumption.
Qed.

Lemma step_lc_at : forall k t t', lc_at k t -> t --> t' -> lc_at k t'.
Proof.
  intros k t t' Hlc Hs. revert k Hlc.
  induction Hs; intros k Hlc; simpl in *.
  - inversion Hlc.
    apply lc_at_mono with (k:=0); [lia|].
    unfold open.
    eapply lc_open_rec.
    + unfold locally_closed in H. inversion H; assumption.
    + eapply value_lc; eauto.
  - inversion Hlc. apply lc_app.
    + eapply IHHs; eauto.
    + assumption.
  - inversion Hlc. apply lc_app.
    + assumption.
    + eapply IHHs; eauto.
  - unfold locally_closed in *. apply lc_at_mono with (k:=0); [lia|assumption].
  - unfold locally_closed in *. apply lc_at_mono with (k:=0); [lia|assumption].
  - inversion Hlc. apply lc_if.
    + eapply IHHs; eauto.
    + assumption.
    + assumption.
  - unfold locally_closed in *. apply lc_at_mono with (k:=0); [lia|assumption].
  - unfold locally_closed in *. apply lc_at_mono with (k:=0); [lia|assumption].
Qed.

Lemma step_lc : forall t t', locally_closed t -> t --> t' -> locally_closed t'.
Proof.
  intros t t' H Hs. unfold locally_closed in *.
  eapply step_lc_at; eauto.
Qed.

Lemma value_no_step : forall v, value v -> forall v', ~ v --> v'.
Proof.
  intros v Hv v' Hs. destruct Hv; inversion Hs.
Qed.

Lemma sn_value : forall v, value v -> strongly_normalizing v.
Proof.
  intros v Hv. constructor. intros v' Hs. exfalso. eapply value_no_step; eauto.
Qed.

Lemma lc_value : forall v, value v -> locally_closed v.
Proof. exact value_lc. Qed.

Lemma value_multistep_eq : forall v v', value v -> v -->* v' -> v = v'.
Proof.
  intros v v' Hv Hp. induction Hp.
  - reflexivity.
  - exfalso. eapply value_no_step; eauto.
Qed.

Lemma value_path_refl : forall T v,
  strong_value_relation T v -> strong_expression_relation T v.
Proof.
  intros T v H. destruct T as [|T1 T2]; simpl in H.
  destruct H as [Hv Hshape].
  unfold strong_expression_relation.
  repeat split.
  - apply value_lc; assumption.
  - apply sn_value; assumption.
  - intros v' Hp Hv'.
    pose proof (value_multistep_eq v v' Hv Hp) as E.
    subst. exact (conj Hv Hshape).
Qed.

Lemma expression_step : forall T t t',
  strong_expression_relation T t -> t --> t' ->
  strong_expression_relation T t'.
Proof.
  intros T t t' [Hlc Hsn Hend] Hs.
  repeat split.
  - eapply step_lc; eauto.
  - inversion Hsn; eauto.
  - intros v Hp Hv.
    apply Hend v. econstructor; eauto. exact Hp. exact Hv.
Qed.

Lemma expression_multistep : forall T t t',
  strong_expression_relation T t -> t -->* t' ->
  strong_expression_relation T t'.
Proof.
  intros T t t' He Hp.
  induction Hp; auto.
  eapply IHHp; eapply expression_step; eauto.
Qed.

Lemma expression_value : forall T t,
  strong_expression_relation T t -> value t ->
  strong_value_relation T t.
Proof.
  intros T t He Hv. eapply (proj3 He t); [constructor|assumption].
Qed.

Lemma if_sn : forall t1 t2 t3,
  strongly_normalizing t1 -> strongly_normalizing t2 ->
  strongly_normalizing t3 -> strongly_normalizing (tm_if t1 t2 t3).
Proof.
  intros t1 t2 t3 H1 H2 H3.
  induction H1 as [t1 H1 IH].
  constructor. intros t' Hstep; inversion Hstep; subst; eauto.
Qed.

Lemma choice_sn : forall t1 t2,
  strongly_normalizing t1 -> strongly_normalizing t2 ->
  strongly_normalizing (tm_choice t1 t2).
Proof.
  intros t1 t2 H1 H2. constructor. intros t' H; inversion H; eauto.
Qed.

Lemma app_sn_aux : forall A B f,
  strongly_normalizing f ->
  strong_expression_relation (Ty_Arrow A B) f ->
  forall a, strong_expression_relation A a ->
  strongly_normalizing (tm_app f a).
Proof.
  intros A B f Hsn.
  induction Hsn as [f Hnext IH].
  intros Ef a Ea.
  induction (proj2 Ea) as [a Hanext IHa].
  constructor. intros z Hz; inversion Hz; subst.
  - apply IH. apply expression_step; eauto.
  - apply IHa. apply expression_step; eauto.
  - pose proof (expression_value (Ty_Arrow A B) f Ef H0) as Evf.
    pose proof (expression_value A a Ea H1) as Eva.
    simpl in Evf, Eva. destruct Evf as [Evf Hfun].
    destruct Hfun as [body -> Hfun].
    simpl in Eva. destruct Eva as [Eva _].
    eapply Hfun; eauto.
Qed.

Lemma app_path : forall A B f a v,
  strong_expression_relation (Ty_Arrow A B) f ->
  strong_expression_relation A a ->
  tm_app f a -->* v -> value v ->
  strong_value_relation B v.
Proof.
  intros A B f a v Ef Ea Hp Hv.
  induction Hp as [x|x y z Hxy Hyz IH]; subst.
  - inversion Hv.
  - inversion Hxy; subst.
    + apply IH. apply expression_step; eauto. exact Ea. exact Hv.
    + apply IH. exact Ef. apply expression_step; eauto. exact Hv.
    + pose proof (expression_value (Ty_Arrow A B) f Ef H0) as Evf.
      pose proof (expression_value A a Ea H1) as Eva.
      simpl in Evf, Eva. destruct Evf as [_ Hfun].
      destruct Hfun as [body -> Hfun].
      simpl in Eva. destruct Eva as [Eva _].
      eapply Hfun; eauto.
Qed.

Lemma app_expression : forall A B f a,
  strong_expression_relation (Ty_Arrow A B) f ->
  strong_expression_relation A a ->
  strong_expression_relation B (tm_app f a).
Proof.
  intros A B f a Ef Ea. unfold strong_expression_relation.
  repeat split.
  - apply lc_app; [apply (proj1 Ef)|apply (proj1 Ea)].
  - apply app_sn_aux with (A:=A) (B:=B); eauto.
  - intros v Hp Hv. eapply app_path; eauto.
Qed.

Lemma if_path : forall A c t e v,
  strong_expression_relation Ty_Bool c ->
  strong_expression_relation A t ->
  strong_expression_relation A e ->
  tm_if c t e -->* v -> value v ->
  strong_value_relation A v.
Proof.
  intros A c t e v Ec Et Ee Hp Hv.
  induction Hp as [x|x y z Hxy Hyz IH]; subst.
  - inversion Hv.
  - inversion Hxy; subst.
    + apply expression_value with (T:=A) (t:=v).
      eapply expression_multistep; eauto.
      exact Hv.
    + apply expression_value with (T:=A) (t:=v).
      eapply expression_multistep; eauto.
      exact Hv.
    + apply IH; [apply expression_step; eauto|exact Et|exact Ee|exact Hv].
Qed.

Lemma if_expression : forall A c t e,
  strong_expression_relation Ty_Bool c ->
  strong_expression_relation A t ->
  strong_expression_relation A e ->
  strong_expression_relation A (tm_if c t e).
Proof.
  intros A c t e Ec Et Ee. unfold strong_expression_relation.
  repeat split.
  - apply lc_if; [apply (proj1 Ec)|apply (proj1 Et)|apply (proj1 Ee)].
  - apply if_sn; [apply (proj2 Ec)|apply (proj2 Et)|apply (proj2 Ee)].
  - intros v Hp Hv. eapply if_path; eauto.
Qed.

Lemma choice_path : forall A t1 t2 v,
  strong_expression_relation A t1 ->
  strong_expression_relation A t2 ->
  tm_choice t1 t2 -->* v -> value v ->
  strong_value_relation A v.
Proof.
  intros A t1 t2 v E1 E2 Hp Hv.
  induction Hp as [x|x y z Hxy Hyz IH]; subst.
  - inversion Hv.
  - inversion Hxy; subst.
    + apply expression_value with (T:=A) (t:=v).
      eapply expression_multistep; eauto. exact Hv.
    + apply expression_value with (T:=A) (t:=v).
      eapply expression_multistep; eauto. exact Hv.
Qed.

Lemma choice_expression : forall A t1 t2,
  strong_expression_relation A t1 ->
  strong_expression_relation A t2 ->
  strong_expression_relation A (tm_choice t1 t2).
Proof.
  intros A t1 t2 E1 E2. unfold strong_expression_relation.
  repeat split.
  - apply lc_choice; [apply (proj1 E1)|apply (proj1 E2)].
  - apply choice_sn; [apply (proj2 E1)|apply (proj2 E2)].
  - intros v Hp Hv. eapply choice_path; eauto.
Qed.

Lemma proper_update : forall rho x u,
  proper_substitution rho -> locally_closed u ->
  proper_substitution (subst_update rho x u).
Proof.
  intros rho x u Hr Hu y. unfold subst_update.
  destruct (Nat.eqb x y); auto.
Qed.

Lemma related_update : forall Gamma rho x A u,
  strong_related_substitution Gamma rho ->
  strong_value_relation A u ->
  strong_related_substitution (update Gamma x A) (subst_update rho x u).
Proof.
  intros Gamma rho x A u Hrel Hu y T Hlookup.
  unfold update in Hlookup. unfold subst_update.
  destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. subst. simpl in Hlookup. inversion Hlookup. exact Hu.
  - apply Hrel with (x:=y) (T:=T).
    exact Hlookup.
Qed.

Lemma typing_lc : forall Gamma t T,
  <{ Gamma |-- t \in T }> -> locally_closed t.
Proof.
  intros Gamma t T Hty. induction Hty.
  - constructor.
  - apply lc_abs. pose proof (H x (fresh_for_notin L)) as Hx.
    pose proof (typing_lc _ _ _ Hx) as Hlc.
    unfold open in Hlc.
    eapply lc_open_rec_inv; eauto.
  - apply lc_app; assumption.
  - constructor.
  - constructor.
  - apply lc_if; assumption.
  - apply lc_choice; assumption.
Qed.

Theorem fundamental : forall Gamma t T rho,
  proper_substitution rho ->
  strong_related_substitution Gamma rho ->
  <{ Gamma |-- t \in T }> ->
  strong_expression_relation T (msubst rho t).
Proof.
  intros Gamma t T rho Hr Hrel Hty.
  revert rho Hr Hrel.
  induction Hty; intros rho Hr Hrel.
  - apply value_path_refl. apply Hrel with (x:=x) (T:=T); assumption.
  - pose (x := fresh_for (L ++ fv t1)).
    assert (HxL : ~ In x L).
    { unfold x. apply notin_app_left with (ys:=fv t1); apply fresh_for_notin. }
    assert (Hxfv : ~ In x (fv t1)).
    { unfold x. apply notin_app_right with (xs:=L); apply fresh_for_notin. }
    pose proof (H x HxL) as Hbodyty.
    pose proof (typing_lc _ _ _ Hbodyty) as Hbodylc0.
    unfold open in Hbodylc0.
    pose proof (lc_open_rec_inv 0 t1 (tm_fvar x) Hbodylc0) as Hbodylc.
    pose proof (msubst_lc 1 rho t1 Hr Hbodylc) as Hbodylc'.
    assert (Habs : locally_closed (tm_abs T1 (msubst rho t1))).
    { unfold locally_closed. apply lc_abs. exact Hbodylc'. }
    apply value_path_refl.
    split.
    + apply v_abs. exact Habs.
    + simpl. exists (msubst rho t1). split; [reflexivity|].
      intros arg Harg.
      pose proof (proper_update rho x arg Hr) as Hr'.
      pose proof (related_update Gamma rho x T1 arg Hrel Harg) as Hrel'.
      pose proof (IH (subst_update rho x arg) Hr' Hrel') as HE.
      rewrite (fv_open_update rho x arg 0 t1 Hr Hxfv) in HE.
      exact HE.
  - apply app_expression; [apply IH1|apply IH2]; assumption.
  - apply value_path_refl. split; [constructor|simpl; left; reflexivity].
  - apply value_path_refl. split; [constructor|simpl; right; reflexivity].
  - apply if_expression; [apply IH1|apply IH2|apply IH3]; assumption.
  - apply choice_expression; [apply IH1|apply IH2]; assumption.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  pose proof (fundamental empty t T id_substitution) as H.
  - exact (proj2 H).
  - intros x. unfold locally_closed, id_substitution. constructor.
  - intros x U Hlookup. simpl in Hlookup. discriminate.
  - exact Hty.
Qed.

End STLCNormalizationIfNondeterminismMediumTask.
