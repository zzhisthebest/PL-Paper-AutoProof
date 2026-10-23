(** STLC call-by-value strong-normalization benchmark, Medium variant.
    No if-then-else, non-determinism, or recursion is included. *)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Relations.Relation_Definitions.

Module STLCNormalizationNoneMediumTask.

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

(** Provided logical relation. *)

Inductive strongly_normalizing : tm -> Prop :=
  | SN_intro : forall t,
      (forall t', t --> t' -> strongly_normalizing t') ->
      strongly_normalizing t.

Fixpoint value_relation (T : ty) (v : tm) : Prop :=
  value v /\
  match T with
  | Ty_Bool =>
      v = tm_true \/ v = tm_false
  | Ty_Arrow T1 T2 =>
      exists body,
        v = tm_abs T1 body /\
        forall arg,
          value_relation T1 arg ->
          locally_closed (open body arg) /\
          exists v',
            open body arg -->* v' /\
            value_relation T2 v'
  end.

Definition expression_relation (T : ty) (t : tm) : Prop :=
  locally_closed t /\
  exists v,
    t -->* v /\
    value_relation T v.

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
  end.

Definition proper_substitution (rho : term_substitution) : Prop :=
  forall x, locally_closed (rho x).

Definition related_substitution
    (Gamma : context) (rho : term_substitution) : Prop :=
  forall x T,
    Gamma x = Some T ->
    value_relation T (rho x).

Fixpoint list_max (l : list atom) : nat :=
  match l with
  | nil => 0
  | x :: l' => Nat.max x (list_max l')
  end.

Lemma in_list_max : forall x l, In x l -> x <= list_max l.
Proof.
  induction l as [|a l IH]; simpl; intros H.
  - contradiction.
  - destruct H as [H|H].
    + subst. apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; exact H|apply Nat.le_max_r].
Qed.

Lemma fresh_atom : forall l : list atom, exists x, ~ In x l.
Proof.
  intro l.
  exists (S (list_max l)).
  intro H.
  pose proof (in_list_max _ _ H) as Hle.
  apply (Nat.nle_succ_diag_l (list_max l)).
  exact Hle.
Qed.

Definition fresh_nat (l : list atom) : atom := S (list_max l).

Lemma fresh_nat_spec : forall l, ~ In (fresh_nat l) l.
Proof.
  intros l H. unfold fresh_nat in H.
  pose proof (in_list_max _ _ H) as Hle.
  apply (Nat.nle_succ_diag_l (list_max l)). exact Hle.
Qed.

Fixpoint fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ => nil
  | tm_fvar x => x :: nil
  | tm_app t1 t2 => fv t1 ++ fv t2
  | tm_abs _ t1 => fv t1
  | tm_true => nil
  | tm_false => nil
  end.

Lemma lc_at_mono : forall k t, lc_at k t -> lc_at (S k) t.
Proof.
  intros k t H.
  induction H.
  - apply lc_bvar. apply Nat.lt_lt_succ_r. assumption.
  - constructor.
  - constructor; assumption.
  - apply lc_abs. assumption.
  - constructor.
  - constructor.
Qed.

Lemma lc_from_0 : forall t, locally_closed t -> forall k, lc_at k t.
Proof.
  intros t H k.
  unfold locally_closed in H.
  induction k as [|k IH].
  - exact H.
  - apply lc_at_mono. exact IH.
Qed.

Lemma lc_open_rec_inv : forall k t u,
    lc_at k u -> lc_at k (open_rec k u t) -> lc_at (S k) t.
Proof.
  intros k t. revert k.
  induction t as [i|x|t1 IH1 t2 IH2|T t1 IH| |];
    intros k u Hu Hopen; simpl in Hopen.
  - destruct (Nat.eqb k i) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst i.
      apply lc_bvar. apply Nat.lt_succ_diag_r.
    + apply lc_bvar. apply Nat.lt_lt_succ_r.
      inversion Hopen. assumption.
  - constructor.
  - inversion Hopen. apply lc_app; eauto.
  - inversion Hopen. apply lc_abs.
    apply IH with (k := S k) (u := u). apply lc_at_mono. exact Hu. assumption.
  - constructor.
  - constructor.
Qed.

Lemma lc_msubst : forall k t rho,
    (forall x, lc_at k (rho x)) ->
    lc_at k t ->
    lc_at k (msubst rho t).
Proof.
  intros k t rho Hr Ht.
  induction Ht.
  - simpl. apply lc_bvar. assumption.
  - simpl. apply Hr.
  - simpl. apply lc_app; [apply IHHt1; assumption|apply IHHt2; assumption].
  - simpl. apply lc_abs. apply IHHt.
    intros x. apply lc_at_mono. apply Hr.
  - simpl. constructor.
  - simpl. constructor.
Qed.

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v H. destruct H as [T t Hlc| |].
  - exact Hlc.
  - constructor.
  - constructor.
Qed.

Lemma value_relation_value : forall T v, value_relation T v -> value v.
Proof.
  intros T v H. destruct T; simpl in H; exact (proj1 H).
Qed.

Lemma lc_msubst_on_fv : forall k t rho,
    lc_at k t ->
    (forall x, In x (fv t) -> lc_at k (rho x)) ->
    lc_at k (msubst rho t).
Proof.
  intros k t rho Ht Hr.
  induction Ht.
  - simpl. apply lc_bvar. assumption.
  - simpl. apply Hr. simpl. left. reflexivity.
  - simpl. apply lc_app.
    + apply IHHt1. intros x Hx. apply Hr. apply in_or_app. left. exact Hx.
    + apply IHHt2. intros x Hx. apply Hr. apply in_or_app. right. exact Hx.
  - simpl. apply lc_abs. apply IHHt.
    intros x Hx. apply lc_at_mono. apply Hr. exact Hx.
  - simpl. constructor.
  - simpl. constructor.
Qed.

Lemma subst_update_same : forall rho x v,
    subst_update rho x v x = v.
Proof.
  intros. unfold subst_update. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma open_rec_lc : forall k u t,
    lc_at k t -> open_rec k u t = t.
Proof.
  intros k u t H.
  induction H; simpl.
  - destruct (Nat.eqb k i) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst i. exfalso.
      apply (Nat.lt_irrefl k). assumption.
    + reflexivity.
  - reflexivity.
  - rewrite IHlc_at1, IHlc_at2. reflexivity.
  - rewrite IHlc_at. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma msubst_open_rec : forall k rho x t v,
    ~ In x (fv t) ->
    (forall y, In y (fv t) -> lc_at k (rho y)) ->
    msubst (subst_update rho x v) (open_rec k (tm_fvar x) t) =
    open_rec k v (msubst rho t).
Proof.
  intros k rho x t. revert k.
  induction t as [i|y|t1 IH1 t2 IH2|T t1 IH| |];
    intros k v Hfresh Hr; simpl.
  - destruct (Nat.eqb k i) eqn:Heq; simpl; try rewrite subst_update_same; reflexivity.
  - simpl in Hfresh.
    unfold subst_update. destruct (Nat.eqb x y) eqn:Heq.
    + exfalso. apply Hfresh. apply Nat.eqb_eq in Heq. subst y. simpl. left. reflexivity.
    + rewrite (open_rec_lc k v (rho y)). reflexivity.
      apply Hr. simpl. left. reflexivity.
  - assert (Hf1 : ~ In x (fv t1)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (Hf2 : ~ In x (fv t2)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    assert (Hr1 : forall y, In y (fv t1) -> lc_at k (rho y)).
    { intros y H. apply Hr. apply in_or_app. left. exact H. }
    assert (Hr2 : forall y, In y (fv t2) -> lc_at k (rho y)).
    { intros y H. apply Hr. apply in_or_app. right. exact H. }
    rewrite (IH1 k v Hf1 Hr1), (IH2 k v Hf2 Hr2). reflexivity.
  - apply f_equal. apply IH with (k := S k); [assumption|].
    intros y H. apply lc_at_mono. apply Hr. exact H.
  - reflexivity.
  - reflexivity.
Qed.

Lemma multi_trans : forall (X : Type) (R : relation X) x y z,
    multi R x y -> multi R y z -> multi R x z.
Proof.
  intros X R x y z Hxy Hyz.
  induction Hxy.
  - exact Hyz.
  - eapply multi_step.
    + exact H.
    + apply IHHxy. exact Hyz.
Qed.

Lemma multi_app1 : forall t1 t1' t2,
    t1 -->* t1' -> locally_closed t2 ->
    tm_app t1 t2 -->* tm_app t1' t2.
Proof.
  intros t1 t1' t2 H Hlc.
  induction H.
  - constructor.
  - apply multi_step with (tm_app y t2).
    + apply ST_App1; assumption.
    + exact IHmulti.
Qed.

Lemma multi_app2 : forall v1 t2 t2',
    value v1 -> t2 -->* t2' ->
    tm_app v1 t2 -->* tm_app v1 t2'.
Proof.
  intros v1 t2 t2' Hv H.
  induction H.
  - constructor.
  - apply multi_step with (tm_app v1 y).
    + apply ST_App2; assumption.
    + exact IHmulti.
Qed.

Lemma expression_of_value : forall T v,
    value_relation T v -> expression_relation T v.
Proof.
  intros T v H. destruct T as [|T1 T2]; simpl in H.
  - split.
    + apply value_lc. apply (proj1 H).
    + exists v. split; [constructor|exact H].
  - split.
    + apply value_lc. apply (proj1 H).
    + exists v. split; [constructor|exact H].
Qed.

Lemma related_update : forall G rho x T v,
    related_substitution G rho -> value_relation T v ->
    related_substitution (update G x T) (subst_update rho x v).
Proof.
  intros G rho x T v Hr Hv y U H.
  unfold update, subst_update in *.
  destruct (Nat.eqb x y) eqn:Heq.
  - apply Nat.eqb_eq in Heq. subst y.
    simpl in H. inversion H. subst U. exact Hv.
  - exact (Hr y U H).
Qed.

Lemma related_rho_lc : forall G rho,
    related_substitution G rho ->
    forall x, (exists U, G x = Some U) -> locally_closed (rho x).
Proof.
  intros G rho Hr x Hex. destruct Hex as [U HU].
  apply value_lc. apply (value_relation_value U (rho x)). apply (Hr x U HU).
Qed.

Fixpoint typing_lc (G : context) (t : tm) (T : ty)
    (H : has_type G t T) : locally_closed t :=
  match H with
  | T_Var Gamma x T e => lc_fvar 0 x
  | T_Abs L Gamma T1 T2 t1 Hbody =>
      lc_abs 0 T1 t1
        (lc_open_rec_inv 0 t1 (tm_fvar (fresh_nat (L ++ fv t1)))
          ((lc_from_0 (tm_fvar (fresh_nat (L ++ fv t1)))
             (lc_fvar 0 (fresh_nat (L ++ fv t1)))) 0)
          (typing_lc (update Gamma (fresh_nat (L ++ fv t1)) T1)
             (open t1 (tm_fvar (fresh_nat (L ++ fv t1)))) T2
             (Hbody (fresh_nat (L ++ fv t1))
                (fun Hin => fresh_nat_spec (L ++ fv t1)
                   (in_or_app _ _ _ (or_introl Hin))))))
  | T_App Gamma t1 t2 T1 T2 H1 H2 =>
      lc_app 0 t1 t2 (typing_lc Gamma t1 (Ty_Arrow T1 T2) H1)
        (typing_lc Gamma t2 T1 H2)
  | T_True Gamma => lc_true 0
  | T_False Gamma => lc_false 0
  end.

Lemma in_fv_open : forall k u t y,
    In y (fv t) -> In y (fv (open_rec k u t)).
Proof.
  intros k u t. revert k.
  induction t as [i|x|t1 IH1 t2 IH2|T t1 IH| |];
    intros k y H; simpl in *.
  - contradiction.
  - exact H.
  - apply in_or_app. apply in_app_iff in H. destruct H as [H|H].
    + left. apply IH1. exact H.
    + right. apply IH2. exact H.
  - apply IH. exact H.
  - contradiction.
  - contradiction.
Qed.

Lemma fv_abs_mem : forall (T : ty) t y,
    In y (fv (tm_abs T t)) -> In y (fv t).
Proof. intros. exact H. Qed.

Lemma update_neq : forall G x y T, x <> y -> update G x T y = G y.
Proof.
  intros G x y T H. unfold update. destruct (Nat.eqb x y) eqn:Heq.
  - exfalso. apply H. apply (proj1 (Nat.eqb_eq _ _) Heq).
  - reflexivity.
Qed.

Lemma in_singleton : forall (x y : atom), In y (x :: nil) -> y = x.
Proof.
  intros x y H. simpl in H. destruct H as [H|H].
  - symmetry. exact H.
  - contradiction.
Qed.

Fixpoint fv_typed (G : context) (t : tm) (T : ty)
    (H : has_type G t T) :
    forall x, In x (fv t) -> exists U, G x = Some U :=
  match H with
  | T_Var Gamma x T e =>
      fun y Hy =>
        @ex_intro ty (fun q => Gamma y = Some q) T
          (eq_ind x (fun q => Gamma q = Some T) e y
             (eq_sym (in_singleton x y Hy)))
  | T_Abs L Gamma T1 T2 t1 Hbody =>
      fun y Hy =>
        let z := fresh_nat (L ++ fv t1) in
        let Hz := fresh_nat_spec (L ++ fv t1) in
        match fv_typed (update Gamma z T1) (open t1 (tm_fvar z)) T2
                (Hbody z (fun Hin => Hz (in_or_app _ _ _ (or_introl Hin))))
                y (in_fv_open 0 (tm_fvar z) t1 y (fv_abs_mem T1 t1 y Hy)) with
        | ex_intro _ U Hlookup =>
            match Nat.eqb z y as b return (Nat.eqb z y = b -> exists U, Gamma y = Some U) with
            | true => fun Heq => False_rect _ (Hz (in_or_app _ _ _ (or_intror
                         (eq_rect y (fun q => In q (fv t1)) (fv_abs_mem T1 t1 y Hy) z
                            (eq_sym (proj1 (Nat.eqb_eq _ _) Heq))))))
            | false => fun Heq => @ex_intro ty (fun q => Gamma y = Some q) U
                (eq_trans (eq_sym (update_neq Gamma z y T1
                  (proj1 (Nat.eqb_neq _ _) Heq))) Hlookup)
            end eq_refl
        end
  | T_App Gamma t1 t2 T1 T2 H1 H2 =>
      fun y Hy =>
        match (proj1 (in_app_iff _ _ y) Hy) with
        | or_introl Hyl =>
            fv_typed Gamma t1 (Ty_Arrow T1 T2) H1 y Hyl
        | or_intror Hyr =>
            fv_typed Gamma t2 T1 H2 y Hyr
        end
(*
        match (in_app_iff _ _ _ y) with
        | conj Hleft Hright =>
            match Hy with
            | or_introl Hyl => fv_typed Gamma t1 (Ty_Arrow T1 T2) H1 y Hyl
            | or_intror Hyr => fv_typed Gamma t2 T1 H2 y Hyr
            end
        end
*)
  | T_True Gamma => fun y Hy => False_rect _ Hy
  | T_False Gamma => fun y Hy => False_rect _ Hy
  end.

Lemma abs_body_lc : forall L G T1 T2 t1,
    (forall x, ~ In x L ->
      has_type (update G x T1) (open t1 (tm_fvar x)) T2) ->
    lc_at 1 t1.
Proof.
  intros L G T1 T2 t1 H.
  destruct (fresh_atom (L ++ fv t1)) as [x Hx].
  apply lc_open_rec_inv with (u := tm_fvar x).
  - apply lc_from_0. constructor.
  - apply (typing_lc (update G x T1) (open t1 (tm_fvar x)) T2).
    apply H. intro Hin. apply Hx. apply in_or_app. left. exact Hin.
Qed.

Theorem fundamental : forall G t T rho,
    <{ G |-- t \in T }> ->
    related_substitution G rho ->
    expression_relation T (msubst rho t).
Proof.
  intros G t T rho Hty. revert rho.
  induction Hty; intros rho Hr.
  - apply expression_of_value. apply (Hr x T). assumption.
  - assert (Hsupp : forall x, In x (fv t1) -> exists U, Gamma x = Some U).
    { intros x Hx.
      apply (fv_typed Gamma (tm_abs T1 t1) (Ty_Arrow T1 T2)
        (T_Abs L Gamma T1 T2 t1 H) x Hx). }
    assert (Hbodylc : lc_at 1 (msubst rho t1)).
    { apply lc_msubst_on_fv with (k := 1) (t := t1).
      - apply abs_body_lc with L Gamma T1 T2. exact H.
      - intros x Hx. apply lc_from_0.
        apply (related_rho_lc Gamma rho Hr x).
        apply Hsupp. exact Hx. }
    simpl. split.
    + apply lc_abs. exact Hbodylc.
    + exists (tm_abs T1 (msubst rho t1)). split.
      * constructor.
      * split.
        -- apply v_abs. unfold locally_closed. apply lc_abs. exact Hbodylc.
        -- exists (msubst rho t1). split.
           ++ reflexivity.
           ++ intros arg Harg.
              {
           destruct (fresh_atom (L ++ fv t1)) as [x Hx].
           assert (Hrx : related_substitution (update Gamma x T1)
                         (subst_update rho x arg)).
           { apply related_update; assumption. }
           pose proof (H0 x) as Hbody.
           pose proof (Hbody (fun Hin => Hx (in_or_app _ _ _ (or_introl Hin)))
             (subst_update rho x arg) Hrx) as Hbody'.
           pose proof (msubst_open_rec 0 rho x t1 arg
             (fun Hin => Hx (in_or_app _ _ _ (or_intror Hin)))
             (fun y Hy => lc_from_0 (rho y)
                (related_rho_lc Gamma rho Hr y (Hsupp y Hy)) 0)) as Hcomm.
           unfold open in Hbody'.
           rewrite Hcomm in Hbody'.
           exact Hbody'. }
  - simpl. destruct (IHHty1 rho Hr) as [Hlc1 [v1 [Hm1 Hv1]]].
    destruct (IHHty2 rho Hr) as [Hlc2 [v2 [Hm2 Hv2]]].
    destruct Hv1 as [Hv1 [body [Heq Hfun]]].
    subst v1.
    destruct (Hfun v2 Hv2) as [Hlcopen [v' [Hmopen Hv']]].
    split.
    + apply lc_app; assumption.
    + exists v'. split.
      * apply multi_trans with (tm_app (tm_abs T1 body) v2).
        -- apply multi_trans with (tm_app (tm_abs T1 body) (msubst rho t2)).
           ++ apply multi_app1; assumption.
           ++ apply multi_app2; [apply Hv1|exact Hm2].
        -- apply multi_step with (open body v2).
           ++ apply ST_AppAbs.
              ** apply value_lc. exact Hv1.
              ** apply (value_relation_value T1 v2). exact Hv2.
           ++ exact Hmopen.
      * exact Hv'.
  - apply expression_of_value. split; [constructor|left; reflexivity].
  - apply expression_of_value. split; [constructor|right; reflexivity].
Qed.

Lemma value_no_step : forall v v', value v -> ~ v --> v'.
Proof.
  intros v v' Hv Hs. destruct Hv; inversion Hs.
Qed.

Lemma abs_no_step : forall T t t',
    ~ (tm_abs T t --> t').
Proof. intros T t t' H; inversion H. Qed.

Lemma true_no_step : forall t', ~ (tm_true --> t').
Proof. intros t' H; inversion H. Qed.

Lemma false_no_step : forall t', ~ (tm_false --> t').
Proof. intros t' H; inversion H. Qed.

Lemma step_deterministic : forall t t1 t2,
    t --> t1 -> t --> t2 -> t1 = t2.
Proof.
  intros t t1 t2 H1. revert t2.
  induction H1; intros z H2.
  - inversion H2; subst; try reflexivity.
    + exfalso. exact (abs_no_step T t t1' H4).
    + exfalso. exact (value_no_step v t2' H0 H6).
  - inversion H2; subst; try reflexivity.
    all: try (intros; subst; reflexivity).
    all: try (intros; subst; f_equal; eauto).
    all: try (eauto using abs_no_step, value_no_step).
    all: solve [ intros; exfalso; eapply abs_no_step; eauto |
                 intros; exfalso; eapply value_no_step; eauto ].
  - inversion H2; subst; try reflexivity.
    all: try (intros; subst; reflexivity).
    all: try (intros; subst; f_equal; eauto).
    all: try (eauto using abs_no_step, value_no_step).
    all: solve [ intros; exfalso; eapply abs_no_step; eauto |
                 intros; exfalso; eapply value_no_step; eauto ].
Qed.

Lemma value_strongly_normalizing : forall v, value v -> strongly_normalizing v.
Proof.
  intros v Hv. constructor. intros v' Hs.
  exfalso. eapply value_no_step; eauto.
Qed.

Lemma sn_of_multistep : forall t v,
    t -->* v -> strongly_normalizing v -> strongly_normalizing t.
Proof.
  intros t v Hmulti Hsn.
  induction Hmulti.
  - exact Hsn.
  - apply SN_intro. intros t' Hstep.
    assert (t' = y) as Heq.
    { eapply step_deterministic; eauto. }
    subst t'.
    apply IHHmulti.
    exact Hsn.
Qed.

Lemma msubst_id : forall t, msubst id_substitution t = t.
Proof.
  induction t as [i|x|t1 IH1 t2 IH2|T t1 IH| |]; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  assert (Hrel : related_substitution empty id_substitution).
  { unfold related_substitution, empty. intros x U H. discriminate. }
  pose proof (fundamental empty t T id_substitution Hty Hrel) as Hexpr.
  unfold expression_relation in Hexpr.
  pose proof (proj2 Hexpr) as Hex.
  destruct Hex as [w Hw].
  destruct Hw as [Hm Hv].
  apply sn_of_multistep with w.
  - rewrite msubst_id in Hm. exact Hm.
  - apply value_strongly_normalizing.
    apply (value_relation_value T w). exact Hv.
Qed.

End STLCNormalizationNoneMediumTask.
