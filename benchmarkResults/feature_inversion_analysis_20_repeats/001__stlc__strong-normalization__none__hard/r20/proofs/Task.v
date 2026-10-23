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

(** ** Auxiliary definitions *)

(** Free-variable substitution (substitution only touches [tm_fvar]). *)

Fixpoint subst (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_app t1 t2 => tm_app (subst sigma t1) (subst sigma t2)
  | tm_abs T t1 => tm_abs T (subst sigma t1)
  | tm_true => tm_true
  | tm_false => tm_false
  end.

Definition env_update (sigma : atom -> tm) (x : atom) (v : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then v else sigma y.

(** Free variables of a term. *)

Fixpoint fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ => nil
  | tm_fvar x => x :: nil
  | tm_app t1 t2 => fv t1 ++ fv t2
  | tm_abs _ t1 => fv t1
  | tm_true => nil
  | tm_false => nil
  end.

Definition fresh (L : list atom) : atom := S (fold_right Nat.max 0 L).

(** ** Basic properties of local closure *)

Lemma lc_at_mono : forall k k' t,
  k <= k' -> lc_at k t -> lc_at k' t.
Proof.
  intros k k' t Hle H. revert k' Hle.
  induction H; intros k' Hle.
  - apply lc_bvar. lia.
  - apply lc_fvar.
  - apply lc_app; auto.
  - apply lc_abs. apply IHlc_at. lia.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma open_lc : forall k u t,
  lc_at k u -> lc_at (S k) t -> lc_at k (open_rec k u t).
Proof.
  intros k u t Hu. revert k u Hu.
  induction t; intros k u Hu Ht; simpl.
  - inversion Ht; subst.
    destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. exact Hu.
    + apply Nat.eqb_neq in E. apply lc_bvar. lia.
  - apply lc_fvar.
  - inversion Ht; subst. apply lc_app; auto.
  - inversion Ht; subst. apply lc_abs.
    apply IHt with (k := S k) (u := u).
    + apply lc_at_mono with (k := k); [lia | exact Hu].
    + assumption.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma lc_open_back : forall k u t,
  lc_at k (open_rec k u t) -> lc_at (S k) t.
Proof.
  intros k u t. revert k u.
  induction t; intros k u H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. apply lc_bvar. lia.
    + apply Nat.eqb_neq in E. inversion H; subst. apply lc_bvar. lia.
  - apply lc_fvar.
  - inversion H; subst. apply lc_app.
    + apply IHt1 with (u := u); assumption.
    + apply IHt2 with (u := u); assumption.
  - inversion H; subst. apply lc_abs.
    apply IHt with (k := S k) (u := u). assumption.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma value_lc : forall v, value v -> lc_at 0 v.
Proof.
  intros v H. induction H.
  - assumption.
  - apply lc_true.
  - apply lc_false.
Qed.

(** ** Basic properties of strong normalization *)

Lemma sn_abs : forall T t, strongly_normalizing (tm_abs T t).
Proof. intros. constructor. intros t' H. inversion H. Qed.

Lemma sn_true : strongly_normalizing tm_true.
Proof. constructor. intros t' H. inversion H. Qed.

Lemma sn_false : strongly_normalizing tm_false.
Proof. constructor. intros t' H. inversion H. Qed.

Lemma sn_value : forall v, value v -> strongly_normalizing v.
Proof.
  intros v H. induction H.
  - apply sn_abs.
  - apply sn_true.
  - apply sn_false.
Qed.

Lemma value_no_step : forall v, value v -> forall t', ~ step v t'.
Proof.
  intros v H. induction H; intros t' Hs; inversion Hs.
Qed.

Lemma sn_step : forall t t',
  strongly_normalizing t -> step t t' -> strongly_normalizing t'.
Proof.
  intros t t' Hsn Hstep. inversion Hsn; subst.
  match goal with
  | H : forall y, t --> y -> strongly_normalizing y |- _ => apply H; exact Hstep
  end.
Qed.

Lemma abs_no_step : forall T t s, ~ step (tm_abs T t) s.
Proof. intros T t s H. inversion H. Qed.

Lemma true_no_step : forall s, ~ step tm_true s.
Proof. intros s H. inversion H. Qed.

Lemma false_no_step : forall s, ~ step tm_false s.
Proof. intros s H. inversion H. Qed.

Lemma step_det : forall t t1 t2,
  step t t1 -> step t t2 -> t1 = t2.
Proof.
  intros t t1 t2 H1. revert t2.
  induction H1; intros s H2;
    inversion H2; subst; clear H2;
    try reflexivity;
    try (exfalso;
         match goal with
         | Hs : step (tm_abs _ _) _ |- _ => exact (abs_no_step _ _ _ Hs)
         | Hv : value ?v, Hs : step ?v _ |- _ => exact (value_no_step v Hv _ Hs)
         end);
    try (f_equal; eauto).
Qed.

Lemma sn_back_step : forall t t',
  strongly_normalizing t' -> step t t' -> strongly_normalizing t.
Proof.
  intros t t' Hsn Hstep. constructor. intros t'' Hstep''.
  assert (t'' = t') by (eapply step_det; eauto).
  subst. exact Hsn.
Qed.

(** ** Multi-step lemmas *)

Lemma multi_trans : forall {X : Type} (R : relation X) (x y z : X),
  multi R x y -> multi R y z -> multi R x z.
Proof.
  intros X R x y z H1. revert z.
  induction H1 as [x0 | x0 y0 z0 Hstep Hm IH]; intros w H2.
  - exact H2.
  - apply multi_step with (y := y0); [exact Hstep | apply IH; exact H2].
Qed.

Lemma sn_multi_back : forall t t',
  multi step t t' -> strongly_normalizing t' -> strongly_normalizing t.
Proof.
  intros t t' Hm. induction Hm; intros Hsn.
  - exact Hsn.
  - apply sn_back_step with (t' := y).
    + apply IHHm. exact Hsn.
    + exact H.
Qed.

Lemma multi_app1 : forall t1 t1' t2,
  multi step t1 t1' -> lc_at 0 t2 ->
  multi step (tm_app t1 t2) (tm_app t1' t2).
Proof.
  intros t1 t1' t2 Hm. induction Hm; intros Hlc.
  - apply multi_refl.
  - apply multi_step with (y := tm_app y t2).
    + apply ST_App1; assumption.
    + apply IHHm. exact Hlc.
Qed.

Lemma multi_app2 : forall v1 t2 t2',
  value v1 -> multi step t2 t2' ->
  multi step (tm_app v1 t2) (tm_app v1 t2').
Proof.
  intros v1 t2 t2' Hv Hm. induction Hm.
  - apply multi_refl.
  - apply multi_step with (y := tm_app v1 y).
    + apply ST_App2; assumption.
    + exact IHHm.
Qed.

(** ** Substitution lemmas *)

Lemma open_rec_lc : forall k u t,
  lc_at k t -> open_rec k u t = t.
Proof.
  intros k u t H. induction H; simpl.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. exfalso. lia.
    + reflexivity.
  - reflexivity.
  - rewrite IHlc_at1, IHlc_at2. reflexivity.
  - rewrite IHlc_at. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma subst_open_comm : forall sigma k u t,
  (forall x, lc_at 0 (sigma x)) ->
  subst sigma (open_rec k u t) = open_rec k (subst sigma u) (subst sigma t).
Proof.
  intros sigma k u t Hsig. revert k u.
  induction t; intros k u; simpl.
  - destruct (Nat.eqb k n); simpl; reflexivity.
  - rewrite open_rec_lc. reflexivity.
    apply lc_at_mono with (k := 0); [lia | apply Hsig].
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma subst_ext : forall sigma sigma' t,
  (forall x, In x (fv t) -> sigma x = sigma' x) ->
  subst sigma t = subst sigma' t.
Proof.
  intros sigma sigma' t H. induction t; simpl.
  - reflexivity.
  - apply H. simpl. auto.
  - assert (E1 : subst sigma t1 = subst sigma' t1).
    { apply IHt1. intros x Hx. apply H. simpl. apply in_app_iff. left. exact Hx. }
    assert (E2 : subst sigma t2 = subst sigma' t2).
    { apply IHt2. intros x Hx. apply H. simpl. apply in_app_iff. right. exact Hx. }
    rewrite E1, E2. reflexivity.
  - rewrite IHt. reflexivity.
    intros x Hx. apply H. simpl. exact Hx.
  - reflexivity.
  - reflexivity.
Qed.

Lemma env_update_eq : forall sigma x v, env_update sigma x v x = v.
Proof. intros. unfold env_update. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma env_update_neq : forall sigma x y v,
  x <> y -> env_update sigma x v y = sigma y.
Proof.
  intros. unfold env_update. destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. contradiction.
  - reflexivity.
Qed.

Lemma update_eq : forall Gamma x T, update Gamma x T x = Some T.
Proof. intros. unfold update. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma update_neq : forall Gamma x y T,
  x <> y -> update Gamma x T y = Gamma y.
Proof.
  intros. unfold update. destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. contradiction.
  - reflexivity.
Qed.

Lemma subst_env_update_ext : forall sigma x v t,
  ~ In x (fv t) -> subst (env_update sigma x v) t = subst sigma t.
Proof.
  intros sigma x v t Hx. apply subst_ext. intros y Hy.
  assert (Hxy : x <> y) by (intro E; apply Hx; subst; exact Hy).
  apply env_update_neq. exact Hxy.
Qed.

Lemma subst_id : forall t, subst (fun x => tm_fvar x) t = t.
Proof.
  induction t; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma subst_lc : forall k t sigma,
  lc_at k t -> (forall x, lc_at 0 (sigma x)) -> lc_at k (subst sigma t).
Proof.
  intros k t. revert k. induction t; intros k sigma Hlc Hsig; simpl.
  - apply lc_bvar. inversion Hlc; lia.
  - apply lc_at_mono with (k := 0); [lia | apply Hsig].
  - inversion Hlc; subst. apply lc_app.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
  - inversion Hlc; subst. apply lc_abs. apply IHt; assumption.
  - apply lc_true.
  - apply lc_false.
Qed.

(** ** Freshness *)

Lemma fold_right_max_bound : forall L x,
  In x L -> x <= fold_right Nat.max 0 L.
Proof.
  induction L as [|a L IH]; intros x Hin.
  - inversion Hin.
  - simpl in Hin. destruct Hin as [-> | Hin].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; exact Hin | apply Nat.le_max_r].
Qed.

Lemma fresh_gt : forall L x, In x L -> x < fresh L.
Proof.
  intros. unfold fresh. pose proof (fold_right_max_bound L x H). lia.
Qed.

Lemma fresh_fresh : forall L, ~ In (fresh L) L.
Proof.
  intros L H. pose proof (fresh_gt L (fresh L) H). lia.
Qed.

(** ** Typing implies local closure *)

Lemma typing_lc : forall Gamma t T,
  has_type Gamma t T -> lc_at 0 t.
Proof.
  intros Gamma t T H.
  induction H as [G x S Heq
                 | L G T1 T2 t1 Hprem IHprem
                 | G a b T1 T2 Ha IHa Hb IHb
                 | G
                 | G].
  - apply lc_fvar.
  - apply lc_abs.
    pose (x := fresh L).
    assert (Hx : ~ In x L) by (apply fresh_fresh).
    specialize (IHprem x Hx).
    apply lc_open_back with (k := 0) (u := tm_fvar x).
    simpl. exact IHprem.
  - apply lc_app; assumption.
  - apply lc_true.
  - apply lc_false.
Qed.

(** ** A type-indexed logical relation

    [V T t] is the "value-like" relation; [C T t] is the "computation"
    relation: locally closed, strongly normalizing, and reducing to a value
    in [V T].  Both are defined simultaneously by recursion on the type. *)

Fixpoint CV (T : ty) : (tm -> Prop) * (tm -> Prop) :=
  match T with
  | Ty_Bool =>
      (fun t => lc_at 0 t /\ (t = tm_true \/ t = tm_false),
       fun t => lc_at 0 t /\ strongly_normalizing t /\
                 (exists v, multi step t v /\ value v /\
                    (lc_at 0 v /\ (v = tm_true \/ v = tm_false))))
  | Ty_Arrow T1 T2 =>
      let C1 := snd (CV T1) in
      let C2 := snd (CV T2) in
      let Varr := fun t => lc_at 0 t /\
                           (forall u, C1 u -> C2 (tm_app t u)) in
      (Varr,
       fun t => lc_at 0 t /\ strongly_normalizing t /\
                (exists v, multi step t v /\ value v /\ Varr v))
  end.

Definition V (T : ty) : tm -> Prop := fst (CV T).
Definition C (T : ty) : tm -> Prop := snd (CV T).

Lemma V_Bool : forall t,
  V Ty_Bool t <-> lc_at 0 t /\ (t = tm_true \/ t = tm_false).
Proof.
  intros t. unfold V, CV. cbn. split; intros H; exact H.
Qed.

Lemma V_Arrow : forall T1 T2 t,
  V (Ty_Arrow T1 T2) t <->
  lc_at 0 t /\ (forall u, C T1 u -> C T2 (tm_app t u)).
Proof.
  intros T1 T2 t. unfold V, CV, C. cbn. split; intros H; exact H.
Qed.

Lemma C_Bool : forall t,
  C Ty_Bool t <->
  lc_at 0 t /\ strongly_normalizing t /\
  (exists v, multi step t v /\ value v /\ V Ty_Bool v).
Proof.
  intros t. unfold C, V, CV. cbn. split; intros H; exact H.
Qed.

Lemma C_Arrow : forall T1 T2 t,
  C (Ty_Arrow T1 T2) t <->
  lc_at 0 t /\ strongly_normalizing t /\
  (exists v, multi step t v /\ value v /\ V (Ty_Arrow T1 T2) v).
Proof.
  intros T1 T2 t. unfold C, V, CV. cbn. split; intros H; exact H.
Qed.

Lemma C_lc : forall T t, C T t -> lc_at 0 t.
Proof.
  intros T t H. destruct T as [|T1 T2].
  - apply (proj1 (C_Bool t)) in H. tauto.
  - apply (proj1 (C_Arrow T1 T2 t)) in H. tauto.
Qed.

Lemma C_sn : forall T t, C T t -> strongly_normalizing t.
Proof.
  intros T t H. destruct T as [|T1 T2].
  - apply (proj1 (C_Bool t)) in H. tauto.
  - apply (proj1 (C_Arrow T1 T2 t)) in H. tauto.
Qed.

Lemma C_halts : forall T t,
  C T t -> exists v, multi step t v /\ value v /\ V T v.
Proof.
  intros T t H. destruct T as [|T1 T2].
  - apply (proj1 (C_Bool t)) in H. tauto.
  - apply (proj1 (C_Arrow T1 T2 t)) in H. tauto.
Qed.

Lemma V_lc : forall T t, V T t -> lc_at 0 t.
Proof.
  intros T t H. destruct T as [|T1 T2].
  - apply (proj1 (V_Bool t)) in H. tauto.
  - apply (proj1 (V_Arrow T1 T2 t)) in H. tauto.
Qed.

Lemma C_intro : forall T t,
  lc_at 0 t -> strongly_normalizing t ->
  (exists v, multi step t v /\ value v /\ V T v) -> C T t.
Proof.
  intros T t Hlc Hsn Hex. destruct T as [|T1 T2].
  - apply C_Bool. tauto.
  - apply C_Arrow. tauto.
Qed.

Lemma C_elim : forall T t,
  C T t -> lc_at 0 t /\ strongly_normalizing t /\
            (exists v, multi step t v /\ value v /\ V T v).
Proof.
  intros T t H. destruct T as [|T1 T2].
  - apply (proj1 (C_Bool t)); exact H.
  - apply (proj1 (C_Arrow T1 T2 t)); exact H.
Qed.

Lemma V_value_C : forall T v, value v -> V T v -> C T v.
Proof.
  intros T v Hv HV.
  apply C_intro.
  - apply V_lc in HV. exact HV.
  - apply sn_value. exact Hv.
  - exists v. split; [apply multi_refl | split; assumption].
Qed.

Lemma V_Arrow_apply : forall T1 T2 t u,
  V (Ty_Arrow T1 T2) t -> C T1 u -> C T2 (tm_app t u).
Proof.
  intros T1 T2 t u HV Hu.
  apply (proj1 (V_Arrow T1 T2 t)) in HV.
  destruct HV as (Hlc & HVapp). apply HVapp. exact Hu.
Qed.

(** Semantic application: computations of arrow type applied to computations
    of the argument type are computations of the result type. *)

Lemma C_app : forall T1 T2 t1 t2,
  C (Ty_Arrow T1 T2) t1 -> C T1 t2 -> C T2 (tm_app t1 t2).
Proof.
  intros T1 T2 t1 t2 HC1 HC2.
  destruct (C_elim _ _ HC1) as (Hlc1 & Hsn1 & Hex1).
  destruct (C_elim _ _ HC2) as (Hlc2 & Hsn2 & Hex2).
  destruct Hex1 as (v1 & Hm1 & Hval1 & HV1).
  pose proof (proj1 (V_Arrow T1 T2 v1) HV1) as HV1'.
  destruct HV1' as (Hlcv1 & HVapp1).
  assert (HCv1t2 : C T2 (tm_app v1 t2)) by (apply HVapp1; exact HC2).
  destruct (C_elim _ _ HCv1t2) as (Hlcv1t2 & Hsnv1t2 & Hexv1t2).
  destruct Hexv1t2 as (w & Hmw & Hvalw & HVw).
  assert (Hm_app1 : multi step (tm_app t1 t2) (tm_app v1 t2))
    by (apply multi_app1; assumption).
  apply C_intro.
  - apply lc_app; assumption.
  - apply sn_multi_back with (t' := tm_app v1 t2); assumption.
  - exists w. split.
    + apply multi_trans with (y := tm_app v1 t2); assumption.
    + split; assumption.
Qed.

(** ** Semantic typing environments *)

Definition env_ok (Gamma : context) (sigma : atom -> tm) : Prop :=
  (forall x, lc_at 0 (sigma x)) /\
  (forall x S, Gamma x = Some S -> C S (sigma x)).

Definition sem_type (Gamma : context) (t : tm) (T : ty) : Prop :=
  forall sigma, env_ok Gamma sigma -> C T (subst sigma t).

(** ** Fundamental theorem *)

Lemma fundamental : forall Gamma t T,
  has_type Gamma t T -> sem_type Gamma t T.
Proof.
  intros Gamma t T H.
  induction H as [G x S Heq
                 | L G T1 T2 t1 Hprem IHprem
                 | G a b T1 T2 Ha IHa Hb IHb
                 | G
                 | G].
  - (* T_Var *)
    unfold sem_type. intros sigma [Hlcs Henv]. simpl.
    apply Henv. exact Heq.
  - (* T_Abs *)
    unfold sem_type. intros sigma [Hlcs Henv]. simpl.
    set (body := subst sigma t1).
    pose (x := fresh (L ++ fv t1)).
    assert (HxL : ~ In x L).
    { intro HIn. apply (fresh_fresh (L ++ fv t1)). apply in_app_iff. left. exact HIn. }
    assert (Hxfv : ~ In x (fv t1)).
    { intro HIn. apply (fresh_fresh (L ++ fv t1)). apply in_app_iff. right. exact HIn. }
    assert (Hpx : has_type (update G x T1) (open t1 (tm_fvar x)) T2)
      by (apply Hprem; exact HxL).
    assert (Hlc1 : lc_at 1 t1).
    { apply lc_open_back with (k := 0) (u := tm_fvar x).
      apply (typing_lc (update G x T1) (open t1 (tm_fvar x)) T2). exact Hpx. }
    assert (Hlcbody : lc_at 1 body).
    { unfold body. apply subst_lc with (k := 1); [exact Hlc1 | exact Hlcs]. }
    assert (Hlcabs : lc_at 0 (tm_abs T1 body)) by (apply lc_abs; exact Hlcbody).
    assert (Hsem : sem_type (update G x T1) (open t1 (tm_fvar x)) T2)
      by (apply IHprem; exact HxL).
    apply C_intro.
    + exact Hlcabs.
    + apply sn_abs.
    + exists (tm_abs T1 body). split.
      * apply multi_refl.
      * split.
        -- apply v_abs. exact Hlcabs.
        -- apply (proj2 (V_Arrow T1 T2 (tm_abs T1 body))). split.
           ++ exact Hlcabs.
           ++ intros u Hu.
              destruct (C_elim _ _ Hu) as (Hlcu & Hsnu & Hexu).
              destruct Hexu as (w & Hmuw & Hvalw & HVw).
              assert (HCw : C T1 w) by (apply V_value_C; assumption).
              assert (HCopen : C T2 (subst (env_update sigma x w)
                                             (open t1 (tm_fvar x)))).
              { apply Hsem. unfold env_ok. split.
                - intros y. unfold env_update.
                  destruct (Nat.eqb x y) eqn:E.
                  + apply C_lc in HCw. exact HCw.
                  + apply Hlcs.
                - intros y S Hy.
                  destruct (Nat.eqb x y) eqn:E.
                  + apply Nat.eqb_eq in E. subst y.
                    rewrite update_eq in Hy. injection Hy as HyS. subst S.
                    rewrite env_update_eq. exact HCw.
                  + apply Nat.eqb_neq in E.
                    rewrite (update_neq G x y T1 E) in Hy.
                    rewrite (env_update_neq sigma x y w E).
                    apply Henv. exact Hy. }
              assert (Heq : subst (env_update sigma x w) (open t1 (tm_fvar x))
                            = open body w).
              { unfold body, open.
                rewrite (subst_open_comm (env_update sigma x w) 0 (tm_fvar x) t1).
                - simpl. rewrite env_update_eq.
                  rewrite (subst_env_update_ext sigma x w t1 Hxfv).
                  reflexivity.
                - intros y. unfold env_update.
                  destruct (Nat.eqb x y) eqn:E.
                  + apply C_lc in HCw. exact HCw.
                  + apply Hlcs. }
              rewrite Heq in HCopen.
              apply C_intro.
              { apply lc_app; [exact Hlcabs | exact Hlcu]. }
              { assert (Hm2 : multi step (tm_app (tm_abs T1 body) u)
                                          (tm_app (tm_abs T1 body) w))
                  by (apply multi_app2; [apply v_abs; exact Hlcabs | exact Hmuw]).
                assert (Hbeta : step (tm_app (tm_abs T1 body) w) (open body w))
                  by (apply ST_AppAbs; [exact Hlcabs | exact Hvalw]).
                assert (Hmtot : multi step (tm_app (tm_abs T1 body) u) (open body w)).
                { apply multi_trans with (y := tm_app (tm_abs T1 body) w).
                  - exact Hm2.
                  - apply multi_step with (y := open body w).
                    + exact Hbeta.
                    + apply multi_refl. }
                apply sn_multi_back with (t' := open body w).
                - exact Hmtot.
                - apply (C_sn T2 (open body w)). exact HCopen. }
              { destruct (C_elim _ _ HCopen) as (_ & _ & Hexo).
                destruct Hexo as (z & Hmoz & Hvalz & HVz).
                exists z. split.
                - assert (Hm2' : multi step (tm_app (tm_abs T1 body) u)
                                             (tm_app (tm_abs T1 body) w))
                     by (apply multi_app2; [apply v_abs; exact Hlcabs | exact Hmuw]).
                  assert (Hbeta' : step (tm_app (tm_abs T1 body) w) (open body w))
                     by (apply ST_AppAbs; [exact Hlcabs | exact Hvalw]).
                  apply multi_trans with (y := tm_app (tm_abs T1 body) w).
                  + exact Hm2'.
                  + apply multi_trans with (y := open body w).
                    * apply multi_step with (y := open body w).
                      -- exact Hbeta'.
                      -- apply multi_refl.
                    * exact Hmoz.
                - split; assumption. }
  - (* T_App *)
    unfold sem_type. intros sigma [Hlcs Henv]. simpl.
    apply C_app with T1.
    + apply IHa. split; assumption.
    + apply IHb. split; assumption.
  - (* T_True *)
    unfold sem_type. intros sigma [Hlcs Henv]. simpl.
    apply V_value_C.
    + apply v_true.
    + apply (proj2 (V_Bool tm_true)). split.
      * apply lc_true.
      * left. reflexivity.
  - (* T_False *)
    unfold sem_type. intros sigma [Hlcs Henv]. simpl.
    apply V_value_C.
    + apply v_false.
    + apply (proj2 (V_Bool tm_false)). split.
      * apply lc_false.
      * right. reflexivity.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T H.
  pose proof (fundamental empty t T H) as Hsem.
  assert (Henv : env_ok empty (fun x => tm_fvar x)).
  { unfold env_ok. split.
    - intros x. apply lc_fvar.
    - intros x S Hx. unfold empty in Hx. discriminate Hx. }
  pose proof (Hsem (fun x => tm_fvar x) Henv) as HC.
  rewrite subst_id in HC.
  apply C_sn in HC. exact HC.
Qed.

End STLCNormalizationNoneHardTask.
