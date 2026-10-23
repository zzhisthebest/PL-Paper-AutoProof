(** STLC call-by-value strong-normalization benchmark task. *)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Relations.Relation_Definitions.
From Stdlib Require Import Lia.

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

(** ** Substitution of free variables *)

Fixpoint subst (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_app t1 t2 => tm_app (subst sigma t1) (subst sigma t2)
  | tm_abs T t1 => tm_abs T (subst sigma t1)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (subst sigma t1) (subst sigma t2) (subst sigma t3)
  end.

Definition subst_update (sigma : atom -> tm) (x : atom) (u : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then u else sigma y.

Lemma subst_update_eq : forall (sigma : atom -> tm) x u,
  subst_update sigma x u x = u.
Proof. intros. unfold subst_update. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma subst_update_neq : forall (sigma : atom -> tm) x u y,
  y <> x -> subst_update sigma x u y = sigma y.
Proof.
  intros. unfold subst_update.
  destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. congruence.
  - reflexivity.
Qed.

Lemma lc_app_inv : forall k t1 t2,
  lc_at k (tm_app t1 t2) -> lc_at k t1 /\ lc_at k t2.
Proof. intros k t1 t2 H. inversion H; subst; auto. Qed.

Lemma lc_abs_inv : forall k T t,
  lc_at k (tm_abs T t) -> lc_at (S k) t.
Proof. intros k T t H. inversion H; subst; auto. Qed.

Lemma lc_if_inv : forall k t1 t2 t3,
  lc_at k (tm_if t1 t2 t3) -> lc_at k t1 /\ lc_at k t2 /\ lc_at k t3.
Proof. intros k t1 t2 t3 H. inversion H; subst; auto. Qed.

Lemma open_rec_lc_gen : forall t j k v,
  lc_at j t -> j <= k -> open_rec k v t = t.
Proof.
  induction t as [i | x | a IHa b IHb | Ty b IHb | | | a IHa b IHb c IHBc];
    intros j k v Ht Hjk; simpl.
  - inversion Ht; subst. destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst i. lia.
    + reflexivity.
  - reflexivity.
  - apply lc_app_inv in Ht as [H1 H2].
    assert (E1 : open_rec k v a = a) by (apply IHa with (j := j); [exact H1 | exact Hjk]).
    assert (E2 : open_rec k v b = b) by (apply IHb with (j := j); [exact H2 | exact Hjk]).
    rewrite E1, E2. reflexivity.
  - apply lc_abs_inv with (T := Ty) in Ht.
    assert (E : open_rec (S k) v b = b) by (apply IHb with (j := S j); [exact Ht | lia]).
    rewrite E. reflexivity.
  - reflexivity.
  - reflexivity.
  - apply lc_if_inv in Ht as [H1 [H2 H3]].
    assert (E1 : open_rec k v a = a) by (apply IHa with (j := j); [exact H1 | exact Hjk]).
    assert (E2 : open_rec k v b = b) by (apply IHb with (j := j); [exact H2 | exact Hjk]).
    assert (E3 : open_rec k v c = c) by (apply IHBc with (j := j); [exact H3 | exact Hjk]).
    rewrite E1, E2, E3. reflexivity.
Qed.

Lemma open_rec_lc : forall k v t, locally_closed t -> open_rec k v t = t.
Proof. intros. apply open_rec_lc_gen with (j := 0); [exact H | lia]. Qed.

Lemma subst_open_rec : forall (sigma : atom -> tm) k u t,
  (forall x, locally_closed (sigma x)) ->
  subst sigma (open_rec k u t) = open_rec k (subst sigma u) (subst sigma t).
Proof.
  intros sigma k u t Hsig. revert k.
  induction t as [i | x | a IHa b IHb | Ty b IHb | | | a IHa b IHb c IHBc];
    intros k; simpl.
  - destruct (Nat.eqb k i); reflexivity.
  - symmetry. apply open_rec_lc. apply Hsig.
  - rewrite IHa, IHb; auto.
  - rewrite IHb; auto.
  - reflexivity.
  - reflexivity.
  - rewrite IHa, IHb, IHBc; auto.
Qed.

Lemma subst_id : forall t, subst (fun x : atom => tm_fvar x) t = t.
Proof.
  induction t as [i | x | a IHa b IHb | Ty b IHb | | | a IHa b IHb c IHBc]; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IHa, IHb. reflexivity.
  - rewrite IHb. reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHa, IHb, IHBc. reflexivity.
Qed.

Fixpoint fvars (t : tm) : list atom :=
  match t with
  | tm_bvar _ => nil
  | tm_fvar x => x :: nil
  | tm_app t1 t2 => fvars t1 ++ fvars t2
  | tm_abs _ t1 => fvars t1
  | tm_true => nil
  | tm_false => nil
  | tm_if t1 t2 t3 => fvars t1 ++ fvars t2 ++ fvars t3
  end.

Lemma subst_ext : forall t (sigma1 sigma2 : atom -> tm),
  (forall x, In x (fvars t) -> sigma1 x = sigma2 x) ->
  subst sigma1 t = subst sigma2 t.
Proof.
  induction t as [i | x | a IHa b IHb | Ty b IHb | | | a IHa b IHb c IHBc];
    intros sigma1 sigma2 Hagree; simpl.
  - reflexivity.
  - apply Hagree. simpl. auto.
  - assert (E1 : subst sigma1 a = subst sigma2 a).
    { apply IHa. intros y Hy. apply Hagree. simpl. apply in_or_app. left. exact Hy. }
    assert (E2 : subst sigma1 b = subst sigma2 b).
    { apply IHb. intros y Hy. apply Hagree. simpl. apply in_or_app. right. exact Hy. }
    rewrite E1, E2. reflexivity.
  - assert (E1 : subst sigma1 b = subst sigma2 b).
    { apply IHb. intros y Hy. apply Hagree. simpl. exact Hy. }
    rewrite E1. reflexivity.
  - reflexivity.
  - reflexivity.
  - assert (E1 : subst sigma1 a = subst sigma2 a).
    { apply IHa. intros y Hy. apply Hagree. simpl. apply in_or_app. left. exact Hy. }
    assert (E2 : subst sigma1 b = subst sigma2 b).
    { apply IHb. intros y Hy. apply Hagree. simpl. apply in_or_app. right. apply in_or_app. left. exact Hy. }
    assert (E3 : subst sigma1 c = subst sigma2 c).
    { apply IHBc. intros y Hy. apply Hagree. simpl. apply in_or_app. right. apply in_or_app. right. exact Hy. }
    rewrite E1, E2, E3. reflexivity.
Qed.

Fixpoint max_atom (l : list atom) : atom :=
  match l with
  | nil => 0
  | x :: rest => Nat.max x (max_atom rest)
  end.

Lemma In_max_atom : forall (l : list atom) x, In x l -> x <= max_atom l.
Proof.
  induction l as [| a rest IH]; intros x H.
  - inversion H.
  - simpl. destruct H as [-> | H].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; eauto | apply Nat.le_max_r].
Qed.

Lemma fresh_atom : forall l : list atom, exists x, ~ In x l.
Proof.
  intros l. exists (S (max_atom l)).
  intro H. apply In_max_atom in H.
  exact (Nat.nle_succ_diag_l (max_atom l) H).
Qed.

(** ** Basic properties of values, local closure, and reduction *)

Lemma value_no_step : forall v t, value v -> ~ (v --> t).
Proof.
  intros v t Hv Hstep. destruct Hv; inversion Hstep.
Qed.

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v H. destruct H as [T t Hlc | | ].
  - exact Hlc.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma value_SN : forall v, value v -> strongly_normalizing v.
Proof.
  intros v Hv. apply SN_intro. intros v' Hstep.
  exfalso. exact (value_no_step v v' Hv Hstep).
Qed.

Lemma multi_of_value_aux : forall a b,
  multi step a b -> forall v, value v -> v = a -> b = v.
Proof.
  intros a b Hm. induction Hm as [x | x y z Hxy Hyz IH]; intros v Hv Heq.
  - symmetry. exact Heq.
  - subst v. exfalso. exact (value_no_step x y Hv Hxy).
Qed.

Lemma multi_of_value : forall v v', value v -> multi step v v' -> v' = v.
Proof.
  intros v v' Hv Hm. exact (multi_of_value_aux v v' Hm v Hv eq_refl).
Qed.

Lemma multi_cases : forall (a b : tm),
  multi step a b -> a = b \/ (exists c, step a c /\ multi step c b).
Proof.
  intros a b H. destruct H as [x | x y z Hxy Hyz].
  - left. reflexivity.
  - right. exists y. split; assumption.
Qed.

Lemma SN_step : forall t t', strongly_normalizing t -> t --> t' -> strongly_normalizing t'.
Proof.
  intros t t' Hsn Hstep. destruct Hsn as [t0 Hprem]. exact (Hprem t' Hstep).
Qed.

Lemma lc_mono : forall t k k', lc_at k t -> k <= k' -> lc_at k' t.
Proof.
  induction t as [i | x | a IHa b IHb | Ty b IHb | | | a IHa b IHb c IHBc];
    intros k k' Hlc Hle; simpl in *.
  - apply lc_bvar. inversion Hlc; subst. lia.
  - apply lc_fvar.
  - apply lc_app.
    + apply IHa with (k := k) (k' := k'); [apply lc_app_inv in Hlc as [H1 H2]; exact H1 | exact Hle].
    + apply IHb with (k := k) (k' := k'); [apply lc_app_inv in Hlc as [H1 H2]; exact H2 | exact Hle].
  - apply lc_abs. apply IHb with (k := S k) (k' := S k').
    + apply lc_abs_inv with (T := Ty). exact Hlc.
    + lia.
  - apply lc_true.
  - apply lc_false.
  - apply lc_if.
    + apply IHa with (k := k) (k' := k'); [apply lc_if_inv in Hlc as [H1 [H2 H3]]; exact H1 | exact Hle].
    + apply IHb with (k := k) (k' := k'); [apply lc_if_inv in Hlc as [H1 [H2 H3]]; exact H2 | exact Hle].
    + apply IHBc with (k := k) (k' := k'); [apply lc_if_inv in Hlc as [H1 [H2 H3]]; exact H3 | exact Hle].
Qed.

Lemma lc_open_rec : forall t k u,
  lc_at (S k) t -> lc_at k u -> lc_at k (open_rec k u t).
Proof.
  induction t as [i | x | a IHa b IHb | Ty b IHb | | | a IHa b IHb c IHBc];
    intros k u Ht Hu; simpl.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst i. exact Hu.
    + inversion Ht; subst. apply Nat.eqb_neq in E. apply lc_bvar. lia.
  - apply lc_fvar.
  - apply lc_app.
    + apply IHa with (u := u); [apply lc_app_inv in Ht as [H1 H2]; exact H1 | exact Hu].
    + apply IHb with (u := u); [apply lc_app_inv in Ht as [H1 H2]; exact H2 | exact Hu].
  - apply lc_abs. apply IHb with (k := S k) (u := u).
    + apply lc_abs_inv with (T := Ty). exact Ht.
    + apply lc_mono with (k := k); [exact Hu | lia].
  - apply lc_true.
  - apply lc_false.
  - apply lc_if.
    + apply IHa with (u := u); [apply lc_if_inv in Ht as [H1 [H2 H3]]; exact H1 | exact Hu].
    + apply IHb with (u := u); [apply lc_if_inv in Ht as [H1 [H2 H3]]; exact H2 | exact Hu].
    + apply IHBc with (u := u); [apply lc_if_inv in Ht as [H1 [H2 H3]]; exact H3 | exact Hu].
Qed.

Lemma lc_open : forall t u, lc_at 1 t -> locally_closed u -> locally_closed (open t u).
Proof. intros t u Ht Hu. apply lc_open_rec with (k := 0); auto. Qed.

Lemma lc_open_inv : forall t k u,
  lc_at k u -> lc_at k (open_rec k u t) -> lc_at (S k) t.
Proof.
  induction t as [i | x | a IHa b IHb | Ty b IHb | | | a IHa b IHb c IHBc];
    intros k u Hu H; simpl in H.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst i. apply lc_bvar. lia.
    + inversion H; subst. apply Nat.eqb_neq in E. apply lc_bvar. lia.
  - apply lc_fvar.
  - apply lc_app.
    + apply IHa with (u := u); [exact Hu | apply lc_app_inv in H as [H1 H2]; exact H1].
    + apply IHb with (u := u); [exact Hu | apply lc_app_inv in H as [H1 H2]; exact H2].
  - apply lc_abs. apply IHb with (k := S k) (u := u).
    + apply lc_mono with (k := k); [exact Hu | lia].
    + apply lc_abs_inv with (T := Ty). exact H.
  - apply lc_true.
  - apply lc_false.
  - apply lc_if.
    + apply IHa with (u := u); [exact Hu | apply lc_if_inv in H as [H1 [H2 H3]]; exact H1].
    + apply IHb with (u := u); [exact Hu | apply lc_if_inv in H as [H1 [H2 H3]]; exact H2].
    + apply IHBc with (u := u); [exact Hu | apply lc_if_inv in H as [H1 [H2 H3]]; exact H3].
Qed.

Lemma lc_step : forall t t', t --> t' -> locally_closed t -> locally_closed t'.
Proof.
  intros t t' Hstep.
  induction Hstep as
    [T0 body v Hlcabs Hval
    | t1 t1' t2 Hs1 IHs1 Hlc2
    | v1 t2 t2' Hval Hs2 IHs2
    | t1 t2 Hlct1 Hlct2
    | t1 t2 Hlct1 Hlct2
    | t1 t1' t2 t3 Hs IHs Hlct2 Hlct3];
    intros Hlc; simpl in Hlc.
  - apply lc_app_inv in Hlc as [Hlab Hlv].
    apply lc_open with (t := body) (u := v).
    + apply lc_abs_inv with (T := T0). exact Hlab.
    + exact Hlv.
  - apply lc_app_inv in Hlc as [Hl1 Hl2].
    apply lc_app.
    + apply IHs1. exact Hl1.
    + exact Hl2.
  - apply lc_app_inv in Hlc as [Hl1 Hl2].
    apply lc_app.
    + exact Hl1.
    + apply IHs2. exact Hl2.
  - apply lc_if_inv in Hlc as [H1 [H2 H3]]. exact H2.
  - apply lc_if_inv in Hlc as [H1 [H2 H3]]. exact H3.
  - apply lc_if_inv in Hlc as [H1 [H2 H3]].
    apply lc_if.
    + apply IHs. exact H1.
    + exact H2.
    + exact H3.
Qed.

Lemma subst_lc_at : forall t k (sigma : atom -> tm),
  lc_at k t -> (forall x, lc_at k (sigma x)) -> lc_at k (subst sigma t).
Proof.
  induction t as [i | x | a IHa b IHb | Ty b IHb | | | a IHa b IHb c IHBc];
    intros k sigma Ht Hs; simpl.
  - exact Ht.
  - apply Hs.
  - apply lc_app.
    + apply IHa with (k := k) (sigma := sigma); [apply lc_app_inv in Ht as [H1 H2]; exact H1 | exact Hs].
    + apply IHb with (k := k) (sigma := sigma); [apply lc_app_inv in Ht as [H1 H2]; exact H2 | exact Hs].
  - apply lc_abs. apply IHb with (k := S k) (sigma := sigma).
    + apply lc_abs_inv with (T := Ty). exact Ht.
    + intros x. apply lc_mono with (k := k); [apply Hs | lia].
  - apply lc_true.
  - apply lc_false.
  - apply lc_if.
    + apply IHa with (k := k) (sigma := sigma); [apply lc_if_inv in Ht as [H1 [H2 H3]]; exact H1 | exact Hs].
    + apply IHb with (k := k) (sigma := sigma); [apply lc_if_inv in Ht as [H1 [H2 H3]]; exact H2 | exact Hs].
    + apply IHBc with (k := k) (sigma := sigma); [apply lc_if_inv in Ht as [H1 [H2 H3]]; exact H3 | exact Hs].
Qed.

(** ** The logical relation *)

Fixpoint R (T : ty) (t : tm) {struct T} : Prop :=
  match T with
  | Ty_Bool =>
      locally_closed t /\
      strongly_normalizing t /\
      (forall v, multi step t v -> value v -> (v = tm_true \/ v = tm_false))
  | Ty_Arrow T1 T2 =>
      locally_closed t /\
      strongly_normalizing t /\
      (forall v, multi step t v -> value v ->
         exists T0 body,
           v = tm_abs T0 body /\
           locally_closed (tm_abs T0 body) /\
           (forall w, V T1 w -> R T2 (open body w)))
  end
with V (T : ty) (t : tm) {struct T} : Prop :=
  match T with
  | Ty_Bool =>
      t = tm_true \/ t = tm_false
  | Ty_Arrow T1 T2 =>
      exists T0 body,
        t = tm_abs T0 body /\
        locally_closed (tm_abs T0 body) /\
        (forall w, V T1 w -> R T2 (open body w))
  end.

Lemma R_lc : forall T t, R T t -> locally_closed t.
Proof. intros T t H. destruct T; simpl in *; tauto. Qed.

Lemma R_sn : forall T t, R T t -> strongly_normalizing t.
Proof. intros T t H. destruct T; simpl in *; tauto. Qed.

Lemma R_cond : forall T t, R T t -> forall v, multi step t v -> value v -> V T v.
Proof.
  intros T t H v Hm Hv. destruct T; simpl in *;
    destruct H as (H1 & H2 & H3); apply (H3 v Hm Hv).
Qed.

Lemma R_intro : forall T t,
  locally_closed t ->
  strongly_normalizing t ->
  (forall v, multi step t v -> value v -> V T v) ->
  R T t.
Proof.
  intros T t H1 H2 H3. destruct T; simpl in *.
  - split; [exact H1 | split; [exact H2 | exact H3]].
  - split; [exact H1 | split; [exact H2 | exact H3]].
Qed.

Lemma V_lc : forall T v, V T v -> locally_closed v.
Proof.
  intros T v H. destruct T; simpl in *.
  - destruct H as [-> | ->]; apply lc_true || apply lc_false.
  - destruct H as (T0 & body & -> & Hlc & _). exact Hlc.
Qed.

Lemma V_value : forall T v, V T v -> value v.
Proof.
  intros T v H. destruct T; simpl in *.
  - destruct H as [-> | ->]; constructor.
  - destruct H as (T0 & body & -> & Hlc & _). apply v_abs. exact Hlc.
Qed.

Lemma V_sn : forall T v, V T v -> strongly_normalizing v.
Proof. intros T v H. apply value_SN. apply V_value with (T := T). exact H. Qed.

Lemma V_R : forall T v, V T v -> R T v.
Proof.
  intros T v H.
  apply R_intro.
  - apply V_lc with (T := T). exact H.
  - apply V_sn with (T := T). exact H.
  - intros v' Hm Hval. rewrite (multi_of_value v v' (V_value T v H) Hm). exact H.
Qed.

Lemma R_forward : forall T t t', R T t -> t --> t' -> R T t'.
Proof.
  intros T t t' HR Hstep.
  apply R_intro.
  - apply lc_step with (t := t); [exact Hstep | apply R_lc with (T := T); exact HR].
  - apply SN_step with (t := t); [apply R_sn with (T := T); exact HR | exact Hstep].
  - intros v Hm Hval. apply (R_cond T t HR v).
    + exact (multi_step step t t' v Hstep Hm).
    + exact Hval.
Qed.

(** ** The application lemma *)

Lemma R_app_aux : forall T1 T2 (t1 : tm),
  locally_closed t1 ->
  (forall v, multi step t1 v -> value v -> V (Ty_Arrow T1 T2) v) ->
  strongly_normalizing t1 ->
  forall (t2 : tm),
  locally_closed t2 ->
  (forall v, multi step t2 v -> value v -> V T1 v) ->
  strongly_normalizing t2 ->
  R T2 (tm_app t1 t2).
Proof.
  intros T1 T2 t1 Hlc1 Hcond1 Hsn1.
  revert Hlc1 Hcond1.
  induction Hsn1 as [t1 Hstep1 IH1].
  intros Hlc1 Hcond1 t2 Hlc2 Hcond2 Hsn2.
  revert Hlc2 Hcond2.
  induction Hsn2 as [t2 Hstep2 IH2].
  intros Hlc2 Hcond2.
  assert (Hsucc : forall s, tm_app t1 t2 --> s -> R T2 s).
  { intros s Hst. inversion Hst; subst.
    - (* ST_AppAbs *)
      assert (HVa : V (Ty_Arrow T1 T2) (tm_abs T t)).
      { apply Hcond1. apply multi_refl. apply v_abs. assumption. }
      simpl in HVa.
      destruct HVa as (T0' & body & Heq & Hlca & Hquant).
      inversion Heq; subst.
      apply Hquant.
      apply Hcond2. apply multi_refl. assumption.
    - (* ST_App1 *)
      apply (IH1 t1' H1).
      + apply lc_step with (t := t1); auto.
      + intros w Hm Hval. apply Hcond1; [exact (multi_step step t1 t1' w H1 Hm) | exact Hval].
      + exact Hlc2.
      + exact Hcond2.
      + apply SN_intro. exact Hstep2.
    - (* ST_App2 *)
      apply (IH2 t2' H3).
      + apply lc_step with (t := t2); auto.
      + intros w Hm Hval. apply Hcond2; [exact (multi_step step t2 t2' w H3 Hm) | exact Hval].
  }
  apply R_intro.
  - apply lc_app; auto.
  - apply SN_intro. intros s Hs. apply R_sn with (T := T2). apply Hsucc. exact Hs.
  - intros v Hm Hval. destruct (multi_cases _ _ Hm) as [Heq | (s & Hs & Hm')].
    + subst v. inversion Hval.
    + apply (R_cond T2 s (Hsucc s Hs) v Hm' Hval).
Qed.

Lemma R_app : forall T1 T2 (t1 : tm),
  R (Ty_Arrow T1 T2) t1 -> forall t2, R T1 t2 -> R T2 (tm_app t1 t2).
Proof.
  intros T1 T2 t1 HR1 t2 HR2.
  apply (R_app_aux T1 T2 t1).
  - apply R_lc with (T := Ty_Arrow T1 T2); exact HR1.
  - apply R_cond with (T := Ty_Arrow T1 T2); exact HR1.
  - apply R_sn with (T := Ty_Arrow T1 T2); exact HR1.
  - apply R_lc with (T := T1); exact HR2.
  - apply R_cond with (T := T1); exact HR2.
  - apply R_sn with (T := T1); exact HR2.
Qed.

(** ** The conditional lemma *)

Lemma R_if_aux : forall T (t1 : tm),
  locally_closed t1 ->
  (forall v, multi step t1 v -> value v -> V Ty_Bool v) ->
  strongly_normalizing t1 ->
  forall t2 t3, R T t2 -> R T t3 -> R T (tm_if t1 t2 t3).
Proof.
  intros T t1 Hlc1 Hcond1 Hsn1.
  revert Hlc1 Hcond1.
  induction Hsn1 as [t1 Hstep1 IH1].
  intros Hlc1 Hcond1 t2 t3 HR2 HR3.
  assert (Hsucc : forall s, tm_if t1 t2 t3 --> s -> R T s).
  { intros s Hst. inversion Hst; subst.
    - (* ST_IfTrue *) exact HR2.
    - (* ST_IfFalse *) exact HR3.
    - (* ST_If *)
      apply (IH1 t1' H2).
      + apply lc_step with (t := t1); auto.
      + intros w Hm Hval. apply Hcond1; [exact (multi_step step t1 t1' w H2 Hm) | exact Hval].
      + exact HR2.
      + exact HR3. }
  apply R_intro.
  - apply lc_if; [exact Hlc1 | apply R_lc with (T := T) | apply R_lc with (T := T)]; auto.
  - apply SN_intro. intros s Hs. apply R_sn with (T := T). apply Hsucc. exact Hs.
  - intros v Hm Hval. destruct (multi_cases _ _ Hm) as [Heq | (s & Hs & Hm')].
    + subst v. inversion Hval.
    + apply (R_cond T s (Hsucc s Hs) v Hm' Hval).
Qed.

Lemma R_if : forall T t1 t2 t3,
  R Ty_Bool t1 -> R T t2 -> R T t3 -> R T (tm_if t1 t2 t3).
Proof.
  intros T t1 t2 t3 HR1 HR2 HR3.
  apply (R_if_aux T t1).
  - apply R_lc with (T := Ty_Bool); exact HR1.
  - apply R_cond with (T := Ty_Bool); exact HR1.
  - apply R_sn with (T := Ty_Bool); exact HR1.
  - exact HR2.
  - exact HR3.
Qed.

(** ** Well-scopedness of typed terms *)

Lemma has_type_lc : forall Gamma t T, has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T H. induction H as
    [Gamma0 x T0 Heq
    | L Gamma0 T1 T2 t1 Hbody IHbody
    | Gamma0 t1 t2 T1 T2 H1 IH1 H2 IH2
    | Gamma0
    | Gamma0
    | Gamma0 t1 t2 t3 T0 H1 IH1 H2 IH2 H3 IH3].
  - apply lc_fvar.
  - apply lc_abs. destruct (fresh_atom L) as [x Hx].
    apply lc_open_inv with (u := tm_fvar x) (k := 0).
    + apply lc_fvar.
    + apply IHbody. exact Hx.
  - apply lc_app; auto.
  - apply lc_true.
  - apply lc_false.
  - apply lc_if; auto.
Qed.

(** ** The fundamental lemma *)

Definition env_ok (Gamma : context) (sigma : atom -> tm) : Prop :=
  forall x T, Gamma x = Some T -> R T (sigma x).

Lemma fundamental : forall Gamma t T,
  has_type Gamma t T ->
  forall sigma,
    (forall x, locally_closed (sigma x)) ->
    env_ok Gamma sigma ->
    R T (subst sigma t).
Proof.
  intros Gamma t T Hty.
  induction Hty as
    [Gamma0 x T0 Heq
    | L Gamma0 T1 T2 t1 Hbody IHbody
    | Gamma0 t1 t2 T1 T2 H1 IH1 H2 IH2
    | Gamma0
    | Gamma0
    | Gamma0 t1 t2 t3 T0 H1 IH1 H2 IH2 H3 IH3].
  - (* T_Var *) intros sigma HlcS Henv. simpl. apply Henv. exact Heq.
  - (* T_Abs *) intros sigma HlcS Henv.
    change (R (Ty_Arrow T1 T2) (tm_abs T1 (subst sigma t1))).
    assert (Hlc_abs : locally_closed (tm_abs T1 (subst sigma t1))).
    { apply lc_abs. apply subst_lc_at with (k := 1).
      - apply lc_abs_inv with (T := T1).
        apply has_type_lc with (Gamma := Gamma0) (T := Ty_Arrow T1 T2).
        exact (T_Abs L Gamma0 T1 T2 t1 Hbody).
      - intros x. apply lc_mono with (k := 0); [apply HlcS | lia]. }
    apply R_intro.
    + exact Hlc_abs.
    + apply value_SN. apply v_abs. exact Hlc_abs.
    + intros v Hm Hval. destruct (multi_cases _ _ Hm) as [Heq | (s & Hs & Hm')].
      * subst v. simpl. exists T1, (subst sigma t1).
        split; [reflexivity | split; [exact Hlc_abs | ]].
        intros w HVw.
        destruct (fresh_atom (L ++ fvars t1)) as [x Hx].
        assert (HxL : ~ In x L) by (intro H; apply Hx; apply in_or_app; left; exact H).
        assert (Hxfv : ~ In x (fvars t1)) by (intro H; apply Hx; apply in_or_app; right; exact H).
        assert (HlcU : forall y, locally_closed (subst_update sigma x w y)).
        { intros y. unfold subst_update. destruct (Nat.eqb x y) eqn:Ey.
          - apply Nat.eqb_eq in Ey. subst y. apply V_lc with (T := T1). exact HVw.
          - apply HlcS. }
        assert (HRx : R T2 (subst (subst_update sigma x w) (open t1 (tm_fvar x)))).
        { apply (IHbody x HxL (subst_update sigma x w)).
          - exact HlcU.
          - intros y U Hy. unfold subst_update. destruct (Nat.eqb x y) eqn:Ey.
            + apply Nat.eqb_eq in Ey. subst y.
              unfold update in Hy. simpl in Hy. rewrite Nat.eqb_refl in Hy.
              injection Hy as HU. subst U. apply V_R. exact HVw.
            + unfold update in Hy. rewrite Ey in Hy. apply Henv. exact Hy. }
        unfold open in HRx.
        rewrite (subst_open_rec (subst_update sigma x w) 0 (tm_fvar x) t1 HlcU) in HRx.
        simpl in HRx.
        rewrite subst_update_eq in HRx.
        assert (Heqsubst : subst (subst_update sigma x w) t1 = subst sigma t1).
        { apply subst_ext. intros y Hy. unfold subst_update. destruct (Nat.eqb x y) eqn:Ey.
          - apply Nat.eqb_eq in Ey. subst y. exfalso. apply Hxfv. exact Hy.
          - reflexivity. }
        rewrite Heqsubst in HRx.
        exact HRx.
      * exfalso. exact (value_no_step (tm_abs T1 (subst sigma t1)) s (v_abs T1 (subst sigma t1) Hlc_abs) Hs).
  - (* T_App *) intros sigma HlcS Henv. simpl. apply (R_app T1 T2 (subst sigma t1)).
    + apply IH1; auto.
    + apply IH2; auto.
  - (* T_True *) intros sigma HlcS Henv. change (R Ty_Bool tm_true). apply R_intro.
    + apply lc_true.
    + apply value_SN. constructor.
    + intros v Hm Hval. destruct (multi_cases _ _ Hm) as [Heq | (s & Hs & Hm')].
      * subst v. left. reflexivity.
      * exfalso. exact (value_no_step tm_true s v_true Hs).
  - (* T_False *) intros sigma HlcS Henv. change (R Ty_Bool tm_false). apply R_intro.
    + apply lc_false.
    + apply value_SN. constructor.
    + intros v Hm Hval. destruct (multi_cases _ _ Hm) as [Heq | (s & Hs & Hm')].
      * subst v. right. reflexivity.
      * exfalso. exact (value_no_step tm_false s v_false Hs).
  - (* T_If *) intros sigma HlcS Henv. simpl. apply R_if.
    + apply IH1; auto.
    + apply IH2; auto.
    + apply IH3; auto.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  assert (HR : R T (subst (fun x : atom => tm_fvar x) t)).
  { apply (fundamental empty t T Hty).
    - intros x. apply lc_fvar.
    - intros x U Hx. unfold empty in Hx. discriminate Hx. }
  rewrite subst_id in HR.
  apply R_sn with (T := T). exact HR.
Qed.

End STLCCBVNormalizationTask.
