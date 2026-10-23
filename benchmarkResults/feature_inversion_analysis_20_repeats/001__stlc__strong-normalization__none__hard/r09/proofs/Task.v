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

(* ============================================================ *)
(* Infrastructure for the strong normalization proof.           *)
(* ============================================================ *)

(* ---------------- basic locally nameless lemmas ------------- *)

Lemma lc_at_app_inv : forall k t1 t2,
  lc_at k (tm_app t1 t2) -> lc_at k t1 /\ lc_at k t2.
Proof. intros k t1 t2 H. inversion H; subst; auto. Qed.

Lemma lc_at_abs_inv : forall k T t, lc_at k (tm_abs T t) -> lc_at (S k) t.
Proof. intros k T t H. inversion H; subst; auto. Qed.

Lemma lc_at_bvar_inv : forall k i, lc_at k (tm_bvar i) -> i < k.
Proof. intros k i H. inversion H; subst; auto. Qed.

Lemma lc_at_weaken : forall t k j, lc_at k t -> k <= j -> lc_at j t.
Proof.
  induction t as [n | x | t1 IH1 t2 IH2 | T t1 IH | | ];
    intros k j H Hle.
  - apply lc_at_bvar_inv in H. apply lc_bvar. lia.
  - apply lc_fvar.
  - apply lc_at_app_inv in H as [H1 H2]. apply lc_app.
    + apply IH1 with (k := k); assumption.
    + apply IH2 with (k := k); assumption.
  - apply lc_abs. apply IH with (k := S k).
    + apply lc_at_abs_inv in H. assumption.
    + lia.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma open_rec_id : forall t k u, lc_at k t -> open_rec k u t = t.
Proof.
  induction t as [n | x | t1 IH1 t2 IH2 | T t1 IH | | ];
    intros k u Hlc; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E.
      pose proof (lc_at_bvar_inv k n Hlc) as Hlt.
      rewrite E in Hlt. lia.
    + reflexivity.
  - reflexivity.
  - apply lc_at_app_inv in Hlc as [H1 H2].
    rewrite (IH1 k u H1), (IH2 k u H2). reflexivity.
  - apply lc_at_abs_inv in Hlc.
    rewrite (IH (S k) u Hlc). reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma lc_open_rec : forall t k u,
  lc_at (S k) t -> lc_at k u -> lc_at k (open_rec k u t).
Proof.
  induction t as [n | x | t1 IH1 t2 IH2 | T t1 IH | | ];
    intros k u Ht Hu; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. assumption.
    + apply lc_bvar. apply Nat.eqb_neq in E.
      pose proof (lc_at_bvar_inv (S k) n Ht). lia.
  - apply lc_fvar.
  - apply lc_at_app_inv in Ht as [H1 H2].
    apply lc_app; [apply IH1 | apply IH2]; assumption.
  - apply lc_abs. apply IH with (k := S k).
    + apply lc_at_abs_inv in Ht. assumption.
    + exact (lc_at_weaken u k (S k) Hu (le_S k k (le_n k))).
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma lc_open_inv : forall t k j u,
  j <= k -> lc_at k (open_rec j u t) -> lc_at (S k) t.
Proof.
  induction t as [n | x | t1 IH1 t2 IH2 | T t1 IH | | ];
    intros k j u Hjk H; simpl in H.
  - destruct (Nat.eqb j n) eqn:E.
    + apply Nat.eqb_eq in E. subst. apply lc_bvar. lia.
    + apply lc_bvar. apply lc_at_bvar_inv in H. lia.
  - apply lc_fvar.
  - apply lc_at_app_inv in H as [H1 H2]. apply lc_app.
    + apply IH1 with (k := k) (j := j) (u := u); assumption.
    + apply IH2 with (k := k) (j := j) (u := u); assumption.
  - apply lc_abs. apply IH with (k := S k) (j := S j) (u := u).
    + lia.
    + apply lc_at_abs_inv in H. assumption.
  - apply lc_true.
  - apply lc_false.
Qed.

(* ---------------- free variables and substitution ----------- *)

Fixpoint tsubst (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_app t1 t2 => tm_app (tsubst sigma t1) (tsubst sigma t2)
  | tm_abs T t1 => tm_abs T (tsubst sigma t1)
  | tm_true => tm_true
  | tm_false => tm_false
  end.

Definition id_sigma : atom -> tm := fun x => tm_fvar x.

Definition upd_sigma (sigma : atom -> tm) (x : atom) (u : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then u else sigma y.

Fixpoint fv (x : atom) (t : tm) : Prop :=
  match t with
  | tm_bvar i => False
  | tm_fvar y => x = y
  | tm_app t1 t2 => fv x t1 \/ fv x t2
  | tm_abs T t1 => fv x t1
  | tm_true => False
  | tm_false => False
  end.

Fixpoint fv_list (t : tm) : list atom :=
  match t with
  | tm_bvar i => nil
  | tm_fvar y => y :: nil
  | tm_app t1 t2 => fv_list t1 ++ fv_list t2
  | tm_abs T t1 => fv_list t1
  | tm_true => nil
  | tm_false => nil
  end.

Lemma fv_in_fv_list : forall t x, fv x t -> In x (fv_list t).
Proof.
  induction t as [n | y | t1 IH1 t2 IH2 | T t1 IH | | ];
    intros x H; simpl in *.
  - destruct H.
  - destruct H. subst. left. reflexivity.
  - destruct H as [H | H];
      [apply in_or_app; left | apply in_or_app; right]; auto.
  - apply IH. assumption.
  - destruct H.
  - destruct H.
Qed.

Definition fresh (L : list atom) (t : tm) : atom :=
  S (fold_right Nat.add 0 (L ++ fv_list t)).

Lemma In_fold_right_add_le : forall l x,
  In x l -> x <= fold_right Nat.add 0 l.
Proof.
  induction l as [| a l IH]; intros x H; simpl in *.
  - destruct H.
  - destruct H as [H | H]; [subst; lia | specialize (IH x H); lia].
Qed.

Lemma fresh_notin : forall L t, ~ In (fresh L t) L.
Proof.
  intros L t H.
  assert (Hin : In (fresh L t) (L ++ fv_list t)).
  { apply in_or_app. left. exact H. }
  unfold fresh in Hin. apply In_fold_right_add_le in Hin. lia.
Qed.

Lemma fresh_not_fv : forall L t, ~ fv (fresh L t) t.
Proof.
  intros L t H. apply fv_in_fv_list in H.
  assert (Hin : In (fresh L t) (L ++ fv_list t)).
  { apply in_or_app. right. exact H. }
  unfold fresh in Hin. apply In_fold_right_add_le in Hin. lia.
Qed.

Lemma tsubst_ids : forall t, tsubst id_sigma t = t.
Proof.
  induction t as [n | x | t1 IH1 t2 IH2 | T t1 IH | | ]; simpl; f_equal; auto.
Qed.

Lemma tsubst_update_same : forall sigma x u t,
  ~ fv x t -> tsubst (upd_sigma sigma x u) t = tsubst sigma t.
Proof.
  intros sigma x u t.
  induction t as [n | y | t1 IH1 t2 IH2 | T t1 IH | | ];
    simpl; intros H; simpl in H.
  - reflexivity.
  - unfold upd_sigma. destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply H. reflexivity.
    + reflexivity.
  - rewrite (IH1 (fun H1 => H (or_introl H1))).
    rewrite (IH2 (fun H2 => H (or_intror H2))). reflexivity.
  - rewrite (IH H). reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma tsubst_open_rec : forall sigma t k u,
  (forall x, locally_closed (sigma x)) ->
  tsubst sigma (open_rec k u t) =
  open_rec k (tsubst sigma u) (tsubst sigma t).
Proof.
  intros sigma t.
  induction t as [n | x | t1 IH1 t2 IH2 | T t1 IH | | ];
    intros k u Hlc; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. apply open_rec_id.
    assert (H0 : 0 <= k) by lia.
    exact (lc_at_weaken (sigma x) 0 k (Hlc x) H0).
  - rewrite (IH1 k u Hlc), (IH2 k u Hlc). reflexivity.
  - rewrite (IH (S k) u Hlc). reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma tsubst_lc : forall t k sigma,
  lc_at k t ->
  (forall x, locally_closed (sigma x)) ->
  lc_at k (tsubst sigma t).
Proof.
  induction t as [n | x | t1 IH1 t2 IH2 | T t1 IH | | ];
    intros k sigma Ht Hlc; simpl.
  - assumption.
  - assert (H0 : 0 <= k) by lia.
    exact (lc_at_weaken (sigma x) 0 k (Hlc x) H0).
  - apply lc_at_app_inv in Ht as [H1 H2].
    apply lc_app; [apply IH1 | apply IH2]; assumption.
  - apply lc_abs. apply IH with (k := S k).
    + apply lc_at_abs_inv in Ht. assumption.
    + assumption.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma tsubst_update_open : forall sigma x u t,
  ~ fv x t ->
  (forall y, locally_closed (sigma y)) ->
  locally_closed u ->
  tsubst (upd_sigma sigma x u) (open t (tm_fvar x)) =
  open (tsubst sigma t) u.
Proof.
  intros sigma x u t Hfresh Hlc Hu. unfold open.
  rewrite tsubst_open_rec.
  - rewrite (tsubst_update_same sigma x u t Hfresh).
    simpl. unfold upd_sigma. rewrite Nat.eqb_refl. reflexivity.
  - intros y. unfold upd_sigma.
    destruct (Nat.eqb x y) eqn:E; [assumption | apply Hlc].
Qed.

(* ---------------- value / step basic facts ------------------ *)

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v Hv. induction Hv.
  - assumption.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma value_not_app : forall t1 t2, value (tm_app t1 t2) -> False.
Proof. intros t1 t2 H. inversion H. Qed.

Lemma step_abs_false : forall T body s, step (tm_abs T body) s -> False.
Proof. intros T body s H. inversion H. Qed.

Lemma step_true_false : forall s, step tm_true s -> False.
Proof. intros s H. inversion H. Qed.

Lemma step_false_false : forall s, step tm_false s -> False.
Proof. intros s H. inversion H. Qed.

Lemma value_no_step : forall v, value v -> forall v', step v v' -> False.
Proof.
  intros v Hv. induction Hv; intros v' Hs.
  - apply step_abs_false in Hs. assumption.
  - apply step_true_false in Hs. assumption.
  - apply step_false_false in Hs. assumption.
Qed.

Lemma step_app_cases : forall t1 t2 s,
  step (tm_app t1 t2) s ->
  (exists T body, t1 = tm_abs T body /\
                  locally_closed (tm_abs T body) /\
                  value t2 /\ s = open body t2)
  \/ (exists t1', step t1 t1' /\ locally_closed t2 /\
                  s = tm_app t1' t2)
  \/ (exists t2', value t1 /\ step t2 t2' /\
                  s = tm_app t1 t2').
Proof.
  intros t1 t2 s Hs. inversion Hs; subst.
  - left. eexists; eexists; repeat split; eassumption.
  - right; left. eexists; repeat split; eassumption.
  - right; right. eexists; repeat split; eassumption.
Qed.

Lemma step_lc_preserve : forall t t',
  step t t' -> locally_closed t -> locally_closed t'.
Proof.
  intros t t' Hs. induction Hs as
    [T body v Hlcabs Hv | t1 t1' t2 Hstep IH Hlc2 | v1 t2 t2' Hv Hstep IH];
    intros Hlc.
  - unfold locally_closed in *. apply lc_at_app_inv in Hlc as [H1 H2].
    apply lc_open_rec with (k := 0).
    + apply lc_at_abs_inv in Hlcabs. assumption.
    + apply value_lc in Hv. assumption.
  - unfold locally_closed in *. apply lc_at_app_inv in Hlc as [H1 H2].
    apply lc_app.
    + apply IH. assumption.
    + assumption.
  - unfold locally_closed in *. apply lc_at_app_inv in Hlc as [H1 H2].
    apply lc_app.
    + assumption.
    + apply IH. assumption.
Qed.

Lemma SN_ind' : forall P : tm -> Prop,
  (forall t, (forall t', step t t' -> P t') -> P t) ->
  forall t, strongly_normalizing t -> P t.
Proof.
  intros P HP t Hsn. induction Hsn as [t' Hreds IH].
  apply HP. intros t'' Hs. apply IH. assumption.
Qed.

Lemma SN_step : forall t t',
  strongly_normalizing t -> step t t' -> strongly_normalizing t'.
Proof.
  intros t t' Hsn Hs. revert Hs.
  induction Hsn as [t0 Hreds IH]. intros Hs. apply Hreds. assumption.
Qed.

(* ---------------- the logical relation ---------------------- *)

Fixpoint R (T : ty) : tm -> Prop :=
  match T with
  | Ty_Bool => fun t => locally_closed t /\ strongly_normalizing t
  | Ty_Arrow T1 T2 => fun t =>
      locally_closed t /\ strongly_normalizing t /\
      (forall u, R T1 u -> R T2 (tm_app t u))
  end.

Lemma R_lc : forall T t, R T t -> locally_closed t.
Proof. intros T t H. destruct T; simpl in H; tauto. Qed.

Lemma R_sn : forall T t, R T t -> strongly_normalizing t.
Proof. intros T t H. destruct T; simpl in H; tauto. Qed.

Lemma R_app : forall T1 T2 t u,
  R (Ty_Arrow T1 T2) t -> R T1 u -> R T2 (tm_app t u).
Proof.
  intros T1 T2 t u H Hu. simpl in H.
  destruct H as [Hlc [Hsn Happ]]. apply Happ. assumption.
Qed.

Lemma R_step : forall T t t', R T t -> step t t' -> R T t'.
Proof.
  induction T as [| T1 IH1 T2 IH2]; intros t t' HR Hs.
  - simpl in HR |- *. destruct HR as [Hlc Hsn]. split.
    + apply step_lc_preserve with (t := t); assumption.
    + apply SN_step with (t := t); assumption.
  - simpl in HR |- *. destruct HR as [Hlc [Hsn Happ]]. split; [| split].
    + apply step_lc_preserve with (t := t); assumption.
    + apply SN_step with (t := t); assumption.
    + intros u Hu. apply IH2 with (t := tm_app t u).
      * apply Happ. assumption.
      * apply ST_App1.
        -- assumption.
        -- apply R_lc in Hu. assumption.
Qed.

(* Any application whose one-step reducts are all in R is itself in R. *)
Lemma anti_red_app : forall T (t u : tm),
  locally_closed (tm_app t u) ->
  strongly_normalizing (tm_app t u) ->
  (forall s, step (tm_app t u) s -> R T s) ->
  R T (tm_app t u).
Proof.
  induction T as [| T1 IH1 T2 IH2]; intros t u Hlc Hsn Hreds.
  - simpl. split; assumption.
  - simpl. split; [assumption | split; [assumption |]].
    intros v Hv.
    apply IH2 with (t := tm_app t u) (u := v).
    + unfold locally_closed in *. simpl. apply lc_app.
      * assumption.
      * apply R_lc in Hv. assumption.
    + apply SN_intro. intros s Hs.
      destruct (step_app_cases (tm_app t u) v s Hs) as
        [[T' [body [E1 [Hlcabs [Hv' E]]]]] |
         [[s1 [Hs1 [Hlcv E]]] | [s2 [Hv' [Hs2 E]]]]].
      * subst. discriminate E1.
      * subst. apply R_sn with (T := T2). apply R_app with (T1 := T1).
        -- apply Hreds. assumption.
        -- assumption.
      * subst. exfalso. apply value_not_app in Hv'. assumption.
    + intros s Hs.
      destruct (step_app_cases (tm_app t u) v s Hs) as
        [[T' [body [E1 [Hlcabs [Hv' E]]]]] |
         [[s1 [Hs1 [Hlcv E]]] | [s2 [Hv' [Hs2 E]]]]].
      * subst. discriminate E1.
      * subst. apply R_app with (T1 := T1).
        -- apply Hreds. assumption.
        -- assumption.
      * subst. exfalso. apply value_not_app in Hv'. assumption.
Qed.

(* A well-typed abstraction applied to a related argument is related. *)
Lemma SN_app_abs_gen : forall T1 T2 body,
  lc_at 1 body ->
  (forall u', R T1 u' -> R T2 (open body u')) ->
  forall u, strongly_normalizing u -> R T1 u ->
  R T2 (tm_app (tm_abs T1 body) u).
Proof.
  intros T1 T2 body Hlc Hbody.
  refine (SN_ind' (fun u => R T1 u ->
                          R T2 (tm_app (tm_abs T1 body) u)) _).
  intros u IH HR.
  apply anti_red_app.
  - unfold locally_closed. simpl. apply lc_app.
    + apply lc_abs. assumption.
    + apply R_lc in HR. assumption.
  - apply SN_intro. intros s Hs.
    destruct (step_app_cases (tm_abs T1 body) u s Hs) as
      [[T' [body' [E1 [Hlcabs [Hv E]]]]] |
       [[s1 [Hs1 [Hlcu E]]] | [s2 [Hv [Hs2 E]]]]].
    + subst. inversion E1; subst. apply R_sn with (T := T2).
      apply Hbody. assumption.
    + subst. exfalso. apply step_abs_false in Hs1. assumption.
    + subst. apply R_sn with (T := T2). apply IH.
      * assumption.
      * apply R_step with (t := u); assumption.
  - intros s Hs.
    destruct (step_app_cases (tm_abs T1 body) u s Hs) as
      [[T' [body' [E1 [Hlcabs [Hv E]]]]] |
       [[s1 [Hs1 [Hlcu E]]] | [s2 [Hv [Hs2 E]]]]].
    + subst. inversion E1; subst. apply Hbody, HR.
    + subst. exfalso. apply step_abs_false in Hs1. assumption.
    + subst. apply IH.
      * assumption.
      * apply R_step with (t := u); assumption.
Qed.

(* ---------------- the semantic context --------------------- *)

Definition ctx_sat (Gamma : context) (sigma : atom -> tm) : Prop :=
  (forall x, locally_closed (sigma x)) /\
  (forall x T, Gamma x = Some T -> R T (sigma x)).

Lemma upd_sigma_sat : forall Gamma sigma x T1 u,
  ctx_sat Gamma sigma ->
  R T1 u ->
  ctx_sat (update Gamma x T1) (upd_sigma sigma x u).
Proof.
  intros Gamma sigma x T1 u [Hlc Hall] HR. split.
  - intros y. unfold upd_sigma. destruct (Nat.eqb x y) eqn:E.
    + apply R_lc in HR. assumption.
    + apply Hlc.
  - intros y T Hty. unfold upd_sigma.
    destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst y.
      unfold update in Hty. rewrite Nat.eqb_refl in Hty.
      inversion Hty; subst. apply HR.
    + apply Hall. unfold update in Hty. rewrite E in Hty. assumption.
Qed.

Lemma ctx_sat_empty : forall sigma,
  (forall x, locally_closed (sigma x)) -> ctx_sat empty sigma.
Proof.
  intros sigma Hlc. split; [assumption |].
  intros x T Hx. unfold empty in Hx. simpl in Hx. discriminate.
Qed.

(* ---------------- fundamental theorem ----------------------- *)

Lemma fundamental_aux : forall Gamma t T,
  has_type Gamma t T ->
  locally_closed t /\
  (forall sigma, ctx_sat Gamma sigma -> R T (tsubst sigma t)).
Proof.
  intros Gamma t T Hty.
  induction Hty as
    [Gamma x T Hlookup
    | L Gamma T1 T2 t1 Hbody IHbody
    | Gamma t1 t2 T1 T2 Ht1 IH1 Ht2 IH2
    | Gamma
    | Gamma].
  - (* T_Var *) simpl. split.
    + apply lc_fvar.
    + intros sigma Hsat. apply (proj2 Hsat). assumption.
  - (* T_Abs *)
    assert (HxL : ~ In (fresh L t1) L) by apply fresh_notin.
    assert (Hxfv : ~ fv (fresh L t1) t1) by apply fresh_not_fv.
    pose proof (IHbody (fresh L t1) HxL) as HIH.
    destruct HIH as [Hlcx Hsem].
    assert (Hlc1 : lc_at 1 t1).
    { apply (lc_open_inv t1 0 0 (tm_fvar (fresh L t1))); [lia | exact Hlcx]. }
    split.
    + (* lc (abs T1 t1) *) apply lc_abs. assumption.
    + intros sigma Hsat. destruct Hsat as [HlcS HallS].
      assert (Hlcsub : lc_at 1 (tsubst sigma t1)).
      { apply (tsubst_lc t1 1 sigma Hlc1 HlcS). }
      simpl. split.
      * apply lc_abs. assumption.
      * split.
        -- apply SN_intro. intros s Hs.
           exfalso. apply step_abs_false in Hs. assumption.
        -- intros u Hu.
           apply (SN_app_abs_gen T1 T2 (tsubst sigma t1) Hlcsub).
           ++ intros u' Hu'.
              pose proof (Hsem (upd_sigma sigma (fresh L t1) u')
                               (upd_sigma_sat Gamma sigma (fresh L t1) T1 u'
                                              (conj HlcS HallS) Hu')) as HR.
              rewrite (tsubst_update_open sigma (fresh L t1) u' t1 Hxfv
                                           HlcS (R_lc T1 u' Hu')) in HR.
              exact HR.
           ++ apply R_sn in Hu. assumption.
           ++ assumption.
  - (* T_App *) simpl. split.
    + apply lc_app; [apply (proj1 IH1) | apply (proj1 IH2)].
    + intros sigma Hsat. simpl.
      apply R_app with (T1 := T1).
      * apply (proj2 IH1). assumption.
      * apply (proj2 IH2). assumption.
  - (* T_True *) simpl. split.
    + apply lc_true.
    + intros sigma Hsat. simpl. split.
      * apply lc_true.
      * apply SN_intro. intros s Hs.
        exfalso. apply step_true_false in Hs. assumption.
  - (* T_False *) simpl. split.
    + apply lc_false.
    + intros sigma Hsat. simpl. split.
      * apply lc_false.
      * apply SN_intro. intros s Hs.
        exfalso. apply step_false_false in Hs. assumption.
Qed.

Lemma fundamental : forall Gamma t T,
  has_type Gamma t T ->
  forall sigma, ctx_sat Gamma sigma -> R T (tsubst sigma t).
Proof.
  intros Gamma t T Hty. apply (proj2 (fundamental_aux Gamma t T Hty)).
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  pose proof (fundamental empty t T Hty id_sigma
                (ctx_sat_empty id_sigma (fun x => lc_fvar 0 x))) as HR.
  rewrite tsubst_ids in HR.
  apply R_sn in HR. exact HR.
Qed.

End STLCNormalizationNoneHardTask.
