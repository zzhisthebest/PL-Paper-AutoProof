(** STLC call-by-value strong-normalization benchmark, Medium variant.
    System T-style natural-number recursion; no if-then-else or choice. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Relations.Relation_Definitions Lia Program.Equality.
Import ListNotations.

Module STLCNormalizationRecursionMediumTask.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
      R x y ->
      multi R y z ->
      multi R x z.

Definition atom := nat.

Inductive ty : Type :=
  | Ty_Bool : ty
  | Ty_Nat : ty
  | Ty_Arrow : ty -> ty -> ty.

Inductive tm : Type :=
  | tm_bvar : nat -> tm
  | tm_fvar : atom -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : ty -> tm -> tm
  | tm_true : tm
  | tm_false : tm
  | tm_zero : tm
  | tm_succ : tm -> tm

  | tm_natrec : tm -> tm -> tm -> tm.

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
Notation "'zero'" := tm_zero
  (in custom stlc_tm at level 0) : stlc_scope.
Notation "'succ' t" := (tm_succ t)
  (in custom stlc_tm at level 9, t custom stlc_tm at level 0) : stlc_scope.
Notation "'rec' n b s" := (tm_natrec n b s)
  (in custom stlc_tm at level 9,
   n custom stlc_tm at level 0, b custom stlc_tm at level 0,
   s custom stlc_tm at level 0) : stlc_scope.
Notation "'Nat'" := Ty_Nat
  (in custom stlc_ty at level 0) : stlc_scope.

Fixpoint open_rec (k : nat) (u : tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => if Nat.eqb k i then u else tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_app t1 t2 => tm_app (open_rec k u t1) (open_rec k u t2)
  | tm_abs T t1 => tm_abs T (open_rec (S k) u t1)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (open_rec k u t1)
  | tm_natrec n b s =>
      tm_natrec (open_rec k u n) (open_rec k u b) (open_rec k u s)
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
  | lc_zero : forall k, lc_at k tm_zero
  | lc_succ : forall k t, lc_at k t -> lc_at k (tm_succ t)
  | lc_rec : forall k n b s,
      lc_at k n -> lc_at k b -> lc_at k s ->
      lc_at k (tm_natrec n b s).

Definition locally_closed (t : tm) : Prop := lc_at 0 t.

Hint Constructors lc_at : core.

Inductive numeric_value : tm -> Prop :=
  | nv_zero : numeric_value tm_zero
  | nv_succ : forall (t : tm), numeric_value t -> numeric_value (tm_succ t).


Inductive value : tm -> Prop :=
  | v_abs : forall T t,
      locally_closed (tm_abs T t) ->
      value (tm_abs T t)
  | v_true :
      value tm_true
  | v_false :
      value tm_false
  | v_nat : forall n, numeric_value n -> value n.

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
  | ST_Succ : forall t t',
      t --> t' -> tm_succ t --> tm_succ t'
  | ST_RecArg : forall n n' b s,

      n --> n' -> locally_closed b -> locally_closed s ->
      tm_natrec n b s --> tm_natrec n' b s
  | ST_RecBase : forall n b b' s,

      numeric_value n -> b --> b' -> locally_closed s ->
      tm_natrec n b s --> tm_natrec n b' s
  | ST_RecStep : forall n b s s',

      numeric_value n -> value b -> s --> s' ->
      tm_natrec n b s --> tm_natrec n b s'
  | ST_RecZero : forall b s,

      value b -> value s -> tm_natrec tm_zero b s --> b
  | ST_RecSucc : forall n b s,

      numeric_value n -> value b -> value s ->
      tm_natrec (tm_succ n) b s -->
        tm_app (tm_app s n) (tm_natrec n b s)
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
  | T_Zero : forall Gamma,
      <{ Gamma |-- zero \in Nat }>
  | T_Succ : forall Gamma n,
      <{ Gamma |-- $(n) \in Nat }> ->
      <{ Gamma |-- succ $(n) \in Nat }>
  | T_Rec : forall Gamma n b s T,
      <{ Gamma |-- $(n) \in Nat }> ->
      <{ Gamma |-- $(b) \in T }> ->
      <{ Gamma |-- $(s) \in Nat -> T -> T }> ->
      <{ Gamma |-- rec $(n) $(b) $(s) \in T }>
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
  | tm_zero => tm_zero
  | tm_succ t => tm_succ (msubst rho t)
  | tm_natrec n b s => tm_natrec (msubst rho n) (msubst rho b) (msubst rho s)
  end.

Definition proper_substitution (rho : term_substitution) : Prop :=
  forall x, locally_closed (rho x).

Fixpoint value_relation (T : ty) (v : tm) : Prop :=
  value v /\
  match T with
  | Ty_Nat => numeric_value v
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

Definition related_substitution
    (Gamma : context) (rho : term_substitution) : Prop :=
  forall x T, Gamma x = Some T -> value_relation T (rho x).

(* Some elementary facts about the syntax and the reduction relation. *)

Fixpoint fvars (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_app t1 t2 => fvars t1 ++ fvars t2
  | tm_abs _ t1 => fvars t1
  | tm_true | tm_false | tm_zero => []
  | tm_succ t1 => fvars t1
  | tm_natrec n b s => fvars n ++ fvars b ++ fvars s
  end.

Fixpoint list_max (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: l' => Nat.max x (list_max l')
  end.

Lemma in_list_max : forall x l, In x l -> x <= list_max l.
Proof.
  intros x l; induction l as [|a l IH]; simpl.
  - contradiction.
  - intros H; destruct H as [->|H].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; exact H|apply Nat.le_max_r].
Qed.

Lemma fresh_not_in : forall l, ~ In (S (list_max l)) l.
Proof.
  intros l H.
  pose proof (in_list_max _ _ H).
  lia.
Qed.

Lemma notin_fvars_app_l : forall x t u,
    ~ In x (fvars (tm_app t u)) -> ~ In x (fvars t).
Proof. intros x t u Hnot Hin; apply Hnot; simpl; apply in_or_app; left; exact Hin. Qed.

Lemma notin_fvars_app_r : forall x t u,
    ~ In x (fvars (tm_app t u)) -> ~ In x (fvars u).
Proof. intros x t u Hnot Hin; apply Hnot; simpl; apply in_or_app; right; exact Hin. Qed.

Lemma notin_fvars_rec_l : forall x n b s,
    ~ In x (fvars (tm_natrec n b s)) -> ~ In x (fvars n).
Proof. intros x n b s Hnot Hin; apply Hnot; simpl; apply in_or_app; left; exact Hin. Qed.

Lemma notin_fvars_rec_b : forall x n b s,
    ~ In x (fvars (tm_natrec n b s)) -> ~ In x (fvars b).
Proof. intros x n b s Hnot Hin; apply Hnot; simpl; apply in_or_app; right; apply in_or_app; left; exact Hin. Qed.

Lemma notin_fvars_rec_s : forall x n b s,
    ~ In x (fvars (tm_natrec n b s)) -> ~ In x (fvars s).
Proof. intros x n b s Hnot Hin; apply Hnot; simpl; apply in_or_app; right; apply in_or_app; right; exact Hin. Qed.

Lemma lc_at_mono : forall k t, lc_at k t -> lc_at (S k) t.
Proof.
  intros k t H; induction H; eauto.
Qed.

Lemma lc_at_from_zero : forall k t, lc_at 0 t -> lc_at k t.
Proof.
  intros k t H; induction k; auto.
  apply lc_at_mono; auto.
Qed.

Lemma lc_msubst : forall k t rho,
    proper_substitution rho -> lc_at k t -> lc_at k (msubst rho t).
Proof.
  intros k t rho Hr Hlc; induction Hlc; simpl; eauto.
  apply lc_at_from_zero; apply Hr.
Qed.

Lemma open_rec_lc : forall k t u, lc_at k t -> open_rec k u t = t.
Proof.
  intros k t u H; induction H; simpl; try reflexivity.
  - destruct (Nat.eqb k i) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
Qed.

Lemma lc_open_rec_inv : forall k t x,
    ~ In x (fvars t) ->
    lc_at k (open_rec k (tm_fvar x) t) ->
    lc_at (S k) t.
Proof.
  intros k t x; revert k x;
  induction t as [i|y|t1 IH1 t2 IH2|T t1 IH| | | |t1 IH|n IHn b IHb s IHs];
    intros k x Hfresh Hlc; simpl in *.
  - destruct (Nat.eqb k i) eqn:E.
    + apply lc_bvar; apply Nat.eqb_eq in E; lia.
    + inversion Hlc; apply lc_bvar; apply Nat.eqb_neq in E; lia.
  - apply lc_fvar.
  - apply lc_app.
    + apply IH1 with (k:=k) (x:=x).
      * apply notin_fvars_app_l with (t:=t1) (u:=t2); exact Hfresh.
      * inversion Hlc; assumption.
    + apply IH2 with (k:=k) (x:=x).
      * apply notin_fvars_app_r with (t:=t1) (u:=t2); exact Hfresh.
      * inversion Hlc; assumption.
  - apply lc_abs. apply IH with (k:=S k) (x:=x).
    + exact Hfresh.
    + inversion Hlc; assumption.
  - apply lc_true.
  - apply lc_false.
  - apply lc_zero.
  - apply lc_succ. apply IH with (k:=k) (x:=x).
    + exact Hfresh.
    + inversion Hlc; assumption.
  - apply lc_rec.
    + apply IHn with (k:=k) (x:=x).
      * apply notin_fvars_rec_l with (n:=n) (b:=b) (s:=s); exact Hfresh.
      * inversion Hlc; assumption.
    + apply IHb with (k:=k) (x:=x).
      * apply notin_fvars_rec_b with (n:=n) (b:=b) (s:=s); exact Hfresh.
      * inversion Hlc; assumption.
    + apply IHs with (k:=k) (x:=x).
      * apply notin_fvars_rec_s with (n:=n) (b:=b) (s:=s); exact Hfresh.
      * inversion Hlc; assumption.
Qed.

Lemma msubst_open_rec : forall k t rho x u,
    proper_substitution rho ->
    ~ In x (fvars t) ->
    msubst (subst_update rho x u) (open_rec k (tm_fvar x) t) =
      open_rec k u (msubst rho t).
Proof.
  intros k t rho x u; revert k rho x u;
  induction t as [i|y|t1 IH1 t2 IH2|T t1 IH| | | |t1 IH|n IHn b IHb s IHs];
    intros k rho x u Hr Hfresh; simpl in *.
  - destruct (Nat.eqb k i) eqn:E.
    + unfold msubst, subst_update; rewrite Nat.eqb_refl; reflexivity.
    + reflexivity.
  - destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E; exfalso; apply Hfresh; simpl; subst; auto.
    + unfold msubst, subst_update; rewrite E; rewrite open_rec_lc;
        [reflexivity|apply lc_at_from_zero; apply Hr].
  - rewrite (IH1 k rho x u Hr
               (notin_fvars_app_l x t1 t2 Hfresh)),
      (IH2 k rho x u Hr
               (notin_fvars_app_r x t1 t2 Hfresh)); reflexivity.
  - f_equal. apply IH with (k:=S k) (rho:=rho) (x:=x) (u:=u); assumption.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - f_equal. apply IH with (k:=k) (rho:=rho) (x:=x) (u:=u); assumption.
  - rewrite (IHn k rho x u Hr
               (notin_fvars_rec_l x n b s Hfresh)),
      (IHb k rho x u Hr
               (notin_fvars_rec_b x n b s Hfresh)),
      (IHs k rho x u Hr
               (notin_fvars_rec_s x n b s Hfresh)); reflexivity.
Qed.

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v Hv; destruct Hv as [T t H| | |n Hn].
  - exact H.
  - apply lc_true.
  - apply lc_false.
  - unfold locally_closed; induction Hn.
    + apply lc_zero.
    + apply lc_succ; exact IHHn.
Qed.

Lemma value_relation_lc : forall T v, value_relation T v -> locally_closed v.
Proof.
  intros T v H; destruct T as [| |T1 T2]; simpl in H;
    destruct H as [Hv _]; apply value_lc; exact Hv.
Qed.

Lemma value_relation_value : forall T v, value_relation T v -> value v.
Proof.
  intros T v H; destruct T as [| |T1 T2]; simpl in H;
    destruct H as [Hv _]; exact Hv.
Qed.

Lemma lc_open_rec : forall k t u,
    lc_at (S k) t -> lc_at k u -> lc_at k (open_rec k u t).
Proof.
  intros k t u; revert k u;
  induction t as [i|x|t1 IH1 t2 IH2|T t1 IH| | | |t1 IH|n IHn b IHb s IHs];
    intros k u Ht Hu; simpl in *.
  - inversion Ht; subst.
    destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E; subst; exact Hu.
    + apply lc_bvar; apply Nat.eqb_neq in E; lia.
  - apply lc_fvar.
  - inversion Ht; subst; apply lc_app.
    + apply IH1; assumption.
    + apply IH2; assumption.
  - inversion Ht; subst; apply lc_abs. apply IH with (k:=S k).
    + assumption.
    + apply lc_at_mono; assumption.
  - apply lc_true.
  - apply lc_false.
  - apply lc_zero.
  - inversion Ht; subst; apply lc_succ. apply IH; assumption.
  - inversion Ht; subst; apply lc_rec.
    + apply IHn; assumption.
    + apply IHb; assumption.
    + apply IHs; assumption.
Qed.

Lemma numeric_lc : forall n, numeric_value n -> locally_closed n.
Proof. intros n H; induction H; unfold locally_closed; eauto. Qed.

Lemma step_lc : forall t t', locally_closed t -> t --> t' -> locally_closed t'.
Proof.
  intros t t' Hlc Hs; revert Hlc; induction Hs; intros Hlc; simpl in *; eauto using lc_open_rec, numeric_lc, value_lc.
  - unfold locally_closed in *; inversion H; apply lc_open_rec.
    + assumption.
    + apply value_lc; exact H0.
  - unfold locally_closed in *; inversion Hlc; eauto using lc_open_rec, numeric_lc, value_lc.
  - unfold locally_closed in *; inversion Hlc; eauto using lc_open_rec, numeric_lc, value_lc.
  - unfold locally_closed in *; inversion Hlc; eauto using lc_open_rec, numeric_lc, value_lc.
  - unfold locally_closed in *; inversion Hlc; eauto using lc_open_rec, numeric_lc, value_lc.
  - unfold locally_closed in *; inversion Hlc; eauto using lc_open_rec, numeric_lc, value_lc.
  - unfold locally_closed in *; inversion Hlc; eauto using lc_open_rec, numeric_lc, value_lc.
  - unfold locally_closed in *; inversion Hlc.
    apply lc_app.
    + apply lc_app; [apply value_lc; exact H1|].
      apply numeric_lc; exact H.
    + apply lc_rec; [apply numeric_lc; exact H|exact H7|exact H8].
Qed.

Lemma numeric_no_step : forall n n', numeric_value n -> ~ step n n'.
Proof.
  intros n n' H; revert n'; induction H; intros n'.
  - intros Hs; inversion Hs.
  - intros Hs; inversion Hs; subst; exact (IHnumeric_value t' H1).
Qed.

Lemma value_no_step : forall v v', value v -> ~ step v v'.
Proof.
  intros v v' Hv; destruct Hv as [T t Hlc| | |n Hn].
  - intros Hs; inversion Hs.
  - intros Hs; inversion Hs.
  - intros Hs; inversion Hs.
  - intros Hs; exact (numeric_no_step n v' Hn Hs).
Qed.

Lemma abs_no_step : forall T t t', locally_closed (tm_abs T t) ->
    ~ step (tm_abs T t) t'.
Proof. intros; intro Hs; inversion Hs. Qed.

Lemma step_deterministic : forall t u v, step t u -> step t v -> u = v.
Proof.
  induction t as [i|x|t1 IH1 t2 IH2|T t1 IH| | | |t1 IH|n IHn b IHb s IHs];
    intros u v H1 H2; dependent destruction H1; dependent destruction H2;
    repeat subst; try reflexivity; try congruence; eauto.
  all: try solve [exfalso; inversion H2].
  all: try solve [exfalso; inversion H1].
  all: try solve [exfalso; inversion H0].
  all: try solve [exfalso; firstorder using value_no_step, numeric_no_step, abs_no_step].
  all: try solve [f_equal; eauto].
  - multimatch goal with
    | Hn : numeric_value n0, Hs : step (tm_succ n0) n' |- _ =>
        exfalso; exact (numeric_no_step (tm_succ n0) n'
                         (nv_succ n0 Hn) Hs)
    end.
  - multimatch goal with
    | Hn : numeric_value n0, Hs : step (tm_succ n0) n' |- _ =>
        exfalso; exact (numeric_no_step (tm_succ n0) n'
                         (nv_succ n0 Hn) Hs)
    end.
Qed.

Lemma multi_trans : forall t u v, t -->* u -> u -->* v -> t -->* v.
Proof.
  intros t u v H; induction H; eauto using multi_refl, multi_step.
Qed.

Lemma multi_app1 : forall t t' a,
    t -->* t' -> locally_closed a ->
    tm_app t a -->* tm_app t' a.
Proof.
  intros t t' a H; induction H; intros; eauto using multi_refl, multi_step.
Qed.

Lemma multi_app2 : forall v a a',
    value v -> a -->* a' ->
    tm_app v a -->* tm_app v a'.
Proof.
  intros v a a' Hv H; induction H; intros; eauto using multi_refl, multi_step.
Qed.

Lemma multi_succ : forall t t', t -->* t' -> tm_succ t -->* tm_succ t'.
Proof. intros; induction H; eauto using multi_refl, multi_step. Qed.

Lemma multi_rec_arg : forall n n' b s,
    n -->* n' -> locally_closed b -> locally_closed s ->
    tm_natrec n b s -->* tm_natrec n' b s.
Proof. intros; induction H; eauto using multi_refl, multi_step. Qed.

Lemma multi_rec_base : forall n b b' s,
    numeric_value n -> b -->* b' -> locally_closed s ->
    tm_natrec n b s -->* tm_natrec n b' s.
Proof. intros n b b' s Hn H; induction H; eauto using multi_refl, multi_step. Qed.

Lemma multi_rec_step : forall n b s s',
    numeric_value n -> value b -> s -->* s' ->
    tm_natrec n b s -->* tm_natrec n b s'.
Proof. intros n b s s' Hn Hb H; induction H; eauto using multi_refl, multi_step. Qed.

Lemma multi_to_sn : forall t v, t -->* v -> value v -> strongly_normalizing t.
Proof.
  intros t v H; induction H as [t|t u v Htu Huv IH]; intros Hv.
  - constructor. intros t' Hstep. exfalso; exact (value_no_step t t' Hv Hstep).
  - constructor. intros t' Hstep.
    assert (Heq : t' = u) by (eapply step_deterministic; eauto).
    subst; eauto.
Qed.

Lemma expr_backstep : forall T t t',
    locally_closed t -> t --> t' -> expression_relation T t' ->
    expression_relation T t.
Proof.
  intros T t t' Hlc Hstep [Hlc' [v [Hm Hvr]]].
  repeat split; eauto.
  exists v; split; eauto using multi_step, multi_refl.
Qed.

Lemma expr_step : forall T t t',
    expression_relation T t -> t --> t' -> expression_relation T t'.
Proof.
  intros T t t' [Hlc [v [Hm Hvr]]] Hstep.
  assert (Htail : t' -->* v).
  { induction Hm as [t|t u v Htu Huv IH].
    - exfalso; exact (value_no_step t t' (value_relation_value _ _ Hvr) Hstep).
    - assert (Heq : t' = u) by (eapply step_deterministic; eauto).
      subst; exact Huv. }
  repeat split; eauto using multi_refl, step_lc.
Qed.

Lemma expression_sn : forall T t, expression_relation T t -> strongly_normalizing t.
Proof.
  intros T t [Hlc [v [Hm Hvr]]].
  apply multi_to_sn with (v:=v); [exact Hm|apply value_relation_value with (T:=T); exact Hvr].
Qed.

Lemma expr_of_value_relation : forall T v,
    value_relation T v -> expression_relation T v.
Proof.
  intros T v H; split; [apply value_relation_lc with (T:=T); exact H|].
  exists v; split; [apply multi_refl|exact H].
Qed.

Lemma expr_app : forall T1 T2 f a,
    expression_relation (<{{ T1 -> T2 }}>) f ->
    expression_relation T1 a ->
    expression_relation T2 (tm_app f a).
Proof.
  intros T1 T2 f a [Hlf [vf [Hmf Hvf]]] [Hla [va [Hma Hva]]].
  destruct Hvf as [Hvf [body [Heq Hbody]]]; subst vf.
  specialize (Hbody va Hva); destruct Hbody as [Hopen [v [Hmopen Hvr]]].
  split.
  - constructor; assumption.
  - exists v; split.
    + assert (Ha1 : tm_app f a -->* tm_app (tm_abs T1 body) a).
      { apply multi_app1; [exact Hmf|exact Hla]. }
      assert (Ha2 : tm_app (tm_abs T1 body) a -->*
                       tm_app (tm_abs T1 body) va).
      { apply multi_app2; [exact Hvf|exact Hma]. }
      assert (Ha3 : tm_app (tm_abs T1 body) va -->* open body va).
      { apply multi_step with (y:=open body va); [apply ST_AppAbs; [apply value_lc; exact Hvf|apply value_relation_value with (T:=T1); exact Hva]|apply multi_refl]. }
      eapply multi_trans; [exact Ha1|].
      eapply multi_trans; [exact Ha2|].
      eapply multi_trans; [exact Ha3|exact Hmopen].
    + exact Hvr.
Qed.

Lemma natrec_value_expr : forall T b s n,
    value_relation T b ->
    value_relation (<{{ Nat -> T -> T }}>) s ->
    numeric_value n ->
    expression_relation T (tm_natrec n b s).
Proof.
  intros T b s n Hb Hs Hn; induction Hn as [|n Hn IH].
  - apply expr_backstep with (t':=b).
    + constructor; [apply lc_zero|apply value_relation_lc with (T:=T); exact Hb|apply value_relation_lc with (T:=Ty_Arrow Ty_Nat (Ty_Arrow T T)); exact Hs].
    + apply ST_RecZero; [apply value_relation_value with (T:=T); exact Hb|apply value_relation_value with (T:=Ty_Arrow Ty_Nat (Ty_Arrow T T)); exact Hs].
    + apply expr_of_value_relation; exact Hb.
  - assert (Hnrel : value_relation Ty_Nat n).
    { split; [constructor; exact Hn|exact Hn]. }
    assert (Hnerel : expression_relation Ty_Nat n) by (apply expr_of_value_relation; exact Hnrel).
    assert (Hrec : expression_relation T (tm_natrec n b s)) by exact IH.
    assert (Hleft : expression_relation (<{{ T -> T }}>) (tm_app s n)).
    { apply expr_app with (T1:=Ty_Nat) (T2:=Ty_Arrow T T);
      [apply expr_of_value_relation; exact Hs|exact Hnerel]. }
    assert (Hright : expression_relation T
              (tm_app (tm_app s n) (tm_natrec n b s))).
    { apply expr_app with (T1:=T) (T2:=T); [exact Hleft|exact Hrec]. }
    apply expr_backstep with
      (t':=tm_app (tm_app s n) (tm_natrec n b s)).
    + constructor.
      * apply lc_succ; apply numeric_lc; exact Hn.
      * apply value_relation_lc with (T:=T); exact Hb.
      * apply value_relation_lc with (T:=Ty_Arrow Ty_Nat (Ty_Arrow T T)); exact Hs.
    + apply ST_RecSucc.
      * exact Hn.
      * apply value_relation_value with (T:=T); exact Hb.
      * apply value_relation_value with (T:=Ty_Arrow Ty_Nat (Ty_Arrow T T)); exact Hs.
    + exact Hright.
Qed.

Lemma expr_natrec : forall T n b s,
    expression_relation Ty_Nat n ->
    expression_relation T b ->
    expression_relation (<{{ Nat -> T -> T }}>) s ->
    expression_relation T (tm_natrec n b s).
Proof.
  intros T n b s [Hln [nv [Hn Hnv]]] [Hlb [bv [Hb Hbv]]]
    [Hls [sv [Hs Hsv]]].
  assert (Hnnum : numeric_value nv).
  { simpl in Hnv; exact (proj2 Hnv). }
  assert (Hbval : value bv) by (apply value_relation_value with (T:=T); exact Hbv).
  assert (Hsval : value sv) by (apply value_relation_value with (T:=Ty_Arrow Ty_Nat (Ty_Arrow T T)); exact Hsv).
  assert (Hq : expression_relation T (tm_natrec nv bv sv)).
  { apply natrec_value_expr; [exact Hbv|exact Hsv|exact Hnnum]. }
  destruct Hq as [Hlq [v [Hq Hvr]]].
  split; [exact (lc_rec 0 n b s Hln Hlb Hls)|].
  exists v; split.
  - assert (Ha : tm_natrec n b s -->* tm_natrec nv b s).
    { apply multi_rec_arg; assumption. }
    assert (Hb' : tm_natrec nv b s -->* tm_natrec nv bv s).
    { apply multi_rec_base; assumption. }
    assert (Hs' : tm_natrec nv bv s -->* tm_natrec nv bv sv).
    { apply multi_rec_step; assumption. }
    eapply multi_trans; [exact Ha|].
    eapply multi_trans; [exact Hb'|].
    eapply multi_trans; [exact Hs'|exact Hq].
  - exact Hvr.
Qed.

Fixpoint canonical (T : ty) : tm :=
  match T with
  | Ty_Bool => tm_true
  | Ty_Nat => tm_zero
  | Ty_Arrow T1 T2 => tm_abs T1 (canonical T2)
  end.

Lemma canonical_lc : forall k T, lc_at k (canonical T).
Proof.
  intros k T; induction T; simpl; eauto.
  apply lc_abs; apply lc_at_mono; exact IHT2.
Qed.

Lemma open_canonical : forall T u, open (canonical T) u = canonical T.
Proof.
  intros T; induction T; simpl; intros; try reflexivity.
  unfold open; simpl; f_equal; apply open_rec_lc with (k:=1); apply canonical_lc.
Qed.

Lemma canonical_related : forall T, value_relation T (canonical T).
Proof.
  intros T; induction T as [| |T1 IH1 T2 IH2]; simpl.
  - split; [apply v_true|left; reflexivity].
  - split; [apply v_nat; apply nv_zero|apply nv_zero].
  - split.
    + apply v_abs; apply lc_abs; apply canonical_lc.
    + exists (canonical T2); split; [reflexivity|].
      intros arg Harg; split.
      * rewrite open_canonical; apply value_relation_lc with (T:=T2); apply IH2.
      * exists (canonical T2); split; [rewrite open_canonical; apply multi_refl|apply IH2].
Qed.

Lemma proper_subst_update : forall rho x v,
    proper_substitution rho -> locally_closed v ->
    proper_substitution (subst_update rho x v).
Proof.
  intros rho x v Hr Hv y; unfold subst_update.
  destruct (Nat.eqb x y); [exact Hv|exact (Hr y)].
Qed.

Lemma related_subst_update : forall Gamma rho x T v,
    related_substitution Gamma rho -> value_relation T v ->
    related_substitution (update Gamma x T) (subst_update rho x v).
Proof.
  intros Gamma rho x T v Hr Hv y S Hy.
  unfold update, subst_update in *.
  destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E; subst y; simpl in Hy; inversion Hy; subst S; exact Hv.
  - apply Hr with (x:=y) (T:=S); exact Hy.
Qed.

Fixpoint tm_size (t : tm) : nat :=
  match t with
  | tm_bvar _ | tm_fvar _ | tm_true | tm_false | tm_zero => 1
  | tm_app t1 t2 => S (tm_size t1 + tm_size t2)
  | tm_abs _ t1 | tm_succ t1 => S (tm_size t1)
  | tm_natrec n b s => S (tm_size n + tm_size b + tm_size s)
  end.

Lemma tm_size_open_fvar : forall k x t, tm_size (open_rec k (tm_fvar x) t) = tm_size t.
Proof.
  intros k x t; revert k x;
  induction t as [i|y|t1 IH1 t2 IH2|T t1 IH| | | |t1 IH|n IHn b IHb s IHs];
    intros k x; simpl; try reflexivity.
  - destruct (Nat.eqb k i); simpl; reflexivity.
  - rewrite IH1, IH2; reflexivity.
  - rewrite IH; reflexivity.
  - rewrite IH; reflexivity.
  - rewrite IHn, IHb, IHs; reflexivity.
Qed.

Lemma fundamental_aux : forall n Gamma t T,
    tm_size t = n -> <{ Gamma |-- t \in T }> ->
    forall rho, proper_substitution rho -> related_substitution Gamma rho ->
      expression_relation T (msubst rho t).
Proof.
  intro n0.
  refine (well_founded_induction Nat.lt_wf_0
    (fun n => forall Gamma t T, tm_size t = n ->
      <{ Gamma |-- t \in T }> ->
      forall rho, proper_substitution rho -> related_substitution Gamma rho ->
        expression_relation T (msubst rho t)) _ n0).
  intros n IH Gamma t T Hsize HT rho Hproper Hrelated.
  destruct HT.
  - simpl. split; [apply Hproper; eapply Hrelated; exact H|].
    exists (rho x); split; [apply multi_refl|eapply Hrelated; exact H].
  - simpl. set (x := S (list_max (L ++ fvars t1))).
    assert (HxL : ~ In x L).
    { intro Hin; apply (fresh_not_in (L ++ fvars t1)); apply in_or_app; left; exact Hin. }
    assert (HxF : ~ In x (fvars t1)).
    { intro Hin; apply (fresh_not_in (L ++ fvars t1)); apply in_or_app; right; exact Hin. }
    assert (Hsmall : tm_size (open t1 (tm_fvar x)) < n).
    { unfold open; rewrite tm_size_open_fvar; simpl in Hsize; lia. }
    assert (Hcan : expression_relation T2
      (msubst (subst_update rho x (canonical T1)) (open t1 (tm_fvar x)))).
    { apply (IH (tm_size (open t1 (tm_fvar x))) Hsmall
          (update Gamma x T1) (open t1 (tm_fvar x)) T2 eq_refl (H x HxL)).
      - apply proper_subst_update; [exact Hproper|apply value_relation_lc with (T:=T1); apply canonical_related].
      - apply related_subst_update; [exact Hrelated|apply canonical_related]. }
    change (expression_relation T2
      (msubst (subst_update rho x (canonical T1))
        (open_rec 0 (tm_fvar x) t1))) in Hcan.
    rewrite (msubst_open_rec 0 t1 rho x (canonical T1) Hproper HxF) in Hcan.
    assert (Hbodylc : lc_at 1 (msubst rho t1)).
    { apply lc_open_rec_inv with (k:=0) (x:=x); [exact HxF|exact (proj1 Hcan)]. }
    split; [apply lc_abs; exact Hbodylc|].
    exists (tm_abs T1 (msubst rho t1)); split; [apply multi_refl|].
    split; [apply v_abs; apply lc_abs; exact Hbodylc|].
    exists (msubst rho t1); split; [reflexivity|].
    intros arg Harg.
    assert (Hbody : expression_relation T2
      (msubst (subst_update rho x arg) (open t1 (tm_fvar x)))).
        { apply (IH (tm_size (open t1 (tm_fvar x))) Hsmall
              (update Gamma x T1) (open t1 (tm_fvar x)) T2 eq_refl (H x HxL)).
      - apply proper_subst_update; [exact Hproper|apply value_relation_lc with (T:=T1); exact Harg].
      - apply related_subst_update; [exact Hrelated|exact Harg]. }
        change (expression_relation T2
          (msubst (subst_update rho x arg)
            (open_rec 0 (tm_fvar x) t1))) in Hbody.
        rewrite (msubst_open_rec 0 t1 rho x arg Hproper HxF) in Hbody; exact Hbody.
  - simpl. apply expr_app.
    + apply (IH (tm_size t1)); [simpl in Hsize; lia|exact H0|exact Hproper|exact Hrelated].
    + apply (IH (tm_size t2)); [simpl in Hsize; lia|exact H1|exact Hproper|exact Hrelated].
  - apply expr_of_value_relation; split; [apply v_true|left; reflexivity].
  - apply expr_of_value_relation; split; [apply v_false|right; reflexivity].
  - apply expr_of_value_relation; split; [apply v_nat; apply nv_zero|apply nv_zero].
  - simpl. apply expr_natrec.
    + apply (IH (tm_size n)); [simpl in Hsize; lia|exact H0|exact Hproper|exact Hrelated].
    + apply (IH (tm_size b)); [simpl in Hsize; lia|exact H1|exact Hproper|exact Hrelated].
    + apply (IH (tm_size s)); [simpl in Hsize; lia|exact H2|exact Hproper|exact Hrelated].
  - simpl. apply expr_of_value_relation; split; [apply v_nat; exact H|exact H].
Qed.

Lemma fundamental : forall Gamma t T,
    <{ Gamma |-- t \in T }> ->
    forall rho, proper_substitution rho -> related_substitution Gamma rho ->
      expression_relation T (msubst rho t).
Proof.
  intros Gamma t T HT rho Hp Hr.
  apply (fundamental_aux (tm_size t) Gamma t T eq_refl HT rho Hp Hr).
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> -> strongly_normalizing t.
Proof.
  (* Complete the proof of normalization. *)
Qed.

End STLCNormalizationRecursionMediumTask.
