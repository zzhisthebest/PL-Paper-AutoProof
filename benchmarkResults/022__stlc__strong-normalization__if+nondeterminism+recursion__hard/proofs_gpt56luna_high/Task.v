(** STLC CBV strong-normalization benchmark, Hard variant.
    Features: if-nondeterminism-recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Relations.Relation_Definitions Lia.
Import ListNotations.

Module STLCNormalizationIfNondeterminismRecursionHardTask.

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

  | tm_natrec : tm -> tm -> tm -> tm
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
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (open_rec k u t1)
  | tm_natrec n b s =>
      tm_natrec (open_rec k u n) (open_rec k u b) (open_rec k u s)
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
  | lc_zero : forall k, lc_at k tm_zero
  | lc_succ : forall k t, lc_at k t -> lc_at k (tm_succ t)
  | lc_rec : forall k n b s,
      lc_at k n -> lc_at k b -> lc_at k s ->
      lc_at k (tm_natrec n b s)
  | lc_if : forall k t1 t2 t3,
      lc_at k t1 -> lc_at k t2 -> lc_at k t3 -> lc_at k (tm_if t1 t2 t3)
  | lc_choice : forall k t1 t2,
      lc_at k t1 -> lc_at k t2 -> lc_at k (tm_choice t1 t2).

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

(* A finite substitution is used only as proof infrastructure.  A variable
   which is not in the substitution is left as a free variable. *)
Fixpoint slookup (rho : list (atom * tm)) (x : atom) : tm :=
  match rho with
  | nil => tm_fvar x
  | (y,u) :: rho' => if Nat.eqb x y then u else slookup rho' x
  end.

Fixpoint subst_env (rho : list (atom * tm)) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => slookup rho x
  | tm_app t1 t2 => tm_app (subst_env rho t1) (subst_env rho t2)
  | tm_abs T t1 => tm_abs T (subst_env rho t1)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (subst_env rho t1)
  | tm_natrec n b s =>
      tm_natrec (subst_env rho n) (subst_env rho b) (subst_env rho s)
  | tm_if t1 t2 t3 =>
      tm_if (subst_env rho t1) (subst_env rho t2) (subst_env rho t3)
  | tm_choice t1 t2 =>
      tm_choice (subst_env rho t1) (subst_env rho t2)
  end.

Fixpoint fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ => nil
  | tm_fvar x => x :: nil
  | tm_app t1 t2 => fv t1 ++ fv t2
  | tm_abs _ t1 => fv t1
  | tm_true | tm_false | tm_zero => nil
  | tm_succ t1 => fv t1
  | tm_natrec n b s => fv n ++ fv b ++ fv s
  | tm_if t1 t2 t3 => fv t1 ++ fv t2 ++ fv t3
  | tm_choice t1 t2 => fv t1 ++ fv t2
  end.

Fixpoint sdom (rho : list (atom * tm)) : list atom :=
  match rho with
  | nil => nil
  | (x,_) :: rho' => x :: sdom rho'
  end.

Definition SN (t : tm) : Prop := strongly_normalizing t.

(* Computability is deliberately unary.  At function types it contains the
   usual closure-under-application clause.  Local closure is required only
   for arguments, exactly where the supplied CBV rules require it. *)
Fixpoint computable (T : ty) (t : tm) : Prop :=
  match T with
  | Ty_Bool => SN t
  | Ty_Nat => SN t
  | Ty_Arrow A B =>
      SN t /\ (forall u, computable A u -> locally_closed u ->
        computable B (tm_app t u))
  end.

Inductive neutral : tm -> Prop :=
  | n_bvar : forall i, neutral (tm_bvar i)
  | n_fvar : forall x, neutral (tm_fvar x)
  | n_app : forall t u, neutral (tm_app t u)
  | n_rec : forall n b s, neutral (tm_natrec n b s)
  | n_if : forall c t1 t2, neutral (tm_if c t1 t2)
  | n_choice : forall t1 t2, neutral (tm_choice t1 t2).

Lemma nv_not_neutral : forall t, numeric_value t -> ~ neutral t.
Proof.
  intros t H; induction H; intros Hn; inversion Hn; eauto.
Qed.

Lemma neutral_not_value : forall t, neutral t -> ~ value t.
Proof.
  intros t Hn Hv; destruct Hv.
  - inversion Hn.
  - inversion Hn.
  - inversion Hn.
  - eapply nv_not_neutral; eauto.
Qed.

Lemma sn_step : forall t t', SN t -> t --> t' -> SN t'.
Proof.
  intros t t' H Hs; inversion H as [q Hred]; eapply Hred; eauto.
Qed.

Lemma sn_intro : forall t, (forall t', t --> t' -> SN t') -> SN t.
Proof. exact SN_intro. Qed.

Lemma lc_weaken : forall k t, lc_at k t -> lc_at (S k) t.
Proof.
  intros k t H; induction H; econstructor; eauto; lia.
Qed.

Lemma lc_raise : forall k t, lc_at 0 t -> lc_at k t.
Proof.
  induction k as [|k IH]; intros t H; auto.
  apply lc_weaken, IH, H.
Qed.

Lemma lc_open_rec : forall k t u,
    lc_at (S k) t -> lc_at k u -> lc_at k (open_rec k u t).
Proof.
  intros k t; revert k; induction t; intros k u Ht Hu; simpl in *; inversion Ht; subst;
    try solve [econstructor; eauto].
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst; exact Hu.
    + constructor; apply Nat.eqb_neq in E; lia.
  - constructor. eapply IHt; eauto using lc_weaken.
Qed.

Lemma lc_open : forall t u, locally_closed (tm_abs Ty_Bool t) ->
    locally_closed u -> locally_closed (open t u).
Proof.
  intros t u Ht Hu; inversion Ht; simpl; eapply lc_open_rec; eauto.
Qed.

Lemma sn_app_of_neutral : forall t u,
    SN u -> neutral t -> locally_closed u ->
    (forall t', t --> t' -> SN (tm_app t' u)) ->
    SN (tm_app t u).
Proof.
  intros t u Hu Hn Hlu Hred.
  induction Hu as [u Hsteps IHu].
  apply SN_intro; intros t' Hs; inversion Hs; subst.
  - exfalso; eapply neutral_not_value; eauto.
  - apply Hred; assumption.
  - exfalso; eapply neutral_not_value; eauto.
Qed.

Lemma sn_abs : forall T t, SN (tm_abs T t).
Proof. intros; apply SN_intro; intros t' H; inversion H. Qed.

Lemma sn_succ : forall t, SN t -> SN (tm_succ t).
Proof.
  intros t H; induction H as [t Hred IH].
  apply SN_intro; intros t' Hs; inversion Hs; subst; eapply IH; eauto.
Qed.

Lemma lc_subst : forall k t rho,
    lc_at k t -> (forall x, locally_closed (slookup rho x)) ->
    lc_at k (subst_env rho t).
Proof.
  intros k t rho H Hr; induction H; simpl in *; eauto using lc_raise.
  all: apply lc_raise; apply Hr.
Qed.

Lemma lc_open_rec_lc : forall k t u,
    lc_at k t -> lc_at 0 u -> open_rec k u t = t.
Proof.
  intros k t; revert k; induction t; intros k u Ht Hu; simpl in *;
    inversion Ht; subst; try f_equal; eauto.
  all: destruct (Nat.eqb k n) eqn:E;
    [ apply Nat.eqb_eq in E; subst; lia | reflexivity ].
Qed.

Lemma subst_open_rec : forall rho x u t k,
    (forall y, In y (fv t) -> y <> x) ->
    ~ In x (sdom rho) ->
    locally_closed u ->
    (forall y, locally_closed (slookup rho y)) ->
    subst_env ((x,u)::rho) (open_rec k (tm_fvar x) t) =
    open_rec k u (subst_env rho t).
Proof.
  intros rho x u t; induction t as
    [i|a|t1 IH1 t2 IH2|A t IH| | | |t IH
     |n IHn b IHb s IHs|c IHc t1 IH1 t2 IH2|t1 IH1 t2 IH2];
    intros k Hfv Hdom Hu Hrho; simpl in *.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E; subst; simpl; rewrite Nat.eqb_refl; reflexivity.
    + reflexivity.
  - assert (Ha : a <> x) by (apply Hfv; simpl; auto).
    destruct (Nat.eqb a x) eqn:E.
    + exfalso; apply Ha; apply Nat.eqb_eq; exact E.
    + symmetry; apply lc_open_rec_lc.
      * apply lc_raise; apply Hrho.
      * exact Hu.
  - f_equal.
    + apply IH1; try assumption.
      intros y Hy; apply Hfv; apply in_or_app; left; exact Hy.
    + apply IH2; try assumption.
      intros y Hy; apply Hfv; apply in_or_app; right; exact Hy.
  - f_equal; apply IH; eauto.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - f_equal; apply IH; eauto.
  - repeat f_equal.
    + apply IHn; try assumption.
      intros y Hy; apply Hfv; apply in_or_app; left; exact Hy.
    + apply IHb; try assumption.
      intros y Hy; apply Hfv; apply in_or_app; right; apply in_or_app; left; exact Hy.
    + apply IHs; try assumption.
      intros y Hy; apply Hfv; apply in_or_app; right; apply in_or_app; right; exact Hy.
  - repeat f_equal.
    + apply IHc; try assumption.
      intros y Hy; apply Hfv; apply in_or_app; left; exact Hy.
    + apply IH1; try assumption.
      intros y Hy; apply Hfv; apply in_or_app; right; apply in_or_app; left; exact Hy.
    + apply IH2; try assumption.
      intros y Hy; apply Hfv; apply in_or_app; right; apply in_or_app; right; exact Hy.
  - f_equal.
    + apply IH1; try assumption.
      intros y Hy; apply Hfv; apply in_or_app; left; exact Hy.
    + apply IH2; try assumption.
      intros y Hy; apply Hfv; apply in_or_app; right; exact Hy.

Qed.

Lemma slookup_cons_eq : forall rho x u, slookup ((x,u)::rho) x = u.
Proof. intros; simpl; rewrite Nat.eqb_refl; reflexivity. Qed.

Lemma slookup_cons_neq : forall rho x y u,
    x <> y -> slookup ((x,u)::rho) y = slookup rho y.
Proof.
  intros; simpl; destruct (Nat.eqb y x) eqn:E;
    [ exfalso; apply H; symmetry; apply Nat.eqb_eq; auto | reflexivity ].
Qed.

Lemma fold_acc_le : forall l acc, acc <= fold_left Nat.max l acc.
Proof.
  induction l as [|a l IH]; simpl; intros acc; [lia|].
  eapply Nat.le_trans; [apply Nat.le_max_l|apply IH].
Qed.

Lemma fold_max_bound : forall l acc x,
    In x l -> x <= fold_left Nat.max l acc.
Proof.
  induction l as [|a l IH]; simpl; intros acc x H; [inversion H|].
  destruct H as [<-|H].
  - eapply Nat.le_trans; [apply Nat.le_max_r|apply fold_acc_le].
  - eapply IH; eauto.
Qed.

Lemma list_max_bound : forall l x, In x l -> x <= fold_left Nat.max l 0.
Proof. intros; eapply fold_max_bound; eauto. Qed.

Lemma fresh_not_in : forall l : list atom, exists x, ~ In x l.
Proof.
  intros l; exists (S (fold_left Nat.max l 0));
    intro H; pose proof (list_max_bound l _ H); lia.
Qed.

Lemma nv_lc : forall t, numeric_value t -> locally_closed t.
Proof.
  intros t H; induction H; unfold locally_closed; econstructor; eauto.
Qed.

Lemma value_lc : forall t, value t -> locally_closed t.
Proof.
  intros t H; destruct H as [T t Hlc | | | n Hn].
  - exact Hlc.
  - constructor.
  - constructor.
  - apply nv_lc; exact Hn.
Qed.

Lemma comp_red : forall T t t', computable T t -> t --> t' -> computable T t'.
Proof.
  induction T as [| |A B IHA IHB]; simpl; intros t t' H Hs.
  - eapply sn_step; eauto.
  - eapply sn_step; eauto.
  - destruct H as [Hsn Hfun]; split.
    + eapply sn_step; eauto.
    + intros u Hu Hlu.
      eapply IHB; [apply (Hfun u Hu Hlu)|].
      apply ST_App1; eauto.
Qed.

Lemma comp_neutral : forall T t, neutral t ->
    (forall t', t --> t' -> computable T t') -> computable T t.
Proof.
  induction T as [| |A B IHA IHB]; simpl; intros t Hn Hr.
  - apply sn_intro; intros t' Hs; apply (Hr t' Hs).
  - apply sn_intro; intros t' Hs; apply (Hr t' Hs).
  - split.
    + apply sn_intro; intros t' Hs; apply (Hr t' Hs).
    + intros u Hu Hlu; apply IHB with (t := tm_app t u).
      * constructor.
      * intros z Hz; inversion Hz; subst.
        -- exfalso; eapply neutral_not_value; eauto.
        -- destruct (Hr _ H1) as [Hsn Hfun]; eauto.
        -- exfalso; eapply neutral_not_value; eauto.
Qed.

Lemma comp_fvar : forall T x, computable T (tm_fvar x).
Proof.
  intros T x; apply comp_neutral with (T := T) (t := tm_fvar x).
  - apply n_fvar.
  - intros t H; inversion H.
Qed.

Lemma comp_sn : forall T t, computable T t -> SN t.
Proof.
  intros T t H; destruct T; simpl in H; try exact H.
  destruct H as [H _]; exact H.
Qed.

Lemma comp_abs_app : forall A B body,
    (forall u, computable A u -> locally_closed u ->
      computable B (open body u)) ->
    forall u, computable A u -> computable B (tm_app (tm_abs A body) u).
Proof.
  intros A B body Hbody u Hu.
  induction (comp_sn A u Hu) as [u Hred IH].
  apply comp_neutral with (t := tm_app (tm_abs A body) u).
  - constructor.
  - intros z Hz; inversion Hz; subst.
    + apply Hbody; auto using value_lc.
    + inversion H1.
    + apply IH; [ exact H3 | eapply comp_red; eauto ].
Qed.

Lemma comp_abs : forall A B body,
    (forall u, computable A u -> locally_closed u ->
      computable B (open body u)) ->
    computable (Ty_Arrow A B) (tm_abs A body).
Proof.
  intros A B body H; simpl; split.
  - apply sn_abs.
  - intros u Hu Hlu; eapply comp_abs_app; eauto.
Qed.

Lemma comp_if : forall T c t1 t2,
    computable Ty_Bool c -> computable T t1 -> computable T t2 ->
    computable T (tm_if c t1 t2).
Proof.
  intros T c t1 t2 Hc H1 H2.
  induction (match Hc with H => H end) as [c Hred IH].
  apply comp_neutral with (T := T) (t := tm_if c t1 t2).
  - apply n_if.
  - intros z Hz; inversion Hz; subst.
    + exact H1.
    + exact H2.
    + eapply IH; eauto using comp_red.
Qed.

Lemma comp_choice : forall T t1 t2,
    computable T t1 -> computable T t2 -> computable T (tm_choice t1 t2).
Proof.
  intros T t1 t2 H1 H2.
  apply comp_neutral with (T := T) (t := tm_choice t1 t2).
  - apply n_choice.
  - intros z Hz; inversion Hz; subst; eauto.
Qed.

Lemma comp_succ : forall t, computable Ty_Nat t -> computable Ty_Nat (tm_succ t).
Proof. intros; simpl; apply sn_succ; exact H. Qed.

Lemma nv_no_step : forall n, numeric_value n -> forall n', ~ n --> n'.
Proof.
  intros n H; induction H as [|n H IH].
  - intros n' Hs; inversion Hs.
  - intros n' Hs; inversion Hs; subst; eauto.
    all: exfalso; apply (IH t'); assumption.
Qed.

Lemma sn_nv : forall n, numeric_value n -> SN n.
Proof.
  intros n H; induction H as [|n H IH].
  - apply SN_intro; intros z Hz; inversion Hz.
  - apply SN_intro; intros z Hz; inversion Hz; subst.
    exfalso; eapply (nv_no_step n H); eauto.
Qed.

Lemma no_step_bvar : forall i t, ~ tm_bvar i --> t.
Proof. intros; inversion 1. Qed.
Lemma no_step_fvar : forall x t, ~ tm_fvar x --> t.
Proof. intros; inversion 1. Qed.
Lemma no_step_abs : forall A t u, ~ tm_abs A t --> u.
Proof. intros; inversion 1. Qed.
Lemma no_step_true : forall t, ~ tm_true --> t.
Proof. intros; inversion 1. Qed.
Lemma no_step_false : forall t, ~ tm_false --> t.
Proof. intros; inversion 1. Qed.
Lemma no_step_zero : forall t, ~ tm_zero --> t.
Proof. intros; inversion 1. Qed.

Lemma no_nv_bvar : forall i, ~ numeric_value (tm_bvar i). Proof. intros; inversion 1. Qed.
Lemma no_nv_fvar : forall x, ~ numeric_value (tm_fvar x). Proof. intros; inversion 1. Qed.
Lemma no_nv_app : forall t u, ~ numeric_value (tm_app t u). Proof. intros; inversion 1. Qed.
Lemma no_nv_abs : forall A t, ~ numeric_value (tm_abs A t). Proof. intros; inversion 1. Qed.
Lemma no_nv_true : ~ numeric_value tm_true. Proof. inversion 1. Qed.
Lemma no_nv_false : ~ numeric_value tm_false. Proof. inversion 1. Qed.
Lemma no_nv_rec : forall n b s, ~ numeric_value (tm_natrec n b s). Proof. intros; inversion 1. Qed.
Lemma no_nv_if : forall c t1 t2, ~ numeric_value (tm_if c t1 t2). Proof. intros; inversion 1. Qed.
Lemma no_nv_choice : forall t1 t2, ~ numeric_value (tm_choice t1 t2). Proof. intros; inversion 1. Qed.

Lemma comp_rec_nonnum : forall T n b s,
    computable Ty_Nat n ->
    (forall n', n --> n' -> computable Ty_Nat n' ->
      computable T (tm_natrec n' b s)) ->
    ~ numeric_value n -> n <> tm_zero ->
    (forall m, n = tm_succ m -> ~ numeric_value m) ->
    computable T b -> computable (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
    computable T (tm_natrec n b s).
Proof.
  intros T n b s Hn Harg Hnv Hz Hsuc Hb Hs.
  apply comp_neutral with (T := T) (t := tm_natrec n b s).
  - apply n_rec.
  - intros z Hzstep; inversion Hzstep; subst.
    + eapply Harg; [eauto | eapply comp_red; eauto].
    + exfalso; eapply Hnv; eauto.
    + exfalso; eapply Hnv; eauto.
    + exfalso; apply Hz; reflexivity.
    + exfalso; eapply Hsuc; [reflexivity|eauto].
Qed.

Lemma comp_rec_numeric : forall T n, numeric_value n ->
    forall b s, computable T b -> computable (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
    computable T (tm_natrec n b s).
Proof.
  intros T n Hn; induction Hn as [|n Hn IHn]; intros b s Hb Hs.
  - generalize dependent s.
    induction (comp_sn T b Hb) as [b Hbr IHb].
    intros s Hs.
    induction (comp_sn (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s Hs)
      as [s Hsr IHs].
    apply comp_neutral with (T := T) (t := tm_natrec tm_zero b s).
    + apply n_rec.
    + intros z Hz; inversion Hz; subst.
      all: try solve [ exfalso; eapply (nv_no_step tm_zero nv_zero); eauto ].
      all: try solve [ exfalso; apply (nv_no_step tm_zero nv_zero z); assumption ].
      all: try solve [eauto].
      all: try solve [eapply IHb; eauto using comp_red].
      all: eapply IHs; eauto using comp_red.
  - generalize dependent s.
    induction (comp_sn T b Hb) as [b Hbr IHb].
    intros s Hs.
    induction (comp_sn (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s Hs)
      as [s Hsr IHs].
    apply comp_neutral with (T := T) (t := tm_natrec (tm_succ n) b s).
    + apply n_rec.
    + intros z Hz; inversion Hz; subst.
      all: try solve [ exfalso; eapply (nv_no_step (tm_succ n) (nv_succ n Hn)); eauto ].
      all: try solve [eauto].
      all: try solve [eapply IHb; eauto using comp_red].
      all: try solve [eapply IHs; eauto using comp_red].
      destruct Hs as [Hss Hfun].
      assert (Hs' : computable (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s) by
        (split; assumption).
      assert (Hncomp : computable Ty_Nat n) by (simpl; apply sn_nv; exact Hn).
      assert (Hsn : computable (Ty_Arrow T T) (tm_app s n)).
      { apply Hfun.
        - exact Hncomp.
        - apply nv_lc; exact Hn. }
      destruct Hsn as [Hsn Hfun'].
      apply Hfun'.
      * eapply IHn; eauto.
      * unfold locally_closed; apply lc_rec.
        -- apply nv_lc; exact H2.
        -- apply value_lc; exact H4.
        -- apply value_lc; exact H5.
Qed.

Fixpoint numeric_dec (t : tm) : {numeric_value t} + {~ numeric_value t}.
Proof.
  destruct t.
  - right; intro H; inversion H.
  - right; intro H; inversion H.
  - right; intro H; inversion H.
  - right; intro H; inversion H.
  - right; intro H; inversion H.
  - right; intro H; inversion H.
  - left; constructor.
  - destruct (numeric_dec t) as [H|H].
    + left; constructor; exact H.
    + right; intro H'; inversion H'; contradiction.
  - right; intro H; inversion H.
  - right; intro H; inversion H.
  - right; intro H; inversion H.
Defined.

Lemma comp_rec : forall T n b s,
    computable Ty_Nat n -> computable T b ->
    computable (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
    computable T (tm_natrec n b s).
Proof.
  intros T n b s Hn Hb Hs.
  induction (comp_sn Ty_Nat n Hn) as [n Hnr IHn].
  destruct n as [i|x|t1 t2|A t| | | |t|n b0 s0|c t1 t2|t1 t2].
  - apply comp_rec_nonnum.
    + exact Hn.
    + intros n' Hst Hn'; exact (IHn n' Hst Hn').
    + apply no_nv_bvar.
    + intros; discriminate.
    + intros; discriminate.
    + exact Hb.
    + exact Hs.
  - apply comp_rec_nonnum; [exact Hn|intros n' Hst Hn'; exact (IHn n' Hst Hn')|apply no_nv_fvar|intros; discriminate|intros; discriminate|exact Hb|exact Hs].
  - apply comp_rec_nonnum; [exact Hn|intros n' Hst Hn'; exact (IHn n' Hst Hn')|apply no_nv_app|intros; discriminate|intros; discriminate|exact Hb|exact Hs].
  - apply comp_rec_nonnum; [exact Hn|intros n' Hst Hn'; exact (IHn n' Hst Hn')|apply no_nv_abs|intros; discriminate|intros; discriminate|exact Hb|exact Hs].
  - apply comp_rec_nonnum; [exact Hn|intros n' Hst Hn'; exact (IHn n' Hst Hn')|apply no_nv_true|intros; discriminate|intros; discriminate|exact Hb|exact Hs].
  - apply comp_rec_nonnum; [exact Hn|intros n' Hst Hn'; exact (IHn n' Hst Hn')|apply no_nv_false|intros; discriminate|intros; discriminate|exact Hb|exact Hs].
  - apply comp_rec_numeric with (n := tm_zero); [constructor|exact Hb|exact Hs].
  - destruct (numeric_dec t) as [Hnv|Hnv].
    + apply comp_rec_numeric; [constructor; exact Hnv|exact Hb|exact Hs].
    + assert (Hnot : ~ numeric_value (tm_succ t)) by
        (intro H; inversion H; contradiction).
      apply comp_rec_nonnum.
      * exact Hn.
      * intros n' Hst Hn'; exact (IHn n' Hst Hn').
      * exact Hnot.
      * intros; discriminate.
      * intros m E; inversion E; subst m; exact Hnv.
      * exact Hb.
      * exact Hs.
  - apply comp_rec_nonnum; [exact Hn|intros n' Hst Hn'; exact (IHn n' Hst Hn')|apply no_nv_rec|intros; discriminate|intros; discriminate|exact Hb|exact Hs].
  - apply comp_rec_nonnum; [exact Hn|intros n' Hst Hn'; exact (IHn n' Hst Hn')|apply no_nv_if|intros; discriminate|intros; discriminate|exact Hb|exact Hs].
  - apply comp_rec_nonnum; [exact Hn|intros n' Hst Hn'; exact (IHn n' Hst Hn')|apply no_nv_choice|intros; discriminate|intros; discriminate|exact Hb|exact Hs].
Qed.

Lemma lc_open_inv : forall k t u,
    lc_at k (open_rec k u t) -> lc_at (S k) t.
Proof.
  intros k t; revert k; induction t; intros k u H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst; inversion H; apply lc_bvar; lia.
    + apply lc_bvar; inversion H; lia.
  - constructor.
  - inversion H; constructor; eauto.
  - inversion H; constructor; eapply IHt; eauto.
  - constructor.
  - constructor.
  - constructor.
  - inversion H; constructor; eapply IHt; eauto.
  - inversion H; constructor; eauto.
  - inversion H; constructor; eauto.
  - inversion H; constructor; eauto.
Qed.

Lemma typed_lc : forall Gamma t T,
    <{ Gamma |-- t \in T }> -> locally_closed t.
Proof.
  intros Gamma t T H; induction H; unfold locally_closed; simpl.
  - constructor.
  - destruct (fresh_not_in L) as [x Hx].
    specialize (H0 x Hx).
    apply lc_abs; eapply lc_open_inv; exact H0.
  - constructor; eauto.
  - constructor.
  - constructor.
  - constructor.
  - constructor; eauto.
  - constructor; eauto.
  - constructor; eauto.
  - constructor; eauto.
Qed.

Definition env_ok (Gamma : context) (rho : list (atom * tm)) : Prop :=
  (forall x, locally_closed (slookup rho x)) /\
  (forall x T, Gamma x = Some T -> computable T (slookup rho x)).

Lemma env_empty : env_ok empty nil.
Proof.
  split.
  - intros; constructor.
  - intros x T E; discriminate.
Qed.

Lemma subst_nil : forall t, subst_env nil t = t.
Proof. induction t; simpl; f_equal; eauto. Qed.

Lemma subst_lc_typed : forall Gamma t T rho,
    <{ Gamma |-- t \in T }> -> env_ok Gamma rho ->
    locally_closed (subst_env rho t).
Proof.
  intros Gamma t T rho H Hok.
  apply lc_subst with (k := 0) (t := t) (rho := rho).
  - exact (typed_lc Gamma t T H).
  - intros x; apply (proj1 Hok).
Qed.

Lemma fundamental : forall Gamma t T,
    <{ Gamma |-- t \in T }> ->
    forall rho, env_ok Gamma rho -> computable T (subst_env rho t).
Proof.
  intros Gamma t T HT; induction HT as
    [ Gamma x T E
    | L Gamma T1 T2 t1 Hbody IHbody
    | Gamma t1 t2 T1 T2 Hfun IHfun Harg IHarg
    | Gamma
    | Gamma
    | Gamma
    | Gamma n Hn IHn
    | Gamma n b s T Hn IHn Hb IHb Hs IHs
    | Gamma c t1 t2 T Hc IHc H1 IH1 H2 IH2
    | Gamma t1 t2 T H1 IH1 H2 IH2 ];
    intros rho Hok; simpl.
  - apply (proj2 Hok x T E).
  - apply comp_abs; intros u Hu Hlu.
    destruct (fresh_not_in (L ++ sdom rho ++ fv t1)) as [x Hx].
    assert (HxL : ~ In x L) by (intro Hmem; apply Hx; apply in_or_app; left; exact Hmem).
    assert (HxD : ~ In x (sdom rho)) by
      (intro Hmem; apply Hx; apply in_or_app; right; apply in_or_app; left; exact Hmem).
    assert (HxF : ~ In x (fv t1)) by
      (intro Hmem; apply Hx; apply in_or_app; right; apply in_or_app; right; exact Hmem).
    assert (Hok' : env_ok (update Gamma x T1) ((x,u)::rho)).
    { split.
      - intros y; simpl; destruct (Nat.eqb y x) eqn:E.
        + apply Hlu.
        + apply (proj1 Hok).
      - intros y U E; unfold update in E; destruct (Nat.eqb x y) eqn:Exy.
        + apply Nat.eqb_eq in Exy; subst y; simpl; rewrite Nat.eqb_refl.
          inversion E; subst U; exact Hu.
        + rewrite (slookup_cons_neq rho x y u (proj1 (Nat.eqb_neq x y) Exy)).
          apply (proj2 Hok y U E). }
    pose proof (IHbody x HxL ((x,u)::rho) Hok') as Hb.
    assert (Hxfv : forall y, In y (fv t1) -> y <> x) by
      (intros y Hy E; subst y; apply HxF; exact Hy).
    change (computable T2
      (subst_env ((x,u)::rho) (open_rec 0 (tm_fvar x) t1))) in Hb.
    rewrite (subst_open_rec rho x u t1 0 Hxfv HxD Hlu
      (proj1 Hok)) in Hb.
    exact Hb.
  - destruct (IHfun rho Hok) as [HfunSN HfunApp].
    pose proof (subst_lc_typed Gamma t2 T1 rho Harg Hok) as Hla.
    apply HfunApp; [exact (IHarg rho Hok)|exact Hla].
  - apply SN_intro; intros z Hz; inversion Hz.
  - apply SN_intro; intros z Hz; inversion Hz.
  - apply SN_intro; intros z Hz; inversion Hz.
  - apply comp_succ; exact (IHn rho Hok).
  - eapply comp_rec; eauto using IHn, IHb, IHs.
  - eapply comp_if; eauto using IHc, IH1, IH2.
  - eapply comp_choice; eauto using IH1, IH2.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T HT.
  pose proof (fundamental empty t T HT nil env_empty) as H.
  rewrite (subst_nil t) in H.
  exact (comp_sn T t H).
Qed.

End STLCNormalizationIfNondeterminismRecursionHardTask.
