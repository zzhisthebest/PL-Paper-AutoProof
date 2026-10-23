(** STLC call-by-value strong-normalization benchmark.
    No if-then-else, non-determinism, or recursion is included. *)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Relations.Relation_Definitions.

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

(** * Basic infrastructure: free variables and term-variable substitution *)

Fixpoint fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ => nil
  | tm_fvar x => cons x nil
  | tm_app t1 t2 => app (fv t1) (fv t2)
  | tm_abs _ t1 => fv t1
  | tm_true => nil
  | tm_false => nil
  end.

Fixpoint subst (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_app t1 t2 => tm_app (subst sigma t1) (subst sigma t2)
  | tm_abs T t1 => tm_abs T (subst sigma t1)
  | tm_true => tm_true
  | tm_false => tm_false
  end.

Lemma subst_id : forall t, subst (fun x => tm_fvar x) t = t.
Proof.
  induction t; simpl; try reflexivity; congruence.
Qed.

Lemma subst_agree : forall t sigma sigma',
    (forall x, In x (fv t) -> sigma x = sigma' x) ->
    subst sigma t = subst sigma' t.
Proof.
  intros t. induction t as [i | y | t1 IH1 t2 IH2 | T t1 IH | | ];
    intros sigma sigma' Hag; simpl.
  - reflexivity.
  - apply Hag. simpl. auto.
  - rewrite (IH1 sigma sigma').
    + rewrite (IH2 sigma sigma').
      * reflexivity.
      * intros x Hx. apply Hag. simpl. apply in_or_app. right. exact Hx.
    + intros x Hx. apply Hag. simpl. apply in_or_app. left. exact Hx.
  - rewrite (IH sigma sigma').
    + reflexivity.
    + intros x Hx. apply Hag. exact Hx.
  - reflexivity.
  - reflexivity.
Qed.

(** * Fresh atoms *)

Definition fresh (L : list atom) : atom := S (fold_right Nat.max 0 L).

Lemma le_fold_max : forall (L : list atom) (x : atom),
    In x L -> x <= fold_right Nat.max 0 L.
Proof.
  induction L as [| a L IH]; intros x Hx.
  - inversion Hx.
  - simpl in Hx. simpl. destruct Hx as [-> | Hx].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; exact Hx | apply Nat.le_max_r].
Qed.

Lemma fresh_not_in : forall L, ~ In (fresh L) L.
Proof.
  intros L Hx. unfold fresh in Hx. apply le_fold_max in Hx.
  exact (Nat.nle_succ_diag_l (fold_right Nat.max 0 L) Hx).
Qed.

Lemma fresh_not_in_app_l : forall L1 L2, ~ In (fresh (L1 ++ L2)) L1.
Proof.
  intros L1 L2 Hx. apply fresh_not_in with (L := L1 ++ L2).
  apply in_or_app. left. exact Hx.
Qed.

Lemma fresh_not_in_app_r : forall L1 L2, ~ In (fresh (L1 ++ L2)) L2.
Proof.
  intros L1 L2 Hx. apply fresh_not_in with (L := L1 ++ L2).
  apply in_or_app. right. exact Hx.
Qed.

Lemma fv_open_rec : forall (t : tm) (x : atom) (k : nat) (y : atom),
    In y (fv t) -> y = x \/ In y (fv (open_rec k (tm_fvar x) t)).
Proof.
  intros t. induction t as [i | a | t1 IH1 t2 IH2 | T t1 IH | | ];
    intros x k y H; simpl in *.
  - inversion H.
  - right. exact H.
  - apply in_app_iff in H. destruct H as [H | H].
    + destruct (IH1 x k y H) as [-> | H']; [left; reflexivity |].
      right. apply in_or_app. left. exact H'.
    + destruct (IH2 x k y H) as [-> | H']; [left; reflexivity |].
      right. apply in_or_app. right. exact H'.
  - destruct (IH x (S k) y H) as [-> | H'].
    + left. reflexivity.
    + right. exact H'.
  - inversion H.
  - inversion H.
Qed.

(** * Local closure under opening and substitution *)

Lemma lt_of_lt_succ_neq : forall i k : nat, i < S k -> i <> k -> i < k.
Proof.
  intros i k H Hneq.
  pose proof (proj1 (Nat.lt_succ_r i k) H) as Hle.
  destruct (proj1 (Nat.lt_eq_cases i k) Hle) as [Hlt | Heq]; [exact Hlt |].
  exfalso. apply Hneq. exact Heq.
Qed.

Lemma lc_at_S : forall (k : nat) (t : tm), lc_at k t -> lc_at (S k) t.
Proof.
  intros k t H. induction H as [k i Hlt | k x | k a b Ha IHa Hb IHb
                               | k T body Hbody IH | k | k].
  - apply lc_bvar. apply Nat.lt_succ_r, Nat.lt_le_incl. exact Hlt.
  - apply lc_fvar.
  - apply lc_app; assumption.
  - apply lc_abs; assumption.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma lc_bvar_inv : forall (k : nat) (i : nat), lc_at k (tm_bvar i) -> i < k.
Proof. intros k i H. inversion H. assumption. Qed.

Lemma lc_app_inv : forall (k : nat) (t1 t2 : tm),
    lc_at k (tm_app t1 t2) -> lc_at k t1 /\ lc_at k t2.
Proof. intros k t1 t2 H. inversion H. auto. Qed.

Lemma lc_abs_inv : forall (k : nat) (T : ty) (body : tm),
    lc_at k (tm_abs T body) -> lc_at (S k) body.
Proof. intros k T body H. inversion H. assumption. Qed.

Lemma lc_open : forall k (body : tm) (u : tm),
    lc_at (S k) body -> lc_at k u -> lc_at k (open_rec k u body).
Proof.
  intros k body. revert k.
  induction body as [i | x | t1 IH1 t2 IH2 | T t1 IH | | ];
    intros k u Hbody Hu; simpl.
  - destruct (Nat.eqb k i) eqn:E.
    + assumption.
    + apply lc_bvar. pose proof (proj1 (Nat.eqb_neq k i) E) as Eneq.
      inversion Hbody as [kk ii Hlt | | | | | ]; subst.
      apply (lt_of_lt_succ_neq i k); [exact Hlt | exact (Nat.neq_sym k i Eneq)].
  - apply lc_fvar.
  - apply lc_app.
    + apply IH1; [| exact Hu]. inversion Hbody; assumption.
    + apply IH2; [| exact Hu]. inversion Hbody; assumption.
  - apply lc_abs. apply (IH (S k) u).
    + inversion Hbody; assumption.
    + apply lc_at_S. exact Hu.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma lc_open_fvar_inv : forall k (body : tm) (x : atom),
    lc_at k (open_rec k (tm_fvar x) body) -> lc_at (S k) body.
Proof.
  intros k body. revert k.
  induction body as [i | y | t1 IH1 t2 IH2 | T t1 IH | | ]; intros k x H.
  - simpl in H. destruct (Nat.eqb k i) eqn:E.
    + apply lc_bvar. pose proof (proj1 (Nat.eqb_eq k i) E) as Heqk. subst. apply Nat.lt_succ_diag_r.
    + apply lc_bvar. pose proof (proj1 (Nat.eqb_neq k i) E) as Eneq.
      inversion H as [kk ii Hlt | | | | | ]; subst.
      apply Nat.lt_succ_r. apply Nat.lt_le_incl. exact Hlt.
  - simpl in H. apply lc_fvar.
  - simpl in H. inversion H as [| | kk a b Ha Hb | | |]; subst.
    apply lc_app; [apply (IH1 k x) | apply (IH2 k x)]; assumption.
  - simpl in H. inversion H as [| | | kk T' t' Ht | |]; subst.
    apply lc_abs. apply (IH (S k) x). assumption.
  - simpl in H. inversion H. apply lc_true.
  - simpl in H. inversion H. apply lc_false.
Qed.

Lemma lc_at_le : forall (k k' : nat) (t : tm), k <= k' -> lc_at k t -> lc_at k' t.
Proof.
  intros k k' t Hle H. revert k' Hle.
  induction H as [k0 i Hlt | k0 x | k0 a b Ha IHa Hb IHb
                 | k0 T body Hbody IH | k0 | k0]; intros k' Hle.
  - apply lc_bvar. eapply Nat.lt_le_trans; [exact Hlt | exact Hle].
  - apply lc_fvar.
  - apply lc_app; [apply IHa; exact Hle | apply IHb; exact Hle].
  - apply lc_abs. apply IH. exact (proj1 (Nat.succ_le_mono k0 k') Hle).
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma lc_subst : forall sigma,
    (forall x, lc_at 0 (sigma x)) ->
    forall k t, lc_at k t -> lc_at k (subst sigma t).
Proof.
  intros sigma Hsigma. intros k t. revert k.
  induction t as [i | x | t1 IH1 t2 IH2 | T t1 IH | | ]; intros k H; simpl.
  - apply lc_bvar. inversion H; assumption.
  - apply (lc_at_le 0 k (sigma x)); [apply Nat.le_0_l | apply Hsigma].
  - apply lc_app; [apply IH1 | apply IH2]; inversion H; assumption.
  - apply lc_abs. apply IH. inversion H; assumption.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma lc_open_rec_id : forall (t : tm) (k : nat),
    lc_at k t -> forall (k' : nat) (u : tm), k <= k' -> open_rec k' u t = t.
Proof.
  intros t. induction t as [i | x | t1 IH1 t2 IH2 | T t1 IH | | ];
    intros k H k' u Hle; simpl.
  - destruct (Nat.eqb k' i) eqn:E.
    + exfalso.
      pose proof (proj1 (Nat.eqb_eq k' i) E) as Hk'i.
      pose proof (lc_bvar_inv k i H) as Hlt.
      pose proof (Nat.lt_le_trans i k k' Hlt Hle) as Hik'.
      rewrite Hk'i in Hik'.
      exact (Nat.lt_irrefl i Hik').
    + reflexivity.
  - reflexivity.
  - pose proof (lc_app_inv k t1 t2 H) as [H1 H2].
    rewrite (IH1 k H1 k' u Hle). rewrite (IH2 k H2 k' u Hle). reflexivity.
  - pose proof (lc_abs_inv k T t1 H) as Hbody.
    rewrite (IH (S k) Hbody (S k') u).
    + reflexivity.
    + exact (proj1 (Nat.succ_le_mono k k') Hle).
  - reflexivity.
  - reflexivity.
Qed.

(** * Substitution commutes with opening a fresh variable *)

Lemma subst_open_fvar : forall (t : tm) (sigma : atom -> tm) (x : atom) (u : tm) (k : nat),
    lc_at 0 u ->
    (forall y, lc_at 0 (sigma y)) ->
    ~ In x (fv t) ->
    subst (fun y => if Nat.eqb x y then u else sigma y)
          (open_rec k (tm_fvar x) t)
    = open_rec k u (subst sigma t).
Proof.
  induction t as [i | y | t1 IH1 t2 IH2 | T t1 IH | | ];
    intros sigma x u k Hu Hsigma Hx; simpl.
  - destruct (Nat.eqb k i).
    + simpl. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - assert (Hy : y <> x) by (intro E; subst; apply Hx; simpl; auto).
    pose proof (proj2 (Nat.eqb_neq x y) (fun E => Hy (eq_sym E))) as Hneq.
    rewrite Hneq. symmetry.
    apply (lc_open_rec_id (sigma y) 0 (Hsigma y) k u (Nat.le_0_l k)).
  - rewrite (IH1 sigma x u k Hu Hsigma).
    + rewrite (IH2 sigma x u k Hu Hsigma).
      * reflexivity.
      * intro H; apply Hx; apply in_or_app; right; exact H.
    + intro H; apply Hx; apply in_or_app; left; exact H.
  - rewrite (IH sigma x u (S k) Hu Hsigma); [reflexivity | exact Hx].
  - reflexivity.
  - reflexivity.
Qed.

(** * Inversion and basic properties of the operational semantics *)

Lemma value_no_step : forall (v t' : tm), value v -> v --> t' -> False.
Proof.
  intros v t' Hv Hstep. destruct Hv as [T body Hlc | | ]; inversion Hstep.
Qed.

Lemma abs_no_step : forall (T : ty) (body t' : tm), tm_abs T body --> t' -> False.
Proof. intros T body t' H. inversion H. Qed.

Lemma app_not_value : forall (t u : tm), value (tm_app t u) -> False.
Proof. intros t u H. inversion H. Qed.

Lemma value_lc : forall (v : tm), value v -> lc_at 0 v.
Proof.
  intros v Hv. destruct Hv as [T body Hlc | | ].
  - exact Hlc.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma value_sn : forall (v : tm), value v -> strongly_normalizing v.
Proof.
  intros v Hv. apply SN_intro. intros t' Hstep.
  exfalso. exact (value_no_step v t' Hv Hstep).
Qed.

Lemma SN_step : forall t t', strongly_normalizing t -> t --> t' -> strongly_normalizing t'.
Proof.
  intros t t' HSN Hstep. induction HSN as [t0 Hred IH].
  exact (Hred t' Hstep).
Qed.

Lemma multi_trans : forall (x y z : tm), x -->* y -> y -->* z -> x -->* z.
Proof.
  intros x y z Hm. induction Hm as [a | a b c Hab Hbc IH]; intros Hm2.
  - exact Hm2.
  - apply multi_step with (y := b).
    + exact Hab.
    + apply IH. exact Hm2.
Qed.

Lemma multi_sn : forall (t t' : tm), strongly_normalizing t -> t -->* t' -> strongly_normalizing t'.
Proof.
  intros t t' HSN Hm. revert HSN.
  induction Hm as [x | x y z Hxy Hyz IH]; intros HSN.
  - exact HSN.
  - apply IH. exact (SN_step x y HSN Hxy).
Qed.

Lemma multi_stuck : forall (t : tm),
    (forall t', t --> t' -> False) -> forall t', t -->* t' -> t' = t.
Proof.
  intros t Hns t' Hm. revert Hns.
  induction Hm as [x | x y z Hxy Hyz IH]; intros Hns.
  - reflexivity.
  - exfalso. exact (Hns y Hxy).
Qed.

Lemma step_lc : forall (t t' : tm), t --> t' -> lc_at 0 t -> lc_at 0 t'.
Proof.
  intros t t' H. induction H as [T body v Hlc Hval | t1 t1' t2 Hstep IH Hlc2
                               | v1 t2 t2' Hval Hstep IH]; intros Hlcin.
  - (* ST_AppAbs *)
    destruct (lc_app_inv 0 (tm_abs T body) v Hlcin) as [H1 H2].
    apply (lc_open 0 body v).
    + apply (lc_abs_inv 0 T body H1).
    + exact H2.
  - (* ST_App1 *)
    destruct (lc_app_inv 0 t1 t2 Hlcin) as [H1 H2].
    apply lc_app.
    + apply IH. exact H1.
    + exact H2.
  - (* ST_App2 *)
    destruct (lc_app_inv 0 v1 t2 Hlcin) as [H1 H2].
    apply lc_app.
    + exact H1.
    + apply IH. exact H2.
Qed.

Lemma lc_typing : forall (Gamma : context) (t : tm) (T : ty),
    has_type Gamma t T -> lc_at 0 t.
Proof.
  intros Gamma t T H.
  induction H as [Gamma x T Hx
                 | L Gamma T1 T2 t1 Hprem IH
                 | Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
                 | Gamma | Gamma].
  - apply lc_fvar.
  - apply lc_abs.
    apply (lc_open_fvar_inv 0 t1 (fresh L)).
    apply IH. apply fresh_not_in.
  - apply lc_app; assumption.
  - apply lc_true.
  - apply lc_false.
Qed.

(** * The logical relation *)

Fixpoint R (T : ty) (t : tm) : Prop :=
  match T with
  | Ty_Bool => lc_at 0 t /\ strongly_normalizing t
  | Ty_Arrow T1 T2 =>
      lc_at 0 t /\ strongly_normalizing t /\
      (forall v, multi step t v -> value v ->
        forall (Tbody : ty) (body : tm), v = tm_abs Tbody body ->
          forall u, R T1 u -> R T2 (open body u))
  end.

Definition Vclause (B : ty) (w : tm) : Prop :=
  match B with
  | Ty_Bool => True
  | Ty_Arrow B1 B2 =>
      forall v, multi step w v -> value v ->
        forall (Tbody : ty) (body : tm), v = tm_abs Tbody body ->
          forall u, R B1 u -> R B2 (open body u)
  end.

Lemma R_iff : forall (B : ty) (w : tm),
    R B w <-> lc_at 0 w /\ strongly_normalizing w /\ Vclause B w.
Proof.
  intros B w. destruct B as [| B1 B2]; simpl.
  - split.
    + intros [H1 H2]. split; [exact H1 | split; [exact H2 | exact I]].
    + intros [H1 [H2 _]]. split; assumption.
  - split.
    + intros [H1 [H2 H3]]. split; [exact H1 | split; [exact H2 | exact H3]].
    + intros [H1 [H2 H3]]. split; [exact H1 | split; [exact H2 | exact H3]].
Qed.

Lemma R_lc : forall (T : ty) (t : tm), R T t -> lc_at 0 t.
Proof.
  intros T t H. apply R_iff in H. destruct H as [H1 _]. exact H1.
Qed.

Lemma R_sn : forall (T : ty) (t : tm), R T t -> strongly_normalizing t.
Proof.
  intros T t H. apply R_iff in H. destruct H as [_ [H2 _]]. exact H2.
Qed.

Lemma R_vclause : forall (T : ty) (t : tm), R T t -> Vclause T t.
Proof.
  intros T t H. apply R_iff in H. destruct H as [_ [_ H3]]. exact H3.
Qed.

Lemma R_step : forall (T : ty) (t t' : tm), R T t -> t --> t' -> R T t'.
Proof.
  intros T t t' H Hstep.
  apply R_iff in H. destruct H as [Hlc [Hsn Hvc]].
  apply R_iff. split.
  - apply (step_lc t t' Hstep Hlc).
  - split.
    + apply (SN_step t t' Hsn Hstep).
    + destruct T as [| B1 B2]; simpl in *.
      * exact I.
      * intros v Hm Hval Tbody body Heq w HRw.
        apply (Hvc v (multi_step step t t' v Hstep Hm) Hval Tbody body Heq w HRw).
Qed.

Lemma R_multi : forall (T : ty) (t t' : tm), R T t -> t -->* t' -> R T t'.
Proof.
  intros T t t' H Hm. revert H.
  induction Hm as [x | x y z Hxy Hyz IH]; intros H.
  - exact H.
  - apply IH. apply (R_step T x y H Hxy).
Qed.

Lemma R_abs : forall (A B : ty) (Tbody : ty) (body : tm),
    lc_at 1 body ->
    (forall u, R A u -> R B (open body u)) ->
    R (Ty_Arrow A B) (tm_abs Tbody body).
Proof.
  intros A B Tbody body Hlc Hbody.
  apply R_iff. split.
  - apply lc_abs. exact Hlc.
  - split.
    + apply SN_intro. intros t' Hstep.
      exfalso. exact (abs_no_step Tbody body t' Hstep).
    + simpl. intros v Hm Hval Tbody' body' Heq w HRw.
      assert (Hv : v = tm_abs Tbody body).
      { apply (multi_stuck (tm_abs Tbody body)).
        - intros t' Hs. exact (abs_no_step Tbody body t' Hs).
        - exact Hm. }
      assert (Heq' : tm_abs Tbody body = tm_abs Tbody' body').
      { rewrite <- Hv. exact Heq. }
      injection Heq' as HT Hb. subst Tbody' body'.
      apply Hbody. exact HRw.
Qed.

Lemma multi_first_step : forall (s v : tm), s -->* v ->
    s = v \/ (exists s', s --> s' /\ s' -->* v).
Proof.
  intros s v H. induction H as [x | x y z Hxy Hyz IH].
  - left. reflexivity.
  - right. exists y. split; assumption.
Qed.

Lemma step_app_inv : forall (t u w : tm), tm_app t u --> w ->
    (exists (Tbody : ty) (body : tm),
        t = tm_abs Tbody body /\ value (tm_abs Tbody body) /\ value u /\ w = open body u)
    \/ (exists t', t --> t' /\ w = tm_app t' u)
    \/ (exists u', value t /\ u --> u' /\ w = tm_app t u').
Proof.
  intros t u w H. inversion H; subst.
  - left. exists T, t0. split; [reflexivity | split].
    + apply v_abs. assumption.
    + split; [assumption | reflexivity].
  - right. left. exists t1'. split; [assumption | reflexivity].
  - right. right. exists t2'. split; [assumption | split].
    + assumption.
    + reflexivity.
Qed.

Lemma R_app_value : forall (A B : ty) (t u : tm),
    value t ->
    (forall v, t -->* v -> value v ->
       forall (Tbody : ty) (body : tm), v = tm_abs Tbody body ->
         forall w, R A w -> R B (open body w)) ->
    strongly_normalizing u ->
    R A u ->
    R B (tm_app t u).
Proof.
  intros A B t u Hval Hclos HSNu HRu.
  revert B Hclos HRu.
  induction HSNu as [u0 Hured IHu].
  intros B Hclos HRu.
  assert (Hlct : lc_at 0 t) by (apply value_lc; exact Hval).
  assert (Hlcu : lc_at 0 u0) by (apply (R_lc A); exact HRu).
  apply R_iff. split.
  - apply lc_app; assumption.
  - split.
    + apply SN_intro. intros w Hstep.
      destruct (step_app_inv t u0 w Hstep) as
        [[Tbody [body [Heq [Hvabs [Hvalu Hw]]]]]
        | [[t' [Hstep' Hw]] | [u' [Hvalt [Hstep' Hw]]]]].
      * subst t. subst w.
        apply R_sn with (T := B).
        exact (Hclos (tm_abs Tbody body) (multi_refl step (tm_abs Tbody body))
                     Hvabs Tbody body eq_refl u0 HRu).
      * subst w. exfalso. exact (value_no_step t t' Hval Hstep').
      * subst w.
        apply R_sn with (T := B).
        apply IHu.
        -- exact Hstep'.
        -- exact Hclos.
        -- apply (R_step A u0 u' HRu Hstep').
    + destruct B as [| B1 B2].
      * exact I.
      * simpl. intros v Hm Hvalv Tbody' body' Heqv w0 HRw.
        destruct (multi_first_step (tm_app t u0) v Hm) as [Heq | [s' [Hstep Hrest]]].
        -- exfalso. apply (app_not_value t u0). rewrite Heq. exact Hvalv.
        -- destruct (step_app_inv t u0 s' Hstep) as
             [[Tbody [body [Heq [Hvabs [Hvalu Hw]]]]]
             | [[t' [Hstep' Hw]] | [u' [Hvalt [Hstep' Hw]]]]].
           ++ subst t. subst s'.
              assert (HRs' : R (Ty_Arrow B1 B2) (open body u0)).
              { exact (Hclos (tm_abs Tbody body) (multi_refl step (tm_abs Tbody body))
                             Hvabs Tbody body eq_refl u0 HRu). }
              pose proof (R_multi (Ty_Arrow B1 B2) (open body u0) v HRs' Hrest) as HRv.
              exact (R_vclause (Ty_Arrow B1 B2) v HRv v (multi_refl step v)
                               Hvalv Tbody' body' Heqv w0 HRw).
           ++ subst s'. exfalso. exact (value_no_step t t' Hval Hstep').
           ++ subst s'.
              pose proof (IHu u' Hstep' (Ty_Arrow B1 B2) Hclos
                               (R_step A u0 u' HRu Hstep')) as HRs'.
              pose proof (R_multi (Ty_Arrow B1 B2) (tm_app t u') v HRs' Hrest) as HRv.
              exact (R_vclause (Ty_Arrow B1 B2) v HRv v (multi_refl step v)
                               Hvalv Tbody' body' Heqv w0 HRw).
Qed.

Lemma R_app_aux : forall (A B : ty) (t u : tm),
    lc_at 0 t ->
    strongly_normalizing t ->
    (forall v, t -->* v -> value v ->
       forall (Tbody : ty) (body : tm), v = tm_abs Tbody body ->
         forall w, R A w -> R B (open body w)) ->
    R A u ->
    R B (tm_app t u).
Proof.
  intros A B t u Hlct HSNt Hclos HRu.
  revert B Hclos Hlct.
  induction HSNt as [t0 Hred IH].
  intros B Hclos Hlct.
  assert (Hlcu : lc_at 0 u) by (apply (R_lc A); exact HRu).
  assert (HSNu : strongly_normalizing u) by (apply (R_sn A); exact HRu).
  apply R_iff. split.
  - apply lc_app; assumption.
  - split.
    + apply SN_intro. intros w Hstep.
      destruct (step_app_inv t0 u w Hstep) as
        [[Tbody [body [Heq [Hvabs [Hvalu Hw]]]]]
        | [[t' [Hstep' Hw]] | [u' [Hvalt [Hstep' Hw]]]]].
      * subst t0. subst w.
        apply R_sn with (T := B).
        exact (Hclos (tm_abs Tbody body) (multi_refl step (tm_abs Tbody body))
                     Hvabs Tbody body eq_refl u HRu).
      * subst w.
        apply R_sn with (T := B).
        apply (IH t' Hstep' B).
        -- intros v Hm Hval Tbody0 body0 Heq0 w0 HRw0.
           exact (Hclos v (multi_step step t0 t' v Hstep' Hm) Hval Tbody0 body0 Heq0 w0 HRw0).
        -- apply (step_lc t0 t' Hstep' Hlct).
      * subst w.
        apply R_sn with (T := B).
        apply (R_app_value A B t0 u').
        -- exact Hvalt.
        -- exact Hclos.
        -- apply (SN_step u u' HSNu Hstep').
        -- apply (R_step A u u' HRu Hstep').
    + destruct B as [| B1 B2].
      * exact I.
      * simpl. intros v Hm Hvalv Tbody' body' Heqv w0 HRw.
        destruct (multi_first_step (tm_app t0 u) v Hm) as [Heq | [s' [Hstep Hrest]]].
        -- exfalso. apply (app_not_value t0 u). rewrite Heq. exact Hvalv.
        -- destruct (step_app_inv t0 u s' Hstep) as
             [[Tb [bd [Heqb [Hvabsb [Hvalub Hwb]]]]]
             | [[t1 [Hst1 Hw1]] | [u1 [Hvalt1 [Hst2 Hw2]]]]].
           ++ subst t0. subst s'.
              assert (HRs' : R (Ty_Arrow B1 B2) (open bd u)).
              { exact (Hclos (tm_abs Tb bd) (multi_refl step (tm_abs Tb bd))
                             Hvabsb Tb bd eq_refl u HRu). }
              pose proof (R_multi (Ty_Arrow B1 B2) (open bd u) v HRs' Hrest) as HRv.
              exact (R_vclause (Ty_Arrow B1 B2) v HRv v (multi_refl step v)
                               Hvalv Tbody' body' Heqv w0 HRw).
           ++ subst s'.
              pose proof (IH t1 Hst1 (Ty_Arrow B1 B2)) as IH'.
              pose proof (IH' (fun v Hm0 Hval0 Tb0 bd0 Heq0 ww HRw0 =>
                                 Hclos v (multi_step step t0 t1 v Hst1 Hm0)
                                       Hval0 Tb0 bd0 Heq0 ww HRw0)
                              (step_lc t0 t1 Hst1 Hlct)) as HRs'.
              pose proof (R_multi (Ty_Arrow B1 B2) (tm_app t1 u) v HRs' Hrest) as HRv.
              exact (R_vclause (Ty_Arrow B1 B2) v HRv v (multi_refl step v)
                               Hvalv Tbody' body' Heqv w0 HRw).
           ++ subst s'.
              pose proof (R_app_value A (Ty_Arrow B1 B2) t0 u1 Hvalt1 Hclos
                            (SN_step u u1 HSNu Hst2)
                            (R_step A u u1 HRu Hst2)) as HRs'.
              pose proof (R_multi (Ty_Arrow B1 B2) (tm_app t0 u1) v HRs' Hrest) as HRv.
              exact (R_vclause (Ty_Arrow B1 B2) v HRv v (multi_refl step v)
                               Hvalv Tbody' body' Heqv w0 HRw).
Qed.

Lemma R_app : forall (A B : ty) (t u : tm),
    R (Ty_Arrow A B) t -> R A u -> R B (tm_app t u).
Proof.
  intros A B t u HRt HRu.
  apply R_iff in HRt. destruct HRt as [Hlc [Hsn Hclos]].
  apply (R_app_aux A B t u Hlc Hsn Hclos HRu).
Qed.

Lemma fundamental : forall (Gamma : context) (t : tm) (T : ty),
    has_type Gamma t T ->
    forall sigma,
      (forall x, lc_at 0 (sigma x)) ->
      (forall x A, Gamma x = Some A -> R A (sigma x)) ->
      R T (subst sigma t).
Proof.
  intros Gamma t T H.
  induction H as [Gamma x T Hx
                 | L Gamma T1 T2 t1 Hprem IH
                 | Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
                 | Gamma | Gamma].
  - (* T_Var *) intros sigma Hlc Hctx. simpl. apply Hctx. exact Hx.
  - (* T_Abs *) intros sigma Hlc Hctx. simpl.
    apply R_abs.
    + (* local closure of the substituted body *)
      apply (lc_subst sigma Hlc 1 t1).
      apply (lc_open_fvar_inv 0 t1 (fresh L)).
      apply (lc_typing (update Gamma (fresh L) T1)
                       (open t1 (tm_fvar (fresh L))) T2).
      apply Hprem. apply fresh_not_in.
    + (* body behaviour for every semantic argument *)
      intros u HRu.
      set (x := fresh (L ++ fv t1)).
      assert (HxL : ~ In x L) by (subst x; apply fresh_not_in_app_l).
      assert (Hxfv : ~ In x (fv t1)) by (subst x; apply fresh_not_in_app_r).
      assert (Hlc' : forall y,
                 lc_at 0 ((fun y => if Nat.eqb x y then u else sigma y) y)).
      { intro y. destruct (Nat.eqb x y) eqn:E.
        - apply (R_lc T1 u HRu).
        - apply Hlc. }
      assert (Hctx' : forall y A0,
                 update Gamma x T1 y = Some A0 ->
                 R A0 ((fun y => if Nat.eqb x y then u else sigma y) y)).
      { intros y A0 Hy. destruct (Nat.eqb x y) eqn:E.
        - pose proof (proj1 (Nat.eqb_eq x y) E) as Hyx. subst y.
          unfold update in Hy. rewrite Nat.eqb_refl in Hy.
          injection Hy as HA. subst A0.
          simpl. exact HRu.
        - apply Hctx with (A := A0). unfold update in Hy. rewrite E in Hy. exact Hy. }
      pose proof (IH x HxL (fun y => if Nat.eqb x y then u else sigma y)
                    Hlc' Hctx') as HRbody.
      change (R T2 (subst (fun y => if Nat.eqb x y then u else sigma y)
                          (open_rec 0 (tm_fvar x) t1))) in HRbody.
      rewrite (subst_open_fvar t1 sigma x u 0 (R_lc T1 u HRu) Hlc Hxfv) in HRbody.
      exact HRbody.
  - (* T_App *) intros sigma Hlc Hctx. simpl.
    apply (R_app T1 T2).
    + apply IH1; assumption.
    + apply IH2; assumption.
  - (* T_True *) intros sigma Hlc Hctx. simpl. split.
    + apply lc_true.
    + apply value_sn. constructor.
  - (* T_False *) intros sigma Hlc Hctx. simpl. split.
    + apply lc_false.
    + apply value_sn. constructor.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  assert (Hlc : forall x, lc_at 0 ((fun x => tm_fvar x) x))
    by (intro x; apply lc_fvar).
  assert (Hctx : forall x A, empty x = Some A -> R A ((fun x => tm_fvar x) x)).
  { intros x A Hx. unfold empty in Hx. discriminate. }
  pose proof (fundamental empty t T Hty (fun x => tm_fvar x) Hlc Hctx) as HR.
  rewrite subst_id in HR.
  exact (R_sn T t HR).
Qed.

End STLCNormalizationNoneHardTask.
