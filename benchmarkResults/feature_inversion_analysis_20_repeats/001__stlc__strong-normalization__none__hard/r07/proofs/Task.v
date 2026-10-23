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

(* ================================================================ *)
(* Development: strong normalization via a logical relation         *)
(* ================================================================ *)

(* ---------------- Free variables and freshness ---------------- *)

Fixpoint fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ => nil
  | tm_fvar x => x :: nil
  | tm_app t1 t2 => fv t1 ++ fv t2
  | tm_abs _ t1 => fv t1
  | tm_true => nil
  | tm_false => nil
  end.

Fixpoint max_list (l : list atom) : nat :=
  match l with
  | nil => 0
  | x :: xs => Nat.max x (max_list xs)
  end.

Lemma max_list_ub : forall (l : list atom) x, In x l -> x <= max_list l.
Proof.
  induction l as [| y ys IH]; intros x Hin; simpl in *.
  - destruct Hin.
  - destruct Hin as [-> | Hin].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; eassumption | apply Nat.le_max_r].
Qed.

Lemma fresh_atom : forall l : list atom, exists x : atom, ~ In x l.
Proof.
  intros l. exists (S (max_list l)). intro Hin.
  pose proof (max_list_ub l _ Hin). lia.
Qed.

(* ---------------- Local closure lemmas ---------------- *)

Lemma lc_at_mono : forall (t : tm) k k', k <= k' -> lc_at k t -> lc_at k' t.
Proof.
  intros t k k' Hle H. revert k' Hle.
  induction H as [k i Hi | k x | k t1 t2 H1 IH1 H2 IH2 | k T t1 H1 IH1 | k | k];
    intros k' Hle.
  - apply lc_bvar. lia.
  - apply lc_fvar.
  - apply lc_app.
    + apply IH1. assumption.
    + apply IH2. assumption.
  - apply lc_abs. apply IH1. lia.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma lc_open : forall (t : tm) k u,
  lc_at (S k) t -> lc_at k u -> lc_at k (open_rec k u t).
Proof.
  induction t as [n | x | t1 IH1 t2 IH2 | T t1 IH | | ]; intros k u Ht Hu; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. exact Hu.
    + apply lc_bvar. apply Nat.eqb_neq in E.
      inversion Ht as [k0 i Hi | | | | |]; subst. lia.
  - apply lc_fvar.
  - inversion Ht as [| | k0 a b Ha Hb | | |]; subst.
    apply lc_app.
    + apply IH1; assumption.
    + apply IH2; assumption.
  - apply lc_abs. apply IH.
    + inversion Ht as [| | | k0 T0 t0 H0 | |]; subst. exact H0.
    + apply lc_at_mono with (k := k); [lia | exact Hu].
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma lc_open_inv : forall (t : tm) k u,
  lc_at k (open_rec k u t) -> lc_at 0 u -> lc_at (S k) t.
Proof.
  induction t as [n | x | t1 IH1 t2 IH2 | T t1 IH | | ]; intros k u H Hlu; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. apply lc_bvar. lia.
    + apply Nat.eqb_neq in E. apply lc_bvar.
      inversion H as [k0 i Hi | | | | |]; subst. lia.
  - apply lc_fvar.
  - inversion H as [| | k0 a b Ha Hb | | |]; subst.
    apply lc_app.
    + apply IH1 with (u := u); assumption.
    + apply IH2 with (u := u); assumption.
  - apply lc_abs. apply IH with (u := u).
    + inversion H as [| | | k0 T0 t0 H0 | |]; subst. exact H0.
    + exact Hlu.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma lc_open_rec_id : forall (t : tm) k u, lc_at k t -> open_rec k u t = t.
Proof.
  induction t as [n | x | t1 IH1 t2 IH2 | T t1 IH | | ]; intros k u H; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. inversion H; lia.
    + reflexivity.
  - reflexivity.
  - inversion H as [| | k0 a b Ha Hb | | |]; subst.
    rewrite (IH1 k u Ha), (IH2 k u Hb). reflexivity.
  - inversion H as [| | | k0 T0 t0 H0 | |]; subst.
    rewrite (IH (S k) u H0). reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(* ---------------- Values and steps ---------------- *)

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v Hv. induction Hv as [T t Hlc | | ].
  - exact Hlc.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma value_app_false : forall t1 t2, ~ value (tm_app t1 t2).
Proof. intros t1 t2 Hv. inversion Hv. Qed.

Lemma step_abs_false : forall (T : ty) (t t' : tm), ~ (tm_abs T t --> t').
Proof. intros T t t' H. inversion H. Qed.

Lemma lc_step : forall t t', t --> t' -> locally_closed t -> locally_closed t'.
Proof.
  intros t t' Hstep.
  induction Hstep as [T body v Hlcabs Hv | t1 t1' t2 Hs IHs Hlc2 | v1 t2 t2' Hv Hs IHs2];
    intros Hlc.
  - apply lc_open.
    + inversion Hlcabs as [| | | k T0 t0 H0 | |]; subst. exact H0.
    + apply value_lc. exact Hv.
  - apply lc_app.
    + apply IHs. inversion Hlc as [| | k a b Ha Hb | | |]; subst. exact Ha.
    + exact Hlc2.
  - apply lc_app.
    + apply value_lc. exact Hv.
    + apply IHs2. inversion Hlc as [| | k a b Ha Hb | | |]; subst. exact Hb.
Qed.

(* ---------------- Strong normalization basics ---------------- *)

Lemma SN_abs : forall (T : ty) (t : tm), strongly_normalizing (tm_abs T t).
Proof. intros T t. apply SN_intro. intros t' H. inversion H. Qed.

Lemma SN_true : strongly_normalizing tm_true.
Proof. apply SN_intro. intros t' H. inversion H. Qed.

Lemma SN_false : strongly_normalizing tm_false.
Proof. apply SN_intro. intros t' H. inversion H. Qed.

Lemma SN_step : forall t, strongly_normalizing t -> forall t', t --> t' -> strongly_normalizing t'.
Proof.
  intros t Hsn. induction Hsn as [t Hred IHred]. intros t' Hstep. apply Hred. exact Hstep.
Qed.

(* ---------------- Inert (stuck) terms ---------------- *)

Inductive inert : tm -> Prop :=
  | inert_fvar : forall x, inert (tm_fvar x)
  | inert_bvar : forall i, inert (tm_bvar i)
  | inert_app : forall t1 t2, inert t1 -> inert (tm_app t1 t2).

Lemma inert_not_value : forall t, inert t -> value t -> False.
Proof.
  intros t Hi. induction Hi as [x | i | t1 t2 Hi IH].
  - intros Hv. inversion Hv.
  - intros Hv. inversion Hv.
  - intros Hv. inversion Hv.
Qed.

Lemma inert_no_step : forall t, inert t -> forall t', ~ (t --> t').
Proof.
  intros t Hi. induction Hi as [x | i | t1 t2 Hi IH].
  - intros t' Hstep. inversion Hstep.
  - intros t' Hstep. inversion Hstep.
  - intros t' Hstep. inversion Hstep; subst.
    + inversion Hi.
    + eapply IH. eassumption.
    + eapply inert_not_value; eassumption.
Qed.

Lemma inert_SN : forall t, inert t -> strongly_normalizing t.
Proof.
  intros t Hi. apply SN_intro. intros t' Hstep.
  exfalso. exact (inert_no_step t Hi t' Hstep).
Qed.

(* ---------------- The logical relation ---------------- *)

Fixpoint LR (T : ty) : tm -> Prop :=
  match T with
  | Ty_Bool => fun t => locally_closed t /\ strongly_normalizing t
  | Ty_Arrow A B =>
      fun t => locally_closed t /\ strongly_normalizing t /\
               (forall s, LR A s -> LR B (tm_app t s))
  end.

Lemma LR_lc : forall T t, LR T t -> locally_closed t.
Proof.
  intros T t H. destruct T as [| A B]; simpl in H.
  - destruct H as [Hlc Hsn]. exact Hlc.
  - destruct H as [Hlc [Hsn Happ]]. exact Hlc.
Qed.

Lemma LR_SN : forall T t, LR T t -> strongly_normalizing t.
Proof.
  intros T t H. destruct T as [| A B]; simpl in H.
  - destruct H as [Hlc Hsn]. exact Hsn.
  - destruct H as [Hlc [Hsn Happ]]. exact Hsn.
Qed.

Lemma LR_app : forall A B t s, LR (Ty_Arrow A B) t -> LR A s -> LR B (tm_app t s).
Proof.
  intros A B t s H Hs. simpl in H.
  destruct H as [Hlc [Hsn Happ]]. apply Happ. exact Hs.
Qed.

Lemma inert_LR : forall T t, inert t -> locally_closed t -> LR T t.
Proof.
  induction T as [| A IHA B IHB]; intros t Hi Hlc; simpl.
  - split; [exact Hlc | apply inert_SN; exact Hi].
  - split; [exact Hlc | split; [apply inert_SN; exact Hi |]].
    intros s Hs. apply IHB.
    + apply inert_app. exact Hi.
    + simpl. apply lc_app.
      * exact Hlc.
      * apply LR_lc with (T := A). exact Hs.
Qed.

Lemma fvar_LR : forall T x, LR T (tm_fvar x).
Proof.
  intros T x. apply inert_LR.
  - apply inert_fvar.
  - apply lc_fvar.
Qed.

Lemma LR_step : forall T t, LR T t -> forall t', t --> t' -> LR T t'.
Proof.
  intros T. induction T as [| A IHA B IHB]; intros t HLR t' Hstep; simpl in *.
  - destruct HLR as [Hlc Hsn]. split.
    + eapply lc_step; eassumption.
    + eapply SN_step; eassumption.
  - destruct HLR as [Hlc [Hsn Happ]]. split.
    + eapply lc_step; eassumption.
    + split.
      * eapply SN_step; eassumption.
      * intros s Hs.
        apply (IHB (tm_app t s) (Happ s Hs) (tm_app t' s)).
        simpl. apply ST_App1.
        -- exact Hstep.
        -- apply LR_lc with (T := A). exact Hs.
Qed.

Lemma LR_of_reducts : forall T t,
  locally_closed t ->
  strongly_normalizing t ->
  ~ value t ->
  (forall t', t --> t' -> LR T t') ->
  LR T t.
Proof.
  induction T as [| A IHA B IHB]; intros t Hlc Hsn Hnv Hred; simpl.
  - split; assumption.
  - split; [exact Hlc | split; [exact Hsn |]].
    intros s Hs.
    apply IHB with (t := tm_app t s).
    + simpl. apply lc_app.
      * exact Hlc.
      * apply LR_lc with (T := A). exact Hs.
    + apply SN_intro. intros r Hr. inversion Hr; subst.
      * exfalso. eapply Hnv. apply v_abs. assumption.
      * apply LR_SN with (T := B). apply LR_app with (A := A).
        -- apply Hred. eassumption.
        -- exact Hs.
      * exfalso. eapply Hnv. assumption.
    + intros Hv. exact (value_app_false t s Hv).
    + intros r Hr. inversion Hr; subst.
      * exfalso. eapply Hnv. apply v_abs. assumption.
      * apply LR_app with (A := A).
        -- apply Hred. eassumption.
        -- exact Hs.
      * exfalso. eapply Hnv. assumption.
Qed.

(* Inversion of a step at an application headed by an abstraction. *)
Lemma step_app_abs_inv : forall (A : ty) (body s t' : tm),
  tm_app (tm_abs A body) s --> t' ->
  (value s /\ t' = open body s) \/
  (exists s', s --> s' /\ t' = tm_app (tm_abs A body) s').
Proof.
  intros A body s t' H. inversion H; subst.
  - left. split; [assumption | reflexivity].
  - exfalso. eapply step_abs_false. eassumption.
  - right. eexists. split; [eassumption | reflexivity].
Qed.

Lemma LR_abs_app : forall s,
  strongly_normalizing s ->
  forall (A : ty) (body : tm) (B : ty),
    locally_closed (tm_abs A body) ->
    (forall s', LR A s' -> LR B (open body s')) ->
    LR A s ->
    LR B (tm_app (tm_abs A body) s).
Proof.
  intros s Hsn. induction Hsn as [s Hred IHred].
  intros A body B Hlcabs Hopen HAs.
  assert (Hsn_app : strongly_normalizing (tm_app (tm_abs A body) s)).
  { apply SN_intro. intros t' Hstep.
    destruct (step_app_abs_inv A body s t' Hstep) as [[Hv Heq] | [s' [Hs' Heq]]].
    - subst t'. apply LR_SN with (T := B). apply Hopen. exact HAs.
    - subst t'. apply LR_SN with (T := B).
      apply (IHred s' Hs' A body B Hlcabs Hopen).
      eapply LR_step; eassumption. }
  apply LR_of_reducts with (t := tm_app (tm_abs A body) s).
  - simpl. apply lc_app.
    + exact Hlcabs.
    + apply LR_lc with (T := A). exact HAs.
  - exact Hsn_app.
  - intro Hv. exact (value_app_false _ _ Hv).
  - intros t' Hstep.
    destruct (step_app_abs_inv A body s t' Hstep) as [[Hv Heq] | [s' [Hs' Heq]]].
    + subst t'. apply Hopen. exact HAs.
    + subst t'. apply (IHred s' Hs' A body B Hlcabs Hopen).
      eapply LR_step; eassumption.
Qed.

(* ---------------- Simultaneous substitution ---------------- *)

Fixpoint subst (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_app t1 t2 => tm_app (subst sigma t1) (subst sigma t2)
  | tm_abs T t1 => tm_abs T (subst sigma t1)
  | tm_true => tm_true
  | tm_false => tm_false
  end.

Definition subst_update (sigma : atom -> tm) (x : atom) (v : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then v else sigma y.

Lemma subst_update_same : forall sigma x v, subst_update sigma x v x = v.
Proof.
  intros. unfold subst_update. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma subst_update_diff : forall sigma x v y, x <> y -> subst_update sigma x v y = sigma y.
Proof.
  intros. unfold subst_update. apply Nat.eqb_neq in H. rewrite H. reflexivity.
Qed.

Lemma subst_id : forall t, subst (fun x => tm_fvar x) t = t.
Proof.
  induction t as [i | x | t1 IH1 t2 IH2 | T t1 IH | | ]; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma subst_open_gen : forall (t : tm) k x sigma v,
  ~ In x (fv t) ->
  (forall y, locally_closed (sigma y)) ->
  locally_closed v ->
  subst (subst_update sigma x v) (open_rec k (tm_fvar x) t)
  = open_rec k v (subst sigma t).
Proof.
  induction t as [n | y | t1 IH1 t2 IH2 | T t1 IH | | ];
    intros k x sigma v Hfresh Hslc Hv; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. simpl. apply subst_update_same.
    + reflexivity.
  - assert (Hxy : x <> y).
    { intro Heq. apply Hfresh. rewrite Heq. simpl. left. reflexivity. }
    rewrite subst_update_diff; [| exact Hxy].
    symmetry. apply lc_open_rec_id.
    apply lc_at_mono with (k := 0); [lia | apply Hslc].
  - f_equal.
    + apply IH1.
      * intro Hin. apply Hfresh. apply in_or_app. left. exact Hin.
      * exact Hslc.
      * exact Hv.
    + apply IH2.
      * intro Hin. apply Hfresh. apply in_or_app. right. exact Hin.
      * exact Hslc.
      * exact Hv.
  - f_equal. apply IH.
    + simpl in Hfresh. exact Hfresh.
    + exact Hslc.
    + exact Hv.
  - reflexivity.
  - reflexivity.
Qed.

(* ---------------- Context / substitution interpretation ---------------- *)

Definition subst_lc (sigma : atom -> tm) : Prop :=
  forall y, locally_closed (sigma y).

Definition env_ok (Gamma : context) (sigma : atom -> tm) : Prop :=
  subst_lc sigma /\ (forall x T, Gamma x = Some T -> LR T (sigma x)).

Lemma env_ok_update_fvar : forall Gamma sigma x T1,
  env_ok Gamma sigma ->
  env_ok (update Gamma x T1) (subst_update sigma x (tm_fvar x)).
Proof.
  intros Gamma sigma x T1 [Hslc Henv]. split.
  - intros y. destruct (Nat.eq_dec x y) as [-> | Hne].
    + rewrite subst_update_same. apply lc_fvar.
    + rewrite subst_update_diff; [apply Hslc | exact Hne].
  - intros y T' Hy. destruct (Nat.eq_dec x y) as [-> | Hne].
    + rewrite subst_update_same. unfold update in Hy. rewrite Nat.eqb_refl in Hy.
      simpl in Hy. injection Hy as Hy. subst T'. apply fvar_LR.
    + rewrite subst_update_diff; [| exact Hne].
      apply Henv. unfold update in Hy.
      assert (E : (x =? y) = false) by (apply Nat.eqb_neq; exact Hne).
      rewrite E in Hy. exact Hy.
Qed.

Lemma env_ok_update : forall Gamma sigma x T1 v,
  env_ok Gamma sigma ->
  LR T1 v ->
  env_ok (update Gamma x T1) (subst_update sigma x v).
Proof.
  intros Gamma sigma x T1 v [Hslc Henv] Hv. split.
  - intros y. destruct (Nat.eq_dec x y) as [-> | Hne].
    + rewrite subst_update_same. apply LR_lc with (T := T1). exact Hv.
    + rewrite subst_update_diff; [apply Hslc | exact Hne].
  - intros y T' Hy. destruct (Nat.eq_dec x y) as [-> | Hne].
    + rewrite subst_update_same. unfold update in Hy. rewrite Nat.eqb_refl in Hy.
      simpl in Hy. injection Hy as Hy. subst T'. exact Hv.
    + rewrite subst_update_diff; [| exact Hne].
      apply Henv. unfold update in Hy.
      assert (E : (x =? y) = false) by (apply Nat.eqb_neq; exact Hne).
      rewrite E in Hy. exact Hy.
Qed.

(* ---------------- Fundamental theorem ---------------- *)

Lemma fundamental : forall Gamma t T,
  has_type Gamma t T ->
  forall sigma, env_ok Gamma sigma -> LR T (subst sigma t).
Proof.
  intros Gamma t T H.
  induction H as [Gamma x T Hx
                 | L Gamma T1 T2 t1 Hbody IHbody
                 | Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
                 | Gamma
                 | Gamma].
  - (* T_Var *)
    intros sigma [Hslc Henv]. simpl. apply Henv. exact Hx.
  - (* T_Abs *)
    intros sigma [Hslc Henv].
    destruct (fresh_atom (L ++ fv t1)) as [x Hx].
    assert (HxL : ~ In x L).
    { intro Hin. apply Hx. apply in_or_app. left. exact Hin. }
    assert (Hxfv : ~ In x (fv t1)).
    { intro Hin. apply Hx. apply in_or_app. right. exact Hin. }
    assert (Henv_fx : env_ok (update Gamma x T1) (subst_update sigma x (tm_fvar x))).
    { apply env_ok_update_fvar. split; assumption. }
    assert (Hbody_fx : LR T2 (open (subst sigma t1) (tm_fvar x))).
    { assert (H0 := IHbody x HxL (subst_update sigma x (tm_fvar x)) Henv_fx).
      assert (Heq : subst (subst_update sigma x (tm_fvar x)) (open t1 (tm_fvar x))
                     = open (subst sigma t1) (tm_fvar x)).
      { apply subst_open_gen.
        - exact Hxfv.
        - exact Hslc.
        - apply lc_fvar. }
      rewrite Heq in H0. exact H0. }
    assert (Hlcabs : locally_closed (tm_abs T1 (subst sigma t1))).
    { apply lc_abs. apply lc_open_inv with (u := tm_fvar x) (k := 0).
      - apply LR_lc with (T := T2). exact Hbody_fx.
      - apply lc_fvar. }
    simpl. split.
    + exact Hlcabs.
    + split.
      * apply SN_abs.
      * intros s Hs.
        apply (LR_abs_app s (LR_SN T1 s Hs) T1 (subst sigma t1) T2 Hlcabs).
        -- intros s' Hs'.
           assert (Henv_s : env_ok (update Gamma x T1) (subst_update sigma x s')).
           { apply env_ok_update; [split; assumption | exact Hs']. }
           assert (H0 := IHbody x HxL (subst_update sigma x s') Henv_s).
           assert (Heq : subst (subst_update sigma x s') (open t1 (tm_fvar x))
                        = open (subst sigma t1) s').
           { apply subst_open_gen.
             - exact Hxfv.
             - exact Hslc.
             - apply LR_lc with (T := T1). exact Hs'. }
           rewrite Heq in H0. exact H0.
        -- exact Hs.
  - (* T_App *)
    intros sigma [Hslc Henv]. simpl.
    apply LR_app with (A := T1).
    + apply IH1. split; assumption.
    + apply IH2. split; assumption.
  - (* T_True *)
    intros sigma [Hslc Henv]. simpl. split.
    + apply lc_true.
    + apply SN_true.
  - (* T_False *)
    intros sigma [Hslc Henv]. simpl. split.
    + apply lc_false.
    + apply SN_false.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T H.
  assert (Henv : env_ok empty (fun x => tm_fvar x)).
  { split.
    - intros y. apply lc_fvar.
    - intros x T' Hx. simpl in Hx. discriminate. }
  assert (HLR := fundamental empty t T H (fun x => tm_fvar x) Henv).
  rewrite subst_id in HLR.
  apply LR_SN with (T := T). exact HLR.
Qed.

End STLCNormalizationNoneHardTask.
