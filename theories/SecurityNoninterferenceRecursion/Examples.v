From AutoProof.SecurityNoninterferenceRecursion Require Import
  Syntax Semantics Typing Evaluation Metatheory Substitution
  LogicalRelation Noninterference.
Import ListNotations.
From Stdlib Require Import Lia.

Definition increment_step : tm :=
  tm_abs (Ty_Nat public)
    (tm_abs (Ty_Nat public) (tm_succ (tm_bvar 0) Low) public) public.

Lemma increment_step_typed : forall Gamma,
  has_type Gamma increment_step
    (Ty_Arrow (Ty_Nat public) (Ty_Arrow (Ty_Nat public) (Ty_Nat public) public) public).
Proof.
  intro Gamma. apply T_Abs with (L := []); [exact I | exact I |].
  intros x Hx. apply T_Abs with (L := []); [exact I | exact I |].
  intros y Hy. simpl. change (has_type (update (update Gamma x (Ty_Nat public)) y (Ty_Nat public))
    (tm_succ (tm_fvar y) Low) (ty_protect Low (Ty_Nat public))).
  eapply T_Succ with (k := public).
  - apply T_Var; [apply lookup_update_eq | exact I].
  - exact I.
Qed.

Lemma unroll_increment : forall n b,
  big_step (natrec_unroll n (tm_nat b public) increment_step High)
    (tm_nat (n + b) public).
Proof.
  induction n; intro b; simpl; [apply B_Nat |].
  change (big_step (tm_app (tm_app increment_step (tm_nat n public) High)
    (natrec_unroll n (tm_nat b public) increment_step High) High)
    (protect_value (tm_nat (S (n + b)) public) Low)).
  eapply B_App with (A := Ty_Nat public) (body := tm_succ (tm_bvar 0) Low)
    (k := public) (v := tm_nat (n + b) public).
  - change (big_step (tm_app increment_step (tm_nat n public) High)
      (protect_value (tm_abs (Ty_Nat public) (tm_succ (tm_bvar 0) Low) public) Low)).
    eapply B_App with (A := Ty_Nat public)
      (body := tm_abs (Ty_Nat public) (tm_succ (tm_bvar 0) Low) public)
      (k := public) (v := tm_nat n public).
    + apply B_Abs. unfold locally_closed. simpl. lia.
    + apply B_Nat.
    + exact I.
    + apply B_Abs. unfold locally_closed. simpl. lia.
  - apply IHn.
  - exact I.
  - change (big_step (tm_succ (tm_nat (n + b) public) Low)
      (protect_value (tm_nat (S (n + b)) public) Low)).
    eapply B_Succ with (k := public); [apply B_Nat | exact I].
Qed.

Definition secret_computed_count := tm_succ (tm_nat 1 secret) High.
Definition secret_count_result :=
  tm_natrec secret_computed_count (tm_nat 0 public) increment_step High.

Example runtime_count_typed : has_type empty secret_count_result (Ty_Nat secret).
Proof.
  change (has_type empty secret_count_result (ty_protect High (Ty_Nat public))).
  eapply T_NatRec with (k := secret).
  - change (has_type empty secret_computed_count (ty_protect High (Ty_Nat public))).
    eapply T_Succ with (k := secret); [apply T_Nat; exact I | exact I].
  - apply T_Nat. exact I.
  - apply increment_step_typed.
  - exact I.
Qed.

Example runtime_count_evaluates : evaluates secret_count_result (tm_nat 2 secret).
Proof.
  apply big_step_iff_evaluates.
  change (big_step secret_count_result (protect_value (tm_nat 2 public) High)).
  eapply B_NatRec with (m := 2) (k := secret)
    (vb := tm_nat 0 public) (vs := increment_step).
  - change (big_step secret_computed_count (protect_value (tm_nat 2 public) High)).
    eapply B_Succ with (k := secret); [apply B_Nat | exact I].
  - apply B_Nat.
  - apply B_Abs. unfold locally_closed, increment_step. simpl. lia.
  - exact I.
  - exact (unroll_increment 2 0).
Qed.

Definition recursive_context : program_context :=
  C_Fst (C_PairRight (tm_nat 7 public)
    (C_RecArg C_Hole (tm_nat 0 public) increment_step High) public) Low.

Lemma recursive_context_typed :
  context_has_type recursive_context (Ty_Nat secret) (Ty_Nat public).
Proof.
  exists []. intros x Hx.
  change (has_type (update empty x (Ty_Nat secret))
    (plug recursive_context (tm_fvar x)) (ty_protect Low (Ty_Nat public))).
  eapply T_Fst with (T2 := Ty_Nat secret) (kappa := public); [|exact I].
  apply T_Pair; [apply T_Nat; exact I | | exact I].
  change (has_type (update empty x (Ty_Nat secret))
    (tm_natrec (tm_fvar x) (tm_nat 0 public) increment_step High)
    (ty_protect High (Ty_Nat public))).
  eapply T_NatRec with (k := secret).
  - apply T_Var; [apply lookup_update_eq | exact I].
  - apply T_Nat. exact I.
  - apply increment_step_typed.
  - exact I.
Qed.

Example changing_secret_count_preserves_public_result : forall n m,
  same_result (plug recursive_context (tm_nat n secret))
              (plug recursive_context (tm_nat m secret)).
Proof.
  intros. apply noninterference with (T_secret := Ty_Nat secret) (T_result := Ty_Nat public).
  - apply T_Nat. exact I.
  - apply T_Nat. exact I.
  - exact recursive_context_typed.
  - exact I.
  - repeat split; exact I.
  - exact (fun H => H).
Qed.

Example recursive_context_returns_seven : forall n,
  evaluates (plug recursive_context (tm_nat n secret)) (tm_nat 7 public).
Proof.
  intro n. apply big_step_iff_evaluates.
  change (big_step (plug recursive_context (tm_nat n secret)) (protect_value (tm_nat 7 public) Low)).
  eapply B_Fst with (k := public) (b := tm_nat (n + 0) secret); [|exact I].
  apply B_Pair; [apply B_Nat |].
  change (big_step (tm_natrec (tm_nat n secret) (tm_nat 0 public) increment_step High)
    (protect_value (tm_nat (n + 0) public) High)).
  eapply B_NatRec with (m := n) (k := secret) (vb := tm_nat 0 public) (vs := increment_step).
  - apply B_Nat.
  - apply B_Nat.
  - apply B_Abs. unfold locally_closed, increment_step. simpl. lia.
  - exact I.
  - apply unroll_increment.
Qed.

Print Assumptions changing_secret_count_preserves_public_result.
Print Assumptions runtime_count_evaluates.
