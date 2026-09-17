From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
From AutoProof Require Import Smallstep.
From AutoProof.STLCRecursion Require Import Syntax StlcProp Infrastructure Norm.
Import ListNotations.

Module STLCRecExamples.
Import STLCRec STLCRecProp STLCRecInfrastructure STLCRecNorm.

Definition add_step : tm :=
  tm_abs Ty_Nat (tm_abs Ty_Nat (tm_succ (tm_bvar 0))).

Definition add (n m : nat) : tm :=
  tm_natrec (numeral n) (numeral m) add_step.

Lemma numeral_typed : forall Gamma n,
  has_type Gamma (numeral n) Ty_Nat.
Proof.
  intros Gamma n. induction n; simpl.
  - apply T_Zero.
  - apply T_Succ. exact IHn.
Qed.

Lemma add_step_typed : forall Gamma,
  has_type Gamma add_step (Ty_Arrow Ty_Nat (Ty_Arrow Ty_Nat Ty_Nat)).
Proof.
  intros Gamma. unfold add_step.
  apply T_Abs with (L := []). intros x Hx. simpl. unfold open. simpl.
  apply T_Abs with (L := []). intros y Hy. unfold open. simpl.
  apply T_Succ. apply T_Var. apply update_eq.
Qed.

Lemma add_step_value : value add_step.
Proof.
  apply v_abs. unfold add_step, locally_closed.
  repeat constructor.
Qed.

Example add_typed : forall n m,
  has_type empty (add n m) Ty_Nat.
Proof.
  intros n m. unfold add. apply T_Rec.
  - apply numeral_typed.
  - apply numeral_typed.
  - apply add_step_typed.
Qed.

Lemma add_evaluates : forall n m,
  add n m -->* numeral (n + m).
Proof.
  induction n as [|n IH]; intros m; unfold add in *; simpl.
  - eapply multi_step.
    + apply ST_RecZero.
      * apply v_nat. apply numeral_numeric.
      * apply add_step_value.
    + apply multi_refl.
  - eapply multi_step.
    + apply ST_RecSucc.
      * apply numeral_numeric.
      * apply v_nat. apply numeral_numeric.
      * apply add_step_value.
    + eapply multi_trans with
        (u := tm_app (tm_abs Ty_Nat (tm_succ (tm_bvar 0)))
          (tm_natrec (numeral n) (numeral m) add_step)).
      * eapply multi_step.
        -- apply ST_App1.
           ++ apply ST_AppAbs.
              ** apply value_regular. apply add_step_value.
              ** apply v_nat. apply numeral_numeric.
           ++ apply typing_regular with (Gamma := empty) (T := Ty_Nat).
              apply add_typed.
        -- apply multi_refl.
      * eapply multi_trans with
          (u := tm_app (tm_abs Ty_Nat (tm_succ (tm_bvar 0))) (numeral (n + m))).
        -- apply multi_app2.
           ++ apply v_abs. unfold locally_closed. repeat constructor.
           ++ apply IH.
        -- eapply multi_step.
           ++ apply ST_AppAbs.
              ** unfold locally_closed. repeat constructor.
              ** apply v_nat. apply numeral_numeric.
           ++ apply multi_refl.
Qed.

Example two_plus_three : add 2 3 -->* numeral 5.
Proof. apply (add_evaluates 2 3). Qed.

Definition nat_identity : tm := tm_abs Ty_Nat (tm_bvar 0).

Definition keep_step (T : ty) : tm :=
  tm_abs Ty_Nat (tm_abs T (tm_bvar 0)).

Lemma keep_step_typed : forall Gamma T,
  has_type Gamma (keep_step T) (Ty_Arrow Ty_Nat (Ty_Arrow T T)).
Proof.
  intros Gamma T. unfold keep_step.
  apply T_Abs with (L := []). intros x Hx. unfold open. simpl.
  apply T_Abs with (L := []). intros y Hy. unfold open. simpl.
  apply T_Var. apply update_eq.
Qed.

Example function_result_typed : forall n,
  has_type empty
    (tm_natrec (numeral n) nat_identity (keep_step (Ty_Arrow Ty_Nat Ty_Nat)))
    (Ty_Arrow Ty_Nat Ty_Nat).
Proof.
  intros n. apply T_Rec.
  - apply numeral_typed.
  - unfold nat_identity. apply T_Abs with (L := []). intros x Hx.
    unfold open. simpl. apply T_Var. apply update_eq.
  - apply keep_step_typed.
Qed.

Example function_result_normalizes : forall n,
  strongly_normalizing
    (tm_natrec (numeral n) nat_identity (keep_step (Ty_Arrow Ty_Nat Ty_Nat))).
Proof.
  intros n. apply normalization with (T := Ty_Arrow Ty_Nat Ty_Nat).
  apply function_result_typed.
Qed.

End STLCRecExamples.
