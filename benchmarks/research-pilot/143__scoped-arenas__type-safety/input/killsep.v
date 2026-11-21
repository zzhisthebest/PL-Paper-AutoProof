Require Export Arith.EqNat.

Require Export PeanoNat.

Require Import Coq.Arith.Arith.

Require Import Coq.Bool.Bool.

Require Import Coq.Program.Equality.

Require Import Coq.Lists.List.

Require Import Psatz.

Require Import ZArith.

Require Import Coq.Arith.Compare_dec.

Import ListNotations.

Require Import vars.

Require Import env.

Require Import nats.

Require Import qualifiers.

Require Import boolean.

Require Import lang.

Require Import qenv.

Require Import ops.

Import QualNotations.

Local Open Scope qualifiers.

Import OpeningNotations.

Local Open Scope opening.

Import SplicingNotations.

Local Open Scope splicing.

Import SubstitutionNotations.

Local Open Scope substitutions.

Definition kill_sep (ϰ : qual) (q : qual) : Prop :=
  q ⊓ ϰ ⊑↑ {♦}.

Fixpoint q_remove' (Σ : senv) (k : loc) (q : qual) (fuel : nat) : qual :=
  match fuel with
  | 0 => ∅
  | S x => if (qlocs q (x)) && negb (qlocs (&!x) k)
      then qor (q_remove' Σ k q x) (&!x)
      else (q_remove' Σ k q x)
  end.

Definition q_remove (Σ : senv) (k : loc) (q : qual) : qual :=
  q_remove' Σ k q (‖Σ‖) ⊔ (qfresh q, qfvs q, qbvs q, n_empty).
