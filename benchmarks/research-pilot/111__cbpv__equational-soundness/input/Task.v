Set Implicit Arguments.
From CBPV Require Import ObservationalEquivalence StrongReduction AbstractReductionSystems.

Definition Equiv {n: nat} := equiv (@sstep n).

Theorem equiv_soundness_CBPV n (Gamma: ctx n) A (M N: CBPVc Gamma A):
  Equiv M N -> M ≃ N.
