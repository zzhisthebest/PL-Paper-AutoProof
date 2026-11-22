From CBPV Require Import StrongReduction AbstractReductionSystems.

Theorem confluence n:
   confluent (@sstep n) /\ confluent (@sstep_value n).
