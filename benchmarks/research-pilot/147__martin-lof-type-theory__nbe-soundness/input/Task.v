Require Import Nbe.Utils.Notations Nbe.Syntax.System Nbe.Domain.Nbe.

Theorem Nbe_Soundness: forall Gamma t T n,
  Gamma |-- t : T -> Nbe T Gamma t n ->
  Gamma |-- t === n : T
.
