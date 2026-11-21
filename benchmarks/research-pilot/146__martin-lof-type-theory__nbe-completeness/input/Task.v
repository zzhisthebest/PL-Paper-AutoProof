Require Import Nbe.Utils.Notations Nbe.Syntax.System Nbe.Domain.Nbe.

Theorem NBE_Completeness: forall Gamma t t' A,
  Gamma |-- t === t' : A ->
  exists v,   Nbe A Gamma t v /\   Nbe A Gamma t' v
.
