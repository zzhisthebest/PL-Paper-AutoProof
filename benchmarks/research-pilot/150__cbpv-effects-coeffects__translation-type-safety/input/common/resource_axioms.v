Require Export common.coeffects.

Parameter Qnontrivial : Qone <> Qzero.

Parameter Qsumzero : forall q1 q2, Qle Qzero (Qadd q1 q2) ->
  q1 = Qzero /\ q2 = Qzero.

Parameter Qprodzero : forall q1 q2, Qmult q1 q2 = Qzero ->
  q1 = Qzero \/ q2 = Qzero.
