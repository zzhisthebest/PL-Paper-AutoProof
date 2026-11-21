Require Import full.CBPV.semantics.

Require Import full.CBPV.typing.

Theorem soundness :
  (forall V A, VWt null null V A -> exists W,
    EvalVal null null V W) /\
  (forall M q A ϕ, CWt null null M (CF q A) ϕ ->
    exists T ϕ1,
    EvalComp null null M T ϕ1 /\ ϕ1 E<= ϕ).
