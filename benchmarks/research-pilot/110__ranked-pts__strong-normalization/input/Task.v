From PTSrk Require Import Typing.

Theorem strong_normalization {n} Γ (t T: Term nat n):
  wf Γ -> Γ ⊢ t ⇐ T -> sn t.
