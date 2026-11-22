From Qual Require Import Qualitative_ott.

Set Implicit Arguments.

Unset Strict Implicit.

Unset Printing Implicit Defensive.

Local Open Scope order_scope.

Theorem non_interference
    ψ a0 b0 v0 v1
    (h0 : GDefEq nil ψ a0 b0)
    (h1 : Typing nil ψ a0 a_Bool)
    (h2 : Typing nil ψ b0 a_Bool)
    (h3 : Reds a0 v0)
    (h4 : Reds b0 v1)
    (hv0 : Value v0)
    (hv1 : Value v1) :
    v0 = v1.
