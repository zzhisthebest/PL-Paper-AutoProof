From Mctt.Core Require Import Base.

From Mctt.Core.Semantic Require Export NbE.

Import Domain_Notations.

Theorem soundness : forall {Γ M A},
    {{ Γ ⊢ M : A }} ->
    exists W, nbe Γ M A W /\ {{ Γ ⊢ M ≈ W : A }}.
