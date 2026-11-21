From Mctt.Algorithmic.Typing Require Import Definitions.

From Mctt.Core Require Import Base.

From Mctt.Frontend Require Import Elaborator.

Import Domain_Notations.

Theorem alg_type_check_sound : forall {Γ i A M},
    {{ Γ ⊢a M ⟸ A }} ->
    {{ ⊢ Γ }} ->
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ ⊢ M : A }}.

Theorem alg_type_check_complete : forall {Γ A M},
    user_exp M ->
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢a M ⟸ A }}.
