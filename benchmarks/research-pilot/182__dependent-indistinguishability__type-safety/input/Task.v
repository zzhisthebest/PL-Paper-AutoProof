From Qual Require Import Qualitative_ott.

Set Implicit Arguments.

Unset Strict Implicit.

Unset Printing Implicit Defensive.

Local Open Scope order_scope.

Theorem preservation :
    forall a b Γ ψ A,
      Typing Γ ψ a A ->
      Red a b ->
      Typing Γ ψ b A.

Theorem progress : forall ψ a A,
  Typing nil ψ a A ->
  Value a \/ exists b, Red a b.
