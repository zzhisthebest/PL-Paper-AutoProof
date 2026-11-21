Require Import CCsub_Definitions.

Theorem preservation : forall Σ Σ' V,
  state_typing Σ V ->
  Σ --> Σ' ->
  state_typing Σ' V.

Theorem progress : forall Σ V,
  state_typing Σ V ->
  state_final Σ \/ exists Σ', Σ --> Σ'.
