Require Import SystemC.Definitions.

Theorem preservation_step : forall s1 s2,
  typing_state s1 ->
  s1 --> s2 ->
  typing_state s2.

Theorem progress_step : forall s1,
  typing_state s1 ->
  done s1 \/ exists s2, s1 --> s2.
