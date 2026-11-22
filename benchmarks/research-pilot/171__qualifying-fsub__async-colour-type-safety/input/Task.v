From Fsub.FuncColour Require Import Fsub_LetSum_Definitions.

Theorem preservation : forall E s s',
  typing_state E s ->
  s --> s' ->
  typing_state E s'.

Theorem progress : forall s,
  typing_state empty s ->
  done_state s \/ exists s', s --> s'.
