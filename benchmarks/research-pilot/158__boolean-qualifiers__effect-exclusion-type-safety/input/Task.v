Require Import Fsub.EffectExclusion.Tactics.

Require Import Coq.Program.Equality.

Require Export Fsub.EffectExclusion.Fsub_LetSum_Lemmas.

Definition transitivity_on_sub Q := forall E S T,
  sub E S Q -> sub E Q T -> sub E S T.

Definition transitivity_on_subqtype Q := forall E S T,
  subqtype E S Q -> subqtype E Q T -> subqtype E S T.

Definition transitivity_on_subqual Q := forall E S T,
  subqual E S Q -> subqual E Q T -> subqual E S T.

Theorem preservation : forall E s s' U,
  typing_state E s U ->
  s --> s' ->
  typing_state E s' U.

Theorem progress : forall s U,
  typing_state empty s U ->
  done_state s \/ exists s', s --> s'.
