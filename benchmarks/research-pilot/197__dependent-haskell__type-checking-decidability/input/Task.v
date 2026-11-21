Require Import Language.

Theorem FC_typechecker : forall t : tm,
  { T : tm | AnnTyping nil t T } + { forall T, ~ AnnTyping nil t T }.
