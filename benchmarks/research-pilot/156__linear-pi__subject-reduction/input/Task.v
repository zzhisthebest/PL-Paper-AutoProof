Require Import pi_syntax type_system type_system_rules semantics.

Theorem sr :
  forall g p a g' p' nd_pf pf pf',
    sl_pos p ->
    typeCheck g pf p ->
    lts g p a g' p' nd_pf ->
    typeCheck g' pf' p'.
