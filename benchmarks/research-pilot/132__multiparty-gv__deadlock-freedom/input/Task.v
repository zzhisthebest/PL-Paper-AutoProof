From cgraphs.multiparty Require Import definitions.

From cgraphs.multiparty Require Import langdef.

Theorem deadlock_freedom_and_full_reachability e es h :
  typed ∅ e UnitT -> steps [e] ∅ es h ->
  deadlock_free es h ∧ fully_reachable es h.
