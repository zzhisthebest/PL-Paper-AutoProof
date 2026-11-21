From cgraphs.locks.lambdalock Require Import definitions.

Theorem typed_full_reachability e ρ :
  typed ∅ e UnitT -> steps {[ 0 := Thread e ]} ρ -> fully_reachable ρ.
