From diris.lambdabar Require Import definitions.

Theorem typed_global_progress e ρ :
  typed ∅ e UnitT -> steps {[ 0 := Thread e ]} ρ -> global_progress ρ.
