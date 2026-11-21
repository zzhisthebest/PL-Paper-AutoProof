From Stdlib Require Import Bool.

From Coq Require Import ssreflect.

Declare Scope lattice_scope.

Local Open Scope lattice_scope.

Module Type Lattice.

Parameter T : Set.

Parameter meet : T -> T -> T.

Parameter join : T -> T -> T.

Parameter T_eqb : T -> T -> bool.

Infix "∪" := join (at level 65) : lattice_scope.

Infix "∩" := meet (at level 60) : lattice_scope.

Notation "a ⊆ b" := (a ∩ b = a) (at level 70, no associativity) : lattice_scope.

Parameter meet_commutative : forall a b, a ∩ b = b ∩ a.

Parameter meet_associative : forall a b c, (a ∩ b) ∩ c = a ∩ (b ∩ c).

Parameter meet_absorptive : forall a b, a ∩ (a ∪ b) = a.

Parameter meet_idempotent : forall a, a ∩ a = a.

Parameter join_commutative : forall a b, a ∪ b = b ∪ a.

Parameter join_associative: forall a b c, (a ∪ b) ∪ c = a ∪ (b ∪ c).

Parameter join_absorptive : forall a b, a ∪ (a ∩ b) = a.

Parameter join_idempotent : forall a, a ∪ a = a.

Parameter T_eqdec : forall a b, Bool.reflect (a = b) (T_eqb a b).

End Lattice.
