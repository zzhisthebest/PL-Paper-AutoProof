From Coq.ssr Require Import ssreflect.

From stdpp Require Import base prelude list gmap.

Class Lattice (A : Type) := {
    lat_equiv :> Equiv A;
    lat_equiv_equiv :> Equivalence lat_equiv;
    lat_equiv_dec :> RelDecision lat_equiv;
    join : A → A → A;
    join_proper :> Proper ((≡) ==> (≡) ==> (≡)) join;
    join_commutative :> Comm (≡) join;
    join_associative :> Assoc (≡) join;
    join_idempotent  :> IdemP (≡) join;

    bot : A;
    bot_left_id  :> LeftId (≡) bot join;
    bot_right_id :> RightId (≡) bot join;

    top : A;
    top_left_absorb :> LeftAbsorb (≡) top join;
    top_right_absorb :> RightAbsorb (≡) top join;
}.

#[global] Existing Instance lat_equiv.

Class SecurityLattice (label : Type) := {
   lattice :> Lattice label;
   ζ : label;
}.

#[global] Existing Instance lattice.

Infix "⊔" := join (at level 50) : stdpp_scope.

Notation "⊥" := bot : stdpp_scope.

Notation "⊤" := top : stdpp_scope.

Section Order.

Context `{lattice : Lattice label}.

Implicit Types a b : label.

Definition order a b := a ⊔ b ≡ b.

End Order.

Notation "a ⊑ b" := (order a b) (at level 70) : stdpp_scope.

Notation "a ⋢ b" := (¬ (order a b)) (at level 70) : stdpp_scope.

Section Lemmas.

Context `{lattice : Lattice label}.

Implicit Types ℓ : label.

End Lemmas.
