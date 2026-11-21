Require Import List.

From Stdlib Require Import PeanoNat.

Require Import OrderedType.

Require Import OrderedTypeEx.

Open Scope nat_scope.

Require Import FiniteSets.

Module AtomImpl.

Definition atom := nat.

Module Atom_as_OT := Nat_as_OT.

Module Facts := OrderedTypeFacts Atom_as_OT.

Definition eq_atom_dec : forall x y : atom, {x = y} + {x <> y} :=
    Facts.eq_dec.

End AtomImpl.

Export AtomImpl.

Module AtomSet :=
  FiniteSets.Make Atom_as_OT.

Notation atoms := AtomSet.F.t.

Import AtomSet.F.

Module AtomSetFacts  := FSetFacts.Facts   AtomSet.F.

Module AtomSetProperties := FSetProperties.Properties AtomSet.F.

Definition disjoint (xs : atoms) (ys: atoms) : Prop :=
  AtomSet.F.Empty (AtomSet.F.inter xs ys).

Notation "a `disjoint` b" := (disjoint a b) (at level 1)  : metatheory_scope.
