Require Import List.

From Stdlib Require Import PeanoNat.

Require Import OrderedTypeEx.

Require Import OrderedType.

Require Import FiniteSets.

Require Import FSetFacts.

Module NatSetImpl.

Module OT := Nat_as_OT.

Module Facts := OrderedTypeFacts OT.

Definition eq_nat_dec : forall x y : nat, {x = y} + {x <> y} :=
    Facts.eq_dec.

End NatSetImpl.

Module NatSet :=
  FiniteSets.Make NatSetImpl.OT.

Notation nats := NatSet.F.t.

Notation "{}N" :=
  NatSet.F.empty : metatheory_scope.

Module NatSetFacts  := FSetFacts.Facts NatSet.F.

Module NatSetProperties := FSetProperties.Properties NatSet.F.
