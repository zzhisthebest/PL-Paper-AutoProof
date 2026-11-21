Require Import List.

From Stdlib Require Import PeanoNat.

Require Import OrderedType.

Require Import OrderedTypeEx.

Open Scope nat_scope.

Require Import FiniteSets.

Module LabelImpl.

Definition label := nat.

Module Label_as_OT := Nat_as_OT.

Module Facts := OrderedTypeFacts Label_as_OT.

Definition eq_label_dec : forall x y : label, {x = y} + {x <> y} :=
    Facts.eq_dec.

End LabelImpl.

Export LabelImpl.

Module LabelSet :=
  FiniteSets.Make Label_as_OT.

Notation labels := LabelSet.F.t.

Notation "{}L" :=
  LabelSet.F.empty : metatheory_scope.

Import LabelSet.F.

Module LabelSetFacts  := FSetFacts.Facts   LabelSet.F.

Module LabelSetProperties := FSetProperties.Properties LabelSet.F.

Notation "x =l= y" := (eq_label_dec x y) (at level 67) : metatheory_scope.

Definition labels_disjoint (xs : labels) (ys: labels) : Prop :=
  LabelSet.F.Empty (LabelSet.F.inter xs ys).
