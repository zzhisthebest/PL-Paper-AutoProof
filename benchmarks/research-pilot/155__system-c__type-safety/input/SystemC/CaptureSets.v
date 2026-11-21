Require Import Metatheory.

Require Import OrderedTypeEx.

Require Import OrderedType.

Require Import FSetFacts.

Require Import Atom.

Require Export Label.

Require Export Nat.

Inductive cap : Type :=
  | cset_set : atoms -> nats -> labels -> cap.

Definition empty_cset := cset_set {} {}N {}L.

Notation "{}C" := empty_cset : metatheory_scope.

Definition cset_fvar (a : atom) :=
  (cset_set (AtomSet.F.singleton a) NatSet.F.empty LabelSet.F.empty).

Definition cset_bvar (k : nat) :=
  (cset_set AtomSet.F.empty (NatSet.F.singleton k) LabelSet.F.empty).

Definition cset_lvar (a : label) :=
  (cset_set AtomSet.F.empty NatSet.F.empty (LabelSet.F.singleton a)).

Definition from_labels (ls : labels) :=
  (cset_set AtomSet.F.empty NatSet.F.empty ls).

Definition cset_fvars (c : cap) : atoms :=
  match c with
  | cset_set A N R => A
  end.

Definition cset_bvars (c : cap) : nats :=
  match c with
  | cset_set A N R => N
  end.

Definition cset_lvars (c : cap) : labels :=
  match c with
  | cset_set A N R => R
  end.

Definition cset_references_bvar (k : nat) (c : cap) :=
  NatSet.F.In k (cset_bvars c).

Definition cset_references_fvar (a : atom) (c : cap) :=
  AtomSet.F.In a (cset_fvars c).

Definition cset_references_lvar (a : label) (c : cap) :=
  LabelSet.F.In a (cset_lvars c).

Definition cset_references_bvar_dec (k : nat) (c : cap) :=
  NatSet.F.mem k (cset_bvars c).

Definition cset_references_fvar_dec (a : atom) (c : cap) :=
  AtomSet.F.mem a (cset_fvars c).

Definition cset_references_lvar_dec (a : label) (c : cap) :=
  LabelSet.F.mem a (cset_lvars c).

Definition cset_remove_bvar (k : nat) (c : cap) : cap :=
  cset_set (cset_fvars c) (NatSet.F.remove k (cset_bvars c)) (cset_lvars c).

Definition cset_remove_fvar (a : atom) (c : cap) : cap :=
  cset_set (AtomSet.F.remove a (cset_fvars c)) (cset_bvars c) (cset_lvars c).

Definition cset_union (c1 c2 : cap) : cap :=
  cset_set
    (AtomSet.F.union (cset_fvars c1) (cset_fvars c2))
    (NatSet.F.union (cset_bvars c1) (cset_bvars c2))
    (LabelSet.F.union (cset_lvars c1) (cset_lvars c2)).

Definition cset_subset_dec (C D : cap) :=
  AtomSet.F.subset (cset_fvars C) (cset_fvars D)
    && NatSet.F.subset (cset_bvars C) (cset_bvars D)
    && LabelSet.F.subset (cset_lvars C) (cset_lvars D).

Definition cset_empty (c : cap) : Prop :=
  AtomSet.F.Empty (cset_fvars c) /\ NatSet.F.Empty (cset_bvars c) /\ LabelSet.F.Empty (cset_lvars c).

Definition cset_subset_prop (c : cap) (d : cap) : Prop :=
  AtomSet.F.Subset (cset_fvars c) (cset_fvars d)
    /\ NatSet.F.Subset (cset_bvars c) (cset_bvars d)
    /\ LabelSet.F.Subset (cset_lvars c) (cset_lvars d).

Section Props.

Variable x y a f : atom.

Variable l m : label.

Variable A A1 A2 : atoms.

Variable R R1 R2 : labels.

Variable k n : nat.

Variable N N1 N2 : nats.

Variable C D C1 C2 C3 : cap.

End Props.

Definition capt (c : cap) : Prop := NatSet.F.Empty (cset_bvars c).

Definition open_cset (k : nat) (c : cap) (d : cap) : cap :=
  if cset_references_bvar_dec k d then
    cset_union c (cset_remove_bvar k d)
  else
    d.

Definition subst_cset (a : atom) (c : cap) (d: cap) : cap :=
  if cset_references_fvar_dec a d then
    cset_union c (cset_remove_fvar a d)
  else
    d.
