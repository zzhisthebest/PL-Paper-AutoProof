Require Import Metatheory.

Require Import OrderedTypeEx.

Require Import OrderedType.

Require Import FSetFacts.

Require Import Atom.

Require Import Nat.

Require Export Bool.

Inductive cap : Type :=
  | cset_set : atoms -> nats -> bool -> cap.

Declare Scope cset_shorthand.

Notation "`cset_fvar` a" := (cset_set {a}A {}N false)
                              (at level 10, a at level 9) : cset_shorthand.

Notation "`cset_bvar` k" := (cset_set {}A {k}N false)
                              (at level 10, k at level 9) : cset_shorthand.

Notation "{}" := (cset_set {}A {}N false) : cset_shorthand.

Notation "{*}" := (cset_set {}A {}N true) : cset_shorthand.

Notation "`cset_fvars` C" := (match C with cset_set xs _ _ => xs end)
                                (at level 10, C at level 9) : cset_shorthand.

Notation "`cset_bvars` C" := (match C with cset_set _ ks _ => ks end)
                                (at level 10, C at level 9) : cset_shorthand.

Notation "`cset_uvar` C" := (match C with cset_set _ _ u => u end)
                                (at level 10, C at level 9) : cset_shorthand.

Open Scope cset_shorthand.

Definition cset_union (c1 c2 : cap) : cap :=
  cset_set
    (AtomSet.F.union (`cset_fvars` c1) (`cset_fvars` c2))
    (NatSet.F.union (`cset_bvars` c1) (`cset_bvars` c2))
    ((`cset_uvar` c1) || (`cset_uvar` c2)).

Definition cset_subset_dec (C D : cap) :=
  AtomSet.F.subset (`cset_fvars` C) (`cset_fvars` D)
    && NatSet.F.subset (`cset_bvars` C) (`cset_bvars` D)
    && (implb (`cset_uvar` C) (`cset_uvar` D)).

Notation "C `u` D" := (cset_union C D) (at level 69) : cset_shorthand.

Notation "C A`\` x" := (cset_set ((`cset_fvars` C) `\`A x) (`cset_bvars` C) (`cset_uvar` C))
                         (at level 69) : cset_shorthand.

Notation "x A`in` C" := (AtomSet.F.In x (`cset_fvars` C))
                          (at level 69) : cset_shorthand.

Notation "x A`mem` C" := (AtomSet.F.mem x (`cset_fvars` C)) (at level 69) : cset_shorthand.

Notation "C N`\` k" := (cset_set ((`cset_fvars` C) ) ((`cset_bvars` C) `\`N k) (`cset_uvar` C))
                         (at level 69) : cset_shorthand.

Notation "k N`in` C" := (NatSet.F.In k (`cset_bvars` C))
                          (at level 69) : cset_shorthand.

Notation "k N`mem` C" := (NatSet.F.mem k (`cset_bvars` C))
                           (at level 69) : cset_shorthand.

Notation "`* mem` C" := (`cset_uvar` C)
                           (at level 10, only parsing) : cset_shorthand.

Notation "`* in` C" := (`cset_uvar` C = true)
                           (at level 10) : cset_shorthand.

Notation "`cset_references_bvar` k c" :=
  (k N`in` c)
    (at level 10, k at level 9, c at level 9, only parsing) : cset_shorthand.

Notation "`cset_references_bvar_dec` k c" :=
  (k N`mem` c)
    (at level 10, k at level 9, c at level 9, only parsing) : cset_shorthand.

Notation "`cset_remove_bvar` k c" :=
  (c N`\` k)
    (at level 10, k at level 9, c at level 9, only parsing) : cset_shorthand.

Notation "`cset_references_fvar` a c" :=
  (a A`in` c)
    (at level 10, a at level 9, c at level 9, only parsing) : cset_shorthand.

Notation "`cset_references_fvar_dec` a c" :=
  (a A`mem` c)
    (at level 10, a at level 9, c at level 9, only parsing) : cset_shorthand.

Notation "`cset_remove_fvar` a c" :=
  (c A`\` a)
    (at level 10, a at level 9, c at level 9, only parsing) : cset_shorthand.

Notation "`cset_references_univ_dec` c" :=
  (`cset_uvar` c)
    (at level 10, c at level 9, only parsing) : cset_shorthand.

Notation "`cset_references_univ` c" :=
  (`* in` c)
    (at level 10, only parsing) : cset_shorthand.

Declare Scope experimental_set_scope.

Notation "{ x 'as' A}" := (`cset_fvar` x) : experimental_set_scope.

Notation "{ x 'as' N}" := (`cset_bvar` x) : experimental_set_scope.

Definition cset_empty (c : cap) : Prop :=
  AtomSet.F.Empty (`cset_fvars` c) /\ NatSet.F.Empty (`cset_bvars` c) /\
    ((`cset_uvar` c) = false).

Definition cset_subset_prop (c : cap) (d : cap) : Prop :=
  AtomSet.F.Subset (`cset_fvars` c) (`cset_fvars` d)
    /\ NatSet.F.Subset (`cset_bvars` c) (`cset_bvars` d)
    /\  (Bool.le (`cset_uvar` c) (`cset_uvar` d)).

Section Props.

Variable x y a f : atom.

Variable l m R : bool.

Variable A A1 A2 : atoms.

Variable k n : nat.

Variable N N1 N2 : nats.

Variable C D C1 C2 C3 : cap.

End Props.

Definition capt (c : cap) : Prop := NatSet.F.Empty (`cset_bvars` c).

Definition open_cset (k : nat) (c : cap) (d : cap) : cap :=
  if `cset_references_bvar_dec` k d then
    cset_union c (`cset_remove_bvar` k d)
  else
    d.

Definition subst_cset (a : atom) (c : cap) (d: cap) : cap :=
  if `cset_references_fvar_dec` a d then
    cset_union c (`cset_remove_fvar` a d)
  else
    d.
