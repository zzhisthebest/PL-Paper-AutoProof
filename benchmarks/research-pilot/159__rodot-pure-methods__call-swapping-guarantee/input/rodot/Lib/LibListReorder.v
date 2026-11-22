Set Implicit Arguments.

Require Import Coq.Bool.Bool.

Require Export Coq.Program.Basics.

From TLC Require Import LibVar LibLN LibFset.

Require Import LibSetExtra LibListExtra LibNatExtra.

Inductive list_reorder A: (list A) -> (list nat) -> (list A) -> Prop :=
| list_reorder_nil xs:
    list_reorder xs nil nil
| list_reorder_cons xs y ys n ns:
    list_reorder xs ns ys ->
    LibList.Nth n xs y ->
    list_reorder xs (n::ns) (y::ys).

Definition list_cover_interval (ns: list nat) (n: nat) :=
  forall m, m < n -> LibList.mem m ns.

Inductive list_reordering: (list var) -> (list var) -> (list var) -> (list var) -> (list var) -> (list var) -> Prop :=
  list_reordering_mk ns1 ns2 xs0 ys0 xs1 ys1 xs2 ys2:
    list_reorder xs0 ns1 xs1 ->
    list_reorder ys0 ns1 ys1 ->
    list_reorder xs0 ns2 xs2 ->
    list_reorder ys0 ns2 ys2 ->
    LibList.noduplicates ns1 ->
    LibList.noduplicates ns2 ->
    list_reordering xs0 ys0 xs1 ys1 xs2 ys2.
