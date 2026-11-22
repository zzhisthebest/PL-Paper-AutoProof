From Stdlib Require Export Strings.String.
From stdpp Require Export gmap finite.

(* From the artifact's theories/cgraphs/util.v. *)
Definition fin_list {A} n (f : fin n -> A) : list A := vec_to_list (fun_to_vec f).

Definition fin_gset `{Countable A} n (f : fin n -> A) : gset A
  := list_to_set (fin_list n f).

Definition big_union `{Countable A} : gset (gset A) -> gset A := set_fold (∪) ∅.

Definition fin_union `{Countable A} n (f : fin n -> gset A) : gset A :=
  big_union (fin_gset n f).
