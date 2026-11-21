From stdpp Require Import gmap.

From stdpp Require Export finite.

Fixpoint insert2 {T} (i : nat) (x : T) (xs : list T) : list T :=
  match i,xs with
  | 0,xs => x :: xs
  | S i',y :: xs => y :: insert2 i' x xs
  | S i',[] => [x]
  end.

Section disjoint.

Context `{Countable K}.

Context {V : Type}.

Definition disjoint (xs : list (gmap K V)) :=
    forall i j h1 h2,
        xs !! i = Some h1 -> xs !! j = Some h2 -> i ≠ j -> h1 ##ₘ h2.

End disjoint.

Definition fin_list {A} n (f : fin n -> A) : list A := vec_to_list (fun_to_vec f).

Definition fin_gset `{Countable A} n (f : fin n -> A) : gset A
  := list_to_set (fin_list n f).

Definition all_fin n := fin_gset n id.

Definition big_union `{Countable A} : gset (gset A) -> gset A := set_fold (∪) ∅.

Definition fin_union `{Countable A} n (f : fin n -> gset A) : gset A :=
  big_union (fin_gset n f).

Fixpoint list_to_mapi' {A} (xs : list A) (n : nat) : gmap nat A :=
  match xs with
  | [] => ∅
  | x::r => <[ n := x ]> (list_to_mapi' r (S n))
  end.

Definition list_to_mapi {A} (xs : list A) := list_to_mapi' xs 0.

Definition fin_gmap {T} n : (fin n -> T) -> gmap nat T := list_to_mapi ∘ fin_list n.
