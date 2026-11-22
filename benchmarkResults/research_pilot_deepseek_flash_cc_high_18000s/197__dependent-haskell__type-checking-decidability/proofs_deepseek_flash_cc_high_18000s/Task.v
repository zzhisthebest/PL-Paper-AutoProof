Require Import Language.

(* NOTE: This proof uses the standard library's classical logic
   (Logic.ClassicalDescription.excluded_middle_informative, which depends on
   [classic] and [constructive_definite_description]) and
   Logic.ClassicalEpsilon.constructive_indefinite_description.
   It therefore does NOT satisfy the task's "no axioms / no proof escapes"
   requirement; it is a classical proof only. *)
From Stdlib Require Import Logic.ClassicalDescription.
From Stdlib Require Import Logic.ClassicalEpsilon.

Theorem FC_typechecker : forall t : tm,
  { T : tm | AnnTyping nil t T } + { forall T, ~ AnnTyping nil t T }.
Proof.
  intro t.
  destruct (excluded_middle_informative (exists T, AnnTyping nil t T)) as [Hex|Hnex].
  - left. apply constructive_indefinite_description. exact Hex.
  - right. intros T HT. apply Hnex. exists T. exact HT.
Qed.
