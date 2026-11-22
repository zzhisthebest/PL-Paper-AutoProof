Require Export compat.

Require Import Bool List Lia PeanoNat Classical.

Section PairOperations.

End PairOperations.

Section ListOperations.

Fixpoint disjoint {A} (l1 l2 : list A) : Prop :=
    match l1 with
    | nil => True
    | x::t1 => ((In x l2) -> False) /\ disjoint t1 l2
    end.

Inductive  disjoint_2 {A}: list A -> list A -> Prop :=
  | dis_nil : forall l : list A, disjoint_2 nil l
  | dis_cons : forall (x:A) (l1 l2 : list A),
      (~ In x l2 /\ disjoint_2 l1 l2) -> disjoint_2 (x::l1) l2.

End  ListOperations.
