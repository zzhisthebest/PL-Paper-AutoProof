Require Import Program.Equality.

Require Import Metalib.Metatheory.

Require Import Language.

Inductive algo_cost : typ -> typ -> Prop :=
  | cint : algo_cost int int
  | candl : forall A B C, algo_cost A C -> algo_cost (and A B) C
  | candr : forall A B C, algo_cost B C -> algo_cost (and A B) C
  | crandl : forall A B C, algo_cost A B -> algo_cost A (and B C)
  | crandr : forall A B C, algo_cost A C -> algo_cost A (and B C)
  | carr : forall A B C D, algo_cost B D -> algo_cost (arr A B) (arr C D)
  | crcd : forall A B l, algo_cost A B -> algo_cost (rcd l A) (rcd l B).

Definition algo_dis A B := ~ (algo_cost A B).
