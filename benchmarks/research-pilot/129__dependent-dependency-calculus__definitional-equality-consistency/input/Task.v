Require Import Qual.geq.
Require Import Qual.defeq.

Set Implicit Arguments.

Theorem DefEq_Consistent : forall S D A B, DefEq S D A B -> Consistent A B.
