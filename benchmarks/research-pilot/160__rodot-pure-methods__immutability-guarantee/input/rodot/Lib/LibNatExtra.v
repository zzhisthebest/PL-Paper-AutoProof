Set Implicit Arguments.

Require Import Coq.Bool.Bool.

Require Export Coq.Program.Basics.

From TLC Require Import LibTactics.

Definition decrease_after n m := if (Compare_dec.le_lt_dec n m ) then (Nat.pred m) else m.

Definition increase_after n m := if (Compare_dec.le_lt_dec n m ) then (S m) else m.
