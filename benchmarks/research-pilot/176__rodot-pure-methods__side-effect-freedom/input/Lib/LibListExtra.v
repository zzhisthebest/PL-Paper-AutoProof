Set Implicit Arguments.

Require Import Coq.Bool.Bool.

Require Export Coq.Program.Basics.

From TLC Require Import LibVar LibLN LibFset.

Require Import LibSetExtra LibNatExtra.

Notation list_removeat n xs := (((LibList.take n xs) ++ (LibList.drop (S n) xs))%list) (only parsing).

Notation list_insertat n xs x := (((LibList.take n xs) ++ (x::(LibList.drop n xs)))%list) (only parsing).
