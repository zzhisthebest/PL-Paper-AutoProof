Require Import StdSetup.

Inductive avar : Set :=
| avar_b : nat -> avar
| avar_f : var -> avar.

Definition fv_values {T : Type} (f : T -> atoms)
           (l : list (atom * T)) : atoms :=
  fold_right (fun (b : (atom * T)) a =>
                a \u let (_, t) := b in f t) {} l.
