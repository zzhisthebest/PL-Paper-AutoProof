From Stdlib Require Import Utf8.

Inductive inc (V : Set) : Set :=
| VZ : inc V
| VS : V → inc V
.

Arguments VZ {V}.
Arguments VS [V] _.

Definition inc_map {V W : Set} (f : V → W) (x : inc V) : inc W :=
  match x with
  | VZ   => VZ
  | VS y => VS (f y)
  end.

Inductive empty : Set :=
.

Definition of_empty {V : Set} : empty → V :=
  λ x, match x with end.
