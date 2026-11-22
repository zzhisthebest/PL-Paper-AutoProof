Require Import Metalib.Metatheory.

Class CanOpen (A : Type) :=
  {
    open_rec (k : nat) (u : var) (ins : A) : A
  }.

Notation open := (open_rec 0).

Class CanClose (A : Type) :=
  {
    close_rec (k : nat) (u : var) (ins : A) : A
  }.

Notation close := (close_rec 0).

Class HasFv (A : Type) :=
  {
    fv (ins : A) : atoms
  }.

Class CanSubst (A : Type) :=
  {
    substi (z u : var) (ins : A) : A
  }.

Class LC (A : Type) :=
  {
    lc_at (n : nat) (ins : A) : Prop
  }.

Notation lc := (lc_at 0).
