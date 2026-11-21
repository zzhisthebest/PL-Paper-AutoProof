Set Implicit Arguments.

Require Import Coq.Program.Equality List String.

Require Import Sequences.

Require Import Definitions Binding.

Notation repl_repeat_typ p q := (star (repl_typ p q)).

Notation repl_repeat_dec p q := (star (repl_dec p q)).
