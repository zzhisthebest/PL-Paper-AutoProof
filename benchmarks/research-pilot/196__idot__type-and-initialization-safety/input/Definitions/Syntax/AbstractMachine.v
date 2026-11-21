Set Implicit Arguments.

Require Import LibExtra Vars Terms Items.

Notation heap := (env item).

Inductive frame : Set :=
  | frame_let : trm -> frame
  | frame_ret : var -> frame.

Notation stack := (list frame).

Notation config := (trm * stack * heap)%type.

Notation "t ; Fs ; Sigma"
  := (t, Fs, Sigma) (at level 39, Fs, Sigma at level 38) : syntax_scope.
