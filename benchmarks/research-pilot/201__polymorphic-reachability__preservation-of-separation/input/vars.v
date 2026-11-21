Definition id := nat.

Definition loc := nat.

Inductive var : Type :=
| varF : id -> var
| varB : id -> var
.

Notation "# i" := (varB i) (at level 0, right associativity).

Notation "$ i" := (varF i) (at level 0, right associativity).
