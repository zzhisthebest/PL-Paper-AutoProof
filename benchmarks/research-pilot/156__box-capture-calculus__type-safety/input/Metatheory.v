Require Export Atom.

Require Export Nat.

Require Export Bool.

Require Export Environment.

Declare Scope metatheory_scope.

Declare Scope set_scope.

Inductive var : Set :=
  | var_f : atom -> var
  | var_b : nat -> var.

Coercion var_f : atom >-> var.

Coercion var_b : nat >-> var.

Notation "x == y" :=
  (eq_atom_dec x y) (at level 67) : metatheory_scope.

Notation "i === j" :=
  (Peano_dec.eq_nat_dec i j) (at level 67) : metatheory_scope.

Notation "E `union` F" :=
  (AtomSet.F.union E F) (at level 69, right associativity, only parsing, format "E  `union`  '/' F")
  : set_scope.

Notation "x `in` E" :=
  (AtomSet.F.In x E) (at level 69) : set_scope.

Notation "x `notin` E" :=
  (~ AtomSet.F.In x E) (at level 69) : set_scope.

Notation "E `subset` F" :=
  (AtomSet.F.Subset E F)
  (at level 68)
  : set_scope.

Notation "E `remove` x" :=
  (AtomSet.F.remove x E)
  (at level 68)
  : set_scope.

Notation singleton := (AtomSet.F.singleton) (only parsing).

Definition disjoint (xs : atoms) (ys: atoms) : Prop :=
  AtomSet.F.Empty (AtomSet.F.inter xs ys).

Notation "a `disjoint` b" := (disjoint a b) (at level 1, only parsing)  : metatheory_scope.

Notation "E `u`A F" :=
  (AtomSet.F.union E F) (at level 69, right associativity, format "E  `u`A  '/' F") : set_scope.

Notation "E `c`A F" := (AtomSet.F.Subset E F) (at level 68) : set_scope.

Notation "E `\`A x" := (AtomSet.F.remove x E) (at level 69, right associativity) : set_scope.

Notation "x `in`A F" := (AtomSet.F.In x F) (at level 69) : set_scope.

Notation "x `~in`A F" := (~ AtomSet.F.In x F) (at level 69) : set_scope.

Notation "E `u`N F" :=
  (NatSet.F.union E F) (at level 69, right associativity, format "E  `u`N  '/' F") : set_scope.

Notation "E `c`N F" := (NatSet.F.Subset E F) (at level 68) : set_scope.

Notation "E `\`N x" := (NatSet.F.remove x E) (at level 69, right associativity) : set_scope.

Notation "x `in`N F" := (NatSet.F.In x F) (at level 69) : set_scope.

Notation "x `~in`N F" := (~ NatSet.F.In x F) (at level 69) : set_scope.

Notation "{ x }A" := (AtomSet.F.singleton x) (at level 0, format "{ x }A") : set_scope.

Notation "{}A" := (AtomSet.F.empty) (at level 0) : set_scope.

Notation "{ x }N" := (NatSet.F.singleton x) (at level 0, format "{ x }N") : set_scope.

Notation "{}N" := (NatSet.F.empty) (at level 0) : set_scope.

Open Scope metatheory_scope.

Open Scope set_scope.
