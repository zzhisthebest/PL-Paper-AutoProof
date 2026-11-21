Require Export Atom.

Require Export Environment.

Declare Scope metatheory_scope.

Declare Scope set_scope.

Notation "x == y" :=
      (eq_atom_dec x y) (at level 67) : metatheory_scope.

Notation "i === j" :=
      (Peano_dec.eq_nat_dec i j) (at level 67) : metatheory_scope.

Notation "E `union` F" :=
      (AtomSet.F.union E F)
      (at level 69, right associativity, format "E  `union`  '/' F")
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

Notation "{}" :=
      (AtomSet.F.empty) : metatheory_scope.

Notation singleton := (AtomSet.F.singleton).

Open Scope metatheory_scope.

Open Scope set_scope.
