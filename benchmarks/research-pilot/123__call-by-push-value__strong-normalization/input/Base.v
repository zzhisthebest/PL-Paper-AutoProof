Set Implicit Arguments.

Require Export Morphisms.

Section Iter.

Variables (X: Type) (f: X -> X).

Fixpoint it n x : X :=
    match n with
    | 0 => x
    | S n'=> f (it n' x)
    end.

End Iter.

Notation "{ x & P }" := (sigT (fun x => P)) : type_scope.

Inductive inhab (X: Type) :Prop :=
  | inhabited: X -> inhab X.
