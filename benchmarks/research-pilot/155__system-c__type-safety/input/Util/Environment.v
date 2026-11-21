Require Export List.

Require Import Atom.

Import AtomSet.F.

Notation "[ x ]" := (cons x nil).

Set Implicit Arguments.

Section Definitions.

Variables A B : Type.

Fixpoint dom (E : list (atom * A)) : atoms :=
  match E with
  | nil => empty
  | (x, _) :: E' => union (singleton x) (dom E')
  end.

Fixpoint map (f : A -> B) (E : list (atom * A)) : list (atom * B) :=
  match E with
  | nil => nil
  | (x, V) :: E' => (x, f V) :: map f E'
  end.

Fixpoint get (x : atom) (E : list (atom * A)) : option A :=
  match E with
  | nil => None
  | (y,a) :: E' => if eq_atom_dec x y then Some a else get x E'
  end.

End Definitions.

Unset Implicit Arguments.

Set Implicit Arguments.

Section Relations.

Variable A : Type.

Inductive ok : list (atom * A) -> Prop :=
  | ok_nil :
      ok nil
  | ok_cons : forall (E : list (atom * A)) (x : atom) (a : A),
      ok E -> ~ In x (dom E) -> ok ((x, a) :: E).

Definition binds x b (E : list (atom * A)) :=
  get x E = Some b.

End Relations.

Unset Implicit Arguments.

Section OpProperties.

Variable A B : Type.

Implicit Types E F : list (atom * A).

Implicit Types a b : A.

End OpProperties.

Definition singleton_list (A : Type) (x : atom * A) := x :: nil.

Section OkProperties.

Variable A B : Type.

Implicit Types E F : list (atom * A).

Implicit Types a b : A.

End OkProperties.

Section BindsProperties.

Variable A B : Type.

Implicit Types E F : list (atom * A).

Implicit Types a b : A.

End BindsProperties.

Section AdditionalBindsProperties.

Variable A B : Type.

Implicit Types E F : list (atom * A).

Implicit Types a b : A.

End AdditionalBindsProperties.
