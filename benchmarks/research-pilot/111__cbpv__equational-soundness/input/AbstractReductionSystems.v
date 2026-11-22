Set Implicit Arguments.

Require Import Morphisms FinFun Base.

Notation "R <<= S" := (forall x y, R x y -> S x y) (at level 70).

Notation "R === S" := (R <<= S /\ S <<= R) (at level 70).

Section ClosureRelations.

Variables (X: Type) (R: X -> X -> Prop).

Implicit Types x y z : X.

Definition functional := forall x y z, R x y -> R x z -> y = z.

Inductive star : X -> X -> Prop :=
  | starRefl x     : star x x
  | starStep x x' y : R x x' -> star x' y -> star x y.

Inductive plus : X -> X -> Prop :=
  | plusSingle x y: R x y -> plus x y
  | plusStep x x' y: R x x' -> plus x' y -> plus x y.

Inductive counted : nat -> X -> X -> Prop :=
  | countedRefl x: counted 0 x x
  | countedStep x x' y n: R x x' -> counted n x' y -> counted (S n) x y.

Inductive sym: X -> X -> Prop :=
  | symId x y: R x y -> sym x y
  | symInv x y: R y x -> sym x y.

End ClosureRelations.

Definition equiv X (R: X -> X -> Prop) := star (sym R).

Section Properties.

Variable X: Type.

Implicit Types (x y z : X) (R S : X -> X -> Prop).

End Properties.

Section StrongNormalisation.

Variables (X A: Type).

Variables (R: X -> X -> Prop) (S: A -> A -> Prop).

Definition Normal x := forall y, ~ R x y.

Definition evaluates s t := star R s t /\ Normal t.

Inductive SN {X} (R: X -> X -> Prop) : X -> Prop :=
  | SNC x : (forall y, R x y -> SN R y) -> SN R x.

Definition morphism  (f: X -> A) := forall x y, R x  y -> S (f x) (f y).

End StrongNormalisation.

Section Confluence.

Variable X: Type.

Implicit Types (x y z : X) (R S : X -> X -> Prop).

Definition joinable R x y := exists2 z, R x z & R y z.

Definition diamond R := forall x y z, R x y -> R x z -> joinable R y z.

Definition confluent R := diamond (star R).

Definition semi_confluent R :=
    forall x y z, R x y -> star R x z -> joinable (star R) y z.

End Confluence.

Inductive starL {X: Type} (R: X -> X -> Prop) (x : X):  X -> Prop :=
| starReflL : starL R x x
| starStepL  y y':  starL R x y -> R y y' -> starL R x y'.
