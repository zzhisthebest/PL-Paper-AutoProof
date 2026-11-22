(** A library of relation operators defining sequences of transitions
  and useful properties about them. Originally by Xavier Leroy, with
  some improvements and additions by François Pottier, and more
  additions by the authors of the artifact. *)

Set Implicit Arguments.

Section SEQUENCES.

Variable A: Type.

Implicit Types R S : A -> A -> Prop.
Implicit Types P   : A -> Prop.

(** Zero, one or several transitions: reflexive, transitive closure of [R]. *)


Inductive star R : A -> A -> Prop :=
| star_refl:
  forall a,
  star R a a
| star_step:
  forall a b c,
  R a b -> star R b c -> star R a c.

End SEQUENCES.
