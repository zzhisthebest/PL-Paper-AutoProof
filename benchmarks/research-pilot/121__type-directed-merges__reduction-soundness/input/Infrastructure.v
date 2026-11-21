Require Import Metalib.Metatheory.

Require Import syntax_ott rules_inf.

Require Import List.

Import ListNotations.

Require Import Coq.Strings.String.

Definition relation (X:Type) := X -> X -> Prop.

Section Star.

Variable A : Type.

Variable R : relation A.

Inductive star: relation A:=
  | star_refl: forall a,
      star a a
  | star_step: forall a b c,
      R a b -> star b c -> star a c.

Definition irred a : Prop := forall b, ~(R a b).

End Star.

Definition mul_dstep := star dexp DunfieldStep.

Notation "e ->>* e'" := ((star dexp DunfieldStep) e e') (at level 68).

Notation "[ z ~> u ] e" := (subst_exp u z e) (at level 0).

Notation "t ^^ u"       := (open_exp_wrt_exp t u) (at level 67).

Notation "e ^ x"        := (open_exp_wrt_exp e (e_var_f x)).

Notation "G |= t ~: T" := (Etyping G t T) (at level 69).

Notation "v ~-> A v'" := (TypedReduce v A v') (at level 68).

Notation "R 'star'" := (star exp R) (at level 69).

Notation "t ->* t'" := (step star t t') (at level 68).

Notation "x '#' E" := (x \notin (dom E)) (at level 67) : env_scope.

Definition env := list (atom * exp).

From Stdlib Require Import Lia.
