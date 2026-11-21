From Stdlib Require Import Utf8 List.

From AccInSProp Require Import core unscoped AST.

From Stdlib Require Import Setoid Morphisms Relation_Definitions.

Import ListNotations.

Notation "a ⋅ x" :=
  (ren_term a x) (at level 20, right associativity) : subst_scope.

Notation "t <[ s ]" :=
  (subst_term s t) (at level 10, right associativity) : subst_scope.

Notation "↑" := (shift) : subst_scope.

Notation "s '..'" := (scons s ids) (at level 1, format "s ..") : subst_scope.
