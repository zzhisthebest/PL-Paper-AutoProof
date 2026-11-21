Require Import Utf8.

Require Import Eqdep.

Require Import Eqdep_dec.

Inductive kind := KTyp | KArr (κ₁ κ₂ : kind).

Notation "⋆" := KTyp.

Notation "κ₁ ⇒ κ₂" := (KArr κ₁ κ₂) (at level 45, right associativity).

Module kindEqDec <: DecidableType.

Definition U := kind.

Definition eq_dec : forall x y : U, {x = y} + {x <> y} := ltac:(decide equality).
End kindEqDec.

Module Export DED_kind := DecidableEqDep (kindEqDec).

Inductive tctor : kind → Type :=
| tc_unit : tctor ⋆
| tc_void : tctor ⋆
| tc_arr  : tctor (⋆ ⇒ ⋆ ⇒ ⋆)
| tc_sum  : tctor (⋆ ⇒ ⋆ ⇒ ⋆)
| tc_prod : tctor (⋆ ⇒ ⋆ ⇒ ⋆)
| tc_all  κ : tctor ((κ ⇒ ⋆) ⇒ ⋆)
| tc_xist κ : tctor ((κ ⇒ ⋆) ⇒ ⋆)
| tc_rec  κ : tctor ((κ ⇒ κ) ⇒ κ).
