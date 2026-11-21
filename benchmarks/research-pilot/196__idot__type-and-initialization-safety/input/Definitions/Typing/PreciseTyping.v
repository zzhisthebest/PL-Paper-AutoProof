Set Implicit Arguments.

Require Import LibExtra.

Require Import Coq.Program.Equality.

Require Import AbstractSyntax.

Reserved Notation "G '⊢!' x '∶' T '⪼' U" (at level 40, x at level 59).

Inductive precise_flow : var -> ctx -> typ -> typ -> Prop :=

  | pf_bind : forall x G T,
      binds x T G ->
      G ⊢! x ∶ T ⪼ T

  | pf_open : forall x G T U,
      G ⊢! x ∶ T ⪼ typ_bnd U ->
      G ⊢! x ∶ T ⪼ open x U

  | pf_and1 : forall x G T U1 U2,
      G ⊢! x ∶ T ⪼ typ_and U1 U2 ->
      G ⊢! x ∶ T ⪼ U1

  | pf_and2 : forall x G T U1 U2,
      G ⊢! x ∶ T ⪼ typ_and U1 U2 ->
      G ⊢! x ∶ T ⪼ U2

where "G '⊢!' x '∶' T '⪼' U" := (precise_flow x G T U).
