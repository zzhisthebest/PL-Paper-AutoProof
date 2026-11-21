Set Implicit Arguments.

Require Import LibExtra.

Require Import Coq.Program.Equality.

Require Import AbstractSyntax RecordTypes.

Inductive inert_typ : typ -> Prop :=
  | inert_typ_all : forall S T, inert_typ (typ_all S T)
  | inert_typ_con :
      forall Ts is' T,
        record_type T ->
        inert_typ (typ_con Ts is' T)
  | inert_typ_bnd : forall T,
      record_type T ->
      inert_typ (typ_bnd T).

Inductive inert : ctx -> Prop :=
  | inert_empty : inert empty
  | inert_all : forall G x T,
      inert G ->
      inert_typ T ->
      x # G ->
      inert (G & x ~ T).
