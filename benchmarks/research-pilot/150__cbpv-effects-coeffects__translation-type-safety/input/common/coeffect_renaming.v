Require Export cbpv.common.fin_util.

Require Export cbpv.common.coeffects.

From Coq Require Import FunctionalExtensionality.

Definition ren_wb {n m A} (renamer : fin n -> fin m)
    (γ : gradeVec n) (γ' : gradeVec m)
    (Γ : fin n -> A) (Γ' : fin m -> A) : Prop :=
    ren_match renamer γ γ'
    /\ ren_match renamer Γ Γ'
    /\ default_or_preimage Qzero γ' renamer
    /\ ren_inj renamer.
