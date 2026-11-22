Set Implicit Arguments.

Require Import Logic List Classes.Morphisms.

Import List Notations.

Require Export CBPV.ProgramContexts.

Record CBPVv {n: nat} (Gamma: ctx n) (A: valtype) :=
  mkCBPVv { CBPVv_v :> value n; CBPVv_H :> Gamma ⊩ CBPVv_v : A }.

Record CBPVc {n: nat} (Gamma: ctx n) (B: comptype) :=
  mkCBPVc { CBPVc_c :> comp n; CBPVc_H :> Gamma ⊢ CBPVc_c : B }.

Definition value_obseq {n: nat} {A: valtype} {Gamma: ctx n} (H1 H2: CBPVv Gamma A) :=
  forall (G: groundtype) (C: cctx true 0 n),
    null [[Gamma]] ⊢ C : F G; A -> forall v, (fillc C H1 >* ret v) <-> (fillc C H2 >* ret v).

Notation "V1 ≈ V2" := (value_obseq V1 V2) (at level 50).

Definition comp_obseq {n: nat} {B: comptype} {Gamma: ctx n} (H1 H2: CBPVc Gamma B) :=
  forall (G: groundtype) (C: cctx false 0 n),
    null [[Gamma]] ⊢ C : F G; B -> forall v, (fillc C H1 >* ret v) <-> (fillc C H2 >* ret v).

Notation "C1 ≃ C2" := (comp_obseq C1 C2) (at level 50).
