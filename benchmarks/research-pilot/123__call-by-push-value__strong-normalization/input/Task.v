Require Import CBPV.SyntacticTyping CBPV.AbstractReductionSystems CBPV.StrongReduction.

Set Implicit Arguments.

Require Import Logic List.

Require Import Classes.Morphisms.

Import List Notations.

Theorem strong_normalisation_cbpv n (Gamma: ctx n) P B:
  Gamma ⊢ P : B -> SN sstep P.
