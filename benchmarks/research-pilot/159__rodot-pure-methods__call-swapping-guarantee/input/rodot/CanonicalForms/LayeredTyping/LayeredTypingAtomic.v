Set Implicit Arguments.

Require Import Coq.Program.Equality.

Require Import LibExtra DotTactics.

Require Import AbstractSyntax TypingMode.

Require Import Equivalence GeneralTyping Indep.

Require Import PreciseTyping RecordTypes InertContext EnvCorrespondence.

Require Import TightTyping InertTightSubtyping TightTypingHelpers.

Require Import Orctx Logctx OrctxLogctx Logpath.

Require Import LayeredCommon LayeredSubtypingAtomic.

Require Import LayeredCapabilityBasic LayeredCapabilityMain.

Section WithTypingMode.

Context {typing_mode: Mode}.

Inductive ty_inv_atomic: ctx -> renv -> var -> typ -> Prop :=





| ty_inv_atomic_precise G e x T U V:
  G ⊢! x ∶ T ⪼ U ->
  typ_atomic U ->
  typing_equiv e U V ->
  ty_inv_atomic G e x V





| ty_inv_atomic_subtyp G e x S T:
  ty_inv_atomic G e x S ->
  subtyp_atomic G e S T ->
  ty_inv_atomic G e x T
.

End WithTypingMode.
