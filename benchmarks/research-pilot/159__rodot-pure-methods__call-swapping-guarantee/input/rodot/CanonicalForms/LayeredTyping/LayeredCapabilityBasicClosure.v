Set Implicit Arguments.

Require Import Coq.Program.Equality.

Require Import LibExtra DotTactics.

Require Import AbstractSyntax TypingMode.

Require Import Equivalence GeneralTyping Indep.

Require Import PreciseTyping RecordTypes InertContext EnvCorrespondence.

Require Import TightTyping InertTightSubtyping.

Require Import Orctx Logctx OrctxLogctx Logpath.

Require Import LayeredCommon LayeredSubtypingAtomic LayeredCapabilityBasic.

Section WithTypingMode.

Context {typing_mode: Mode}.

Definition ty_has_M_closure G e := ty_or_closure (ty_has_M G e).

Definition ty_has_N_closure G e := ty_or_closure (ty_has_N G e).

Definition ty_has_top_closure G e := ty_or_closure (ty_has_top_atomic G e).

End WithTypingMode.
