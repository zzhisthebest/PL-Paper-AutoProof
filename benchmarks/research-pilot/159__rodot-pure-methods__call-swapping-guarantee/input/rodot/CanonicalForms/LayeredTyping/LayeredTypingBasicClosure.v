Set Implicit Arguments.

Require Import LibExtra DotTactics.

Require Import Coq.Program.Equality.

Require Import AbstractSyntax TypingMode Equivalence GeneralTyping.

Require Import PreciseTyping RecordTypes InertContext TightTyping Subenvironments Narrowing InertTightSubtyping EnvCorrespondence Indep Weakening Orctx Logctx Logpath.

Require Import LayeredCommon LayeredSubtypingAtomic LayeredCapabilityBasic LayeredCapabilityBasicClosure LayeredCapabilityMain LayeredTypingAtomic LayeredTypingBasic.

Require Import LayeredCapabilityLogic.

Section WithTypingMode.

Context {typing_mode: Mode}.

Definition ty_inv_basic_closure G e x:= ty_or_closure (ty_inv_basic G e x).

End WithTypingMode.
