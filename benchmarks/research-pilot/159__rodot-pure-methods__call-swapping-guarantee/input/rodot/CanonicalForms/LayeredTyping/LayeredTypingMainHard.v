Set Implicit Arguments.

Require Import LibExtra DotTactics.

Require Import Coq.Program.Equality.

Require Import AbstractSyntax TypingMode Equivalence GeneralTyping.

Require Import PreciseTyping RecordTypes InertContext TightTyping Subenvironments Narrowing InertTightSubtyping EnvCorrespondence Indep Weakening Orctx Logctx Logpath LogpathOrder.

Require Import TypeInduction TypLogicInduction.

Require Import LayeredCommon LayeredSubtypingAtomic.

Require Import LayeredCapabilityBasic LayeredCapabilityBasicClosure LayeredCapabilityLogic LayeredCapabilityMain.

Require Import LayeredTypingAtomic LayeredTypingBasic LayeredTypingBasicClosure LayeredTypingLogic LayeredTypingMain LayeredTypingLogicOrdered LayeredSubtypingMainTree LayeredSubtypingMainOrd LayeredSubtypingMainTreeOrd LayeredSubtypingMainPrep LayeredSubtypingMain.

Require Import Lia.

Section WithTypingMode.

Context {typing_mode: Mode}.

Section WithContext.

Context (G: ctx) (e: renv) (x: var).

Context (Hin: inert G) (Hcor: renv_corr G e).

End WithContext.

Section WithContext.

Context (G: ctx) (e: renv) (x: var).

Context (Hin: inert G) (Hcor: renv_corr G e).

End WithContext.

Section WithContext.

Context (G: ctx) (e: renv) (x: var).

Context (Hin: inert G) (Hcor: renv_corr G e).

End WithContext.

End WithTypingMode.
