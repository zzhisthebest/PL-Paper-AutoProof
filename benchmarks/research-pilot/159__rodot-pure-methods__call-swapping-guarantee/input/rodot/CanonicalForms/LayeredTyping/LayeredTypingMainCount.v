Set Implicit Arguments.

Require Import LibExtra DotTactics.

Require Import Coq.Program.Equality.

Require Import AbstractSyntax TypingMode Equivalence GeneralTyping.

Require Import PreciseTyping RecordTypes InertContext TightTyping TightTypingHelpers Subenvironments Narrowing InertTightSubtyping EnvCorrespondence Indep Weakening Orctx Logctx Logpath LogpathOrder.

Require Import TypeInduction TypLogicInduction.

Require Import LayeredCommon LayeredSubtypingAtomic.

Require Import LayeredCapabilityBasic LayeredCapabilityBasicClosure LayeredCapabilityLogic LayeredCapabilityMain.

Require Import LayeredTypingAtomic LayeredTypingBasic LayeredTypingBasicClosure LayeredTypingLogic LayeredTypingMain LayeredTypingLogicOrdered LayeredSubtypingMainTree LayeredSubtypingMainTreeOrd LayeredSubtypingMainOrd LayeredSubtypingMainPrep LayeredSubtypingMain LayeredTypingMainHard.

Require Import Lia.

Section WithTypingMode.

Context {typing_mode: Mode}.

Section WithContext.

Context (G: ctx) (e: renv) (x: var).

Context (Hin: inert G) (Hcor: renv_corr G e).

Definition ty_inv_main_count n T :=  x \in ctx_dom G /\ exists U tr, ty_inv_logic G e x U /\ ty_main_tree_linear_sub G e x tr U T /\ (ty_main_tree_folds tr = n).

Definition ty_has_N_main_count n T := exists U tr, ty_has_N_logic G e U /\  ty_main_tree_linear_sub G e x tr U T /\ (ty_main_tree_folds tr = n).

End WithContext.

End WithTypingMode.
