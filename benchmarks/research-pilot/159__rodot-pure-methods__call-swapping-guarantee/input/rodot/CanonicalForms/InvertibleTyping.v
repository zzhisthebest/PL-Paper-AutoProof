Set Implicit Arguments.

Require Import LibExtra DotTactics.

Require Import Coq.Program.Equality.

Require Import AbstractSyntax TypingMode Equivalence GeneralTyping.

Require Import PreciseTyping RecordTypes InertContext TightTyping Subenvironments Narrowing InertTightSubtyping EnvCorrespondence Indep Weakening Orctx Logctx.

Require Import Coq.Bool.Bool LibBoolExtra.

Require Import LayeredTypingMain LayeredSubtypingAtomic LayeredCapabilityBasic LayeredCapabilityBasicClosure LayeredCapabilityLogic LayeredCapabilityMain LayeredCommon LayeredTypingAtomic LayeredTypingBasic LayeredTypingBasicClosure LayeredTypingLogic LayeredTypingMainHard LayeredSubtypingMainOrd.

Require Import TypeInduction TightTypingHelpers.

Require Import FlatInvertibleTyping.

Require Import TypLogicInduction.

Require Import LayeredTypingMainCount.

Require Import LayeredSubtypingMainTree.

Section WithTypingMode.

Context {typing_mode: Mode}.

Notation "G '⁏' e '⊢##m' x '∶' T" := (ty_inv_main G e x T) (at level 40, e at level 39, x at level 59).

Definition ty_inv := match mode_ty_inv' typing_mode with | mode_ty_inv_layered => ty_inv_main | mode_ty_inv_flat => ty_var_inv end.

Notation "G '⁏' e '⊢##' x '∶' T" := (ty_inv G e x T) (at level 40, e at level 39, x at level 59).

End WithTypingMode.

Notation "G '⁏' e '⊢##m' x '∶' T" := (ty_inv_main G e x T) (at level 40, e at level 39, x at level 59).

Notation "G '⁏' e '⊢##' x '∶' T" := (ty_inv G e x T) (at level 40, e at level 39, x at level 59).
