Set Implicit Arguments.

Require Import LibExtra DotTactics.

Require Import Coq.Program.Equality.

Require Import AbstractSyntax TypingMode Equivalence GeneralTyping.

Require Import PreciseTyping RecordTypes InertContext TightTyping TightTypingHelpers Subenvironments Narrowing InertTightSubtyping EnvCorrespondence Indep Weakening.

Require Import Orctx Logctx Logpath OrctxLogctx.

Require Import LayeredCommon LayeredSubtypingAtomic.

Require Import LayeredCapabilityBasic LayeredCapabilityBasicClosure LayeredCapabilityLogic.

Require Import LayeredTypingAtomic LayeredTypingBasic LayeredTypingBasicClosure.

Section WithTypingMode.

Context {typing_mode: Mode}.

Inductive ty_inv_logic: ctx -> renv -> var -> typ -> Prop :=





| ty_inv_logic_or G e x T:
    x \in ctx_dom G ->
    ty_inv_basic_closure G e x T ->
    ty_inv_logic G e x T





| ty_inv_logic_and G e x oc T U:
    ty_inv_logic G e x (orctx_typ oc T) ->
    ty_inv_logic G e x (orctx_typ oc U) ->
    ty_inv_logic G e x (orctx_typ oc (typ_and T U))
.

End WithTypingMode.
