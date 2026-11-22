Set Implicit Arguments.

Require Import LibExtra DotTactics.

Require Import Coq.Program.Equality.

Require Import AbstractSyntax TypingMode Equivalence GeneralTyping.

Require Import PreciseTyping RecordTypes InertContext TightTyping Subenvironments Narrowing InertTightSubtyping EnvCorrespondence Indep Weakening.

Require Import Orctx Logctx OrctxLogctx Logpath LogpathOrder TypLogicInduction.

Require Import LayeredCommon LayeredSubtypingAtomic.

Require Import LayeredCapabilityBasic LayeredCapabilityBasicClosure LayeredCapabilityLogic.

Section WithTypingMode.

Context {typing_mode: Mode}.

Inductive ty_has_N_logic_ord (G: ctx) (e: renv): orctx -> typ -> Prop :=
| ty_has_N_logic_ord_or oc T:
    ty_has_N_closure G e T ->
    typ_notorand T ->
    ty_has_N_logic_ord G e oc T
| ty_has_N_logic_ord_and oc ocp T U:
    orctx_le oc ocp ->
    ty_has_N_logic_ord G e ocp (orctx_typ ocp T) ->
    ty_has_N_logic_ord G e ocp (orctx_typ ocp U) ->
    ty_has_N_logic_ord G e oc (orctx_typ ocp (typ_and T U))
.

End WithTypingMode.
