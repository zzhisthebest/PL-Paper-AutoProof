Set Implicit Arguments.

Require Import LibExtra DotTactics.

Require Import Coq.Program.Equality.

Require Import AbstractSyntax TypingMode Equivalence GeneralTyping.

Require Import PreciseTyping RecordTypes InertContext TightTyping Subenvironments Narrowing InertTightSubtyping EnvCorrespondence Indep Weakening.

Require Import Orctx Logctx OrctxLogctx Logpath LogpathOrder TypLogicInduction.

Require Import LayeredCommon LayeredSubtypingAtomic.

Require Import LayeredCapabilityBasic LayeredCapabilityBasicClosure LayeredCapabilityLogic LayeredCapabilityLogicOrdered LayeredCapabilityMain.

Require Import LayeredTypingAtomic LayeredTypingBasicClosure LayeredTypingLogic.

Section WithTypingMode.

Context {typing_mode: Mode}.

Section WithTyping.

Context (G: ctx) (e: renv) (x: var).

Context (HinG: inert G) (HGx: x \in ctx_dom G).

Context (Hcor: renv_corr G e).

Inductive ty_inv_logic_ord: orctx -> typ -> Prop :=

| ty_inv_logic_ord_or oc T:
    ty_inv_basic_closure G e x T ->
    typ_notorand T ->
    ty_inv_logic_ord oc T

| ty_inv_logic_ord_and oc ocp T U:
    orctx_le oc ocp ->
    ty_inv_logic_ord ocp (orctx_typ ocp T) ->
    ty_inv_logic_ord ocp (orctx_typ ocp U) ->
    ty_inv_logic_ord oc (orctx_typ ocp (typ_and T U))
.

End WithTyping.

Section WithTyping.

Context (G: ctx) (e: renv) (x: var).

Context (HinG: inert G) (HGx: x \in ctx_dom G).

Context (Hcor: renv_corr G e).

End WithTyping.

Section WithTyping.

Context (G: ctx) (e: renv) (w: var) (y: var).

Context (HinG: inert G) (Hcor: renv_corr G e) (Hbi: binds w y e).

Context (Hm:   mode_has_top_nm_subtype typing_mode).

End WithTyping.

End WithTypingMode.
