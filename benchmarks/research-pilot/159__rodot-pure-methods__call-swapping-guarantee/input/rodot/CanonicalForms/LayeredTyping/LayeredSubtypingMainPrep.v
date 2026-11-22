Set Implicit Arguments.

Require Import LibExtra DotTactics.

Require Import Coq.Program.Equality.

Require Import AbstractSyntax TypingMode Equivalence GeneralTyping.

Require Import PreciseTyping RecordTypes InertContext TightTyping Subenvironments Narrowing InertTightSubtyping EnvCorrespondence Indep Weakening Orctx Logctx Logpath LogpathOrder.

Require Import TypeInduction TypLogicInduction.

Require Import LayeredCommon LayeredSubtypingAtomic.

Require Import LayeredCapabilityBasic LayeredCapabilityBasicClosure LayeredCapabilityLogic LayeredCapabilityMain.

Require Import LayeredTypingAtomic LayeredTypingBasic LayeredTypingBasicClosure LayeredTypingLogic LayeredTypingMain.

Section WithTypingMode.

Context {typing_mode: Mode}.

Inductive ty_main_prep (G: ctx)(e:renv): typ -> typ -> Prop :=
| ty_main_prep_refl T:
  ty_main_prep G e T T
| ty_main_prep_nocap T oc U:
  ty_main_prep G e T (logctx_typ oc typ_nocap) ->
  ty_has_N_logic G e U ->
  ty_main_prep G e T (logctx_typ oc U)
| ty_main_prep_sel T oc y A z U:
  ty_main_prep G e T (logctx_typ oc (typ_sel (avar_f y) A (avar_f z))) ->
  ty_main_prep G e T (logctx_typ oc U)
| ty_main_prep_bnd T oc U U1:
  ty_main_prep G e T (logctx_typ oc (typ_bnd U1)) ->
  ty_main_prep G e T (logctx_typ oc U)
.

Section WithContext.

Context (G: ctx)(e: renv).

End WithContext.

End WithTypingMode.
