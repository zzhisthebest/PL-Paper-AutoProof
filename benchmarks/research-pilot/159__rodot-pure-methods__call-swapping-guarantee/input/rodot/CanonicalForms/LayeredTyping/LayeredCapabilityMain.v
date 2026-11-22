Set Implicit Arguments.

Require Import Coq.Program.Equality.

Require Import LibExtra DotTactics.

Require Import AbstractSyntax TypingMode.

Require Import Equivalence GeneralTyping Indep.

Require Import PreciseTyping RecordTypes InertContext EnvCorrespondence.

Require Import TightTyping InertTightSubtyping TightTypingHelpers.

Require Import Orctx Logctx OrctxLogctx Logpath.

Require Import LayeredCommon LayeredSubtypingAtomic LayeredCapabilityBasic LayeredCapabilityBasicClosure LayeredCapabilityLogic LayeredCapabilityLogicOrdered.

Require Import WrapAction WrapActionMain.

Section WithTypingMode.

Context {typing_mode: Mode}.

Inductive ty_has_N_main: ctx -> renv -> typ -> Prop :=
| ty_has_N_main_logic G e T:
    ty_has_N_logic G e T ->
    ty_has_N_main G e T
| ty_has_N_main_name G e oc S1 S2 U y A z:
    ty_has_N_main G e (logctx_typ oc (open z S1)) ->
    G ⊢! y ∶ U ⪼ typ_rcd (dec_typ A S1 S2) ->
    ty_has_N_main G e (logctx_typ oc (typ_sel (avar_f y) A (avar_f z)))
| ty_has_N_main_bnd G e oc T:
    ty_has_N_main G e (logctx_typ oc typ_nocap) ->
    ty_has_N_main G e (logctx_typ oc (typ_bnd T))
.

End WithTypingMode.
