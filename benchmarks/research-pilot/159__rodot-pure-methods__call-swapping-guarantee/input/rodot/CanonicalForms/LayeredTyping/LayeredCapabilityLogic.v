Set Implicit Arguments.

Require Import Coq.Program.Equality.

Require Import LibExtra DotTactics.

Require Import AbstractSyntax TypingMode.

Require Import Equivalence GeneralTyping Indep.

Require Import PreciseTyping RecordTypes InertContext EnvCorrespondence.

Require Import TightTyping InertTightSubtyping TightTypingHelpers.

Require Import Orctx Logctx OrctxLogctx Logpath.

Require Import LayeredCommon LayeredSubtypingAtomic.

Require Import LayeredCapabilityBasic LayeredCapabilityBasicClosure.

Section WithTypingMode.

Context {typing_mode: Mode}.

Inductive ty_has_N_logic (G: ctx) (e: renv): typ -> Prop :=
| ty_has_N_logic_or T:
    ty_has_N_closure G e T ->
    ty_has_N_logic G e T
| ty_has_N_logic_oc_and oc T U:
    ty_has_N_logic G e (orctx_typ oc T) ->
    ty_has_N_logic G e (orctx_typ oc U) ->
    ty_has_N_logic G e (orctx_typ oc (typ_and T U))
.

End WithTypingMode.
