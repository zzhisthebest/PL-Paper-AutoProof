Set Implicit Arguments.

Require Import Coq.Program.Equality.

Require Import LibExtra DotTactics.

Require Import AbstractSyntax TypingMode.

Require Import Equivalence GeneralTyping Indep.

Require Import PreciseTyping RecordTypes InertContext EnvCorrespondence.

Require Import TightTyping InertTightSubtyping TightTypingHelpers.

Require Import Orctx Logctx OrctxLogctx Logpath.

Require Import LayeredCommon LayeredSubtypingAtomic.

Require Import LayeredCapabilityBasic LayeredCapabilityBasicClosure LayeredCapabilityMain.

Require Import LayeredTypingAtomic.

Section WithTypingMode.

Context {typing_mode: Mode}.

Inductive ty_inv_basic: ctx -> renv -> var -> typ -> Prop :=



| ty_inv_basic_atomic G e x T:
    ty_inv_atomic G e x T ->
    ty_inv_basic G e x T




| ty_inv_basic_NM G e x  T U:
    mode_has_top_nm_subtype typing_mode ->
    ty_has_N_closure G e T ->
    ty_has_M_closure G e U ->
    ty_inv_basic G e x (typ_or T U)




| ty_inv_basic_MN G e x T U:
    mode_has_top_nm_subtype typing_mode ->
    ty_has_M_closure G e T ->
    ty_has_N_closure G e U ->
    ty_inv_basic G e x (typ_or T U)
.

End WithTypingMode.
