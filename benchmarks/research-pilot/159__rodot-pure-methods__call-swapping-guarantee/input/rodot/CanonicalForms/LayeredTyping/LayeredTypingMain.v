Set Implicit Arguments.

Require Import LibExtra DotTactics.

Require Import Coq.Program.Equality.

Require Import AbstractSyntax TypingMode Equivalence GeneralTyping.

Require Import PreciseTyping RecordTypes InertContext TightTyping Subenvironments Narrowing InertTightSubtyping EnvCorrespondence Indep Weakening TypeInduction.

Require Import Orctx Logctx Logpath.

Require Import LayeredCommon LayeredSubtypingAtomic.

Require Import LayeredCapabilityMain LayeredCapabilityBasic LayeredCapabilityLogic.

Require Import LayeredTypingAtomic LayeredTypingBasic LayeredTypingBasicClosure.

Require Import LayeredTypingLogic LayeredTypingLogicOrdered WrapAction.

Section WithTypingMode.

Context {typing_mode: Mode}.

Inductive ty_inv_main: ctx -> renv -> var -> typ -> Prop :=



| ty_inv_main_logic G e x T:
    ty_inv_logic G e x T ->
    ty_inv_main G e x T




| ty_inv_main_sel G e x oc S1 S2 U y A z:
    ty_inv_main G e x (logctx_typ oc (open z S1)) ->
    G ⊢! y ∶ U ⪼ typ_rcd (dec_typ A S1 S2) ->
    ty_inv_main G e x (logctx_typ oc (typ_sel (avar_f y) A (avar_f z)))





| ty_inv_main_bnd G e x oc T:
    typ_indep_b 0 T ->
    ((mode_has_incap typing_mode) -> (G⁏e ⊢# typ_nocap <: (open x T))) ->
    ty_inv_main G e x (logctx_typ oc (open x T)) ->
    ty_inv_main G e x (logctx_typ oc (typ_bnd T))



| ty_inv_main_nocap_bnd G e x oc T:
    ty_inv_main G e x (logctx_typ oc typ_nocap) ->
    ty_inv_main G e x (logctx_typ oc (typ_bnd T))
.

Inductive wrap_action_ty_inv_main: ctx -> renv -> var -> wrap_action -> Prop :=
|  wrap_action_ty_inv_main_name G e x y U z A S1 S2 oc:
    inert G ->
    G ⊢! y ∶ U ⪼ typ_rcd (dec_typ A S1 S2) ->
    wrap_action_ty_inv_main G e x (wrap_action_c oc (open z S1) (typ_sel (avar_f y) A (avar_f z)))
| wrap_action_ty_inv_main_bnd G e x oc T:
    typ_indep_b 0 T ->
    ((mode_has_incap typing_mode) -> (G⁏e ⊢# typ_nocap <: (open x T))) ->
    wrap_action_ty_inv_main G e x (wrap_action_c oc (open x T) (typ_bnd T))
| wrap_action_ty_inv_main_nocap_bnd G e x oc T:
    wrap_action_ty_inv_main G e x (wrap_action_c oc typ_nocap (typ_bnd T))
.

End WithTypingMode.
