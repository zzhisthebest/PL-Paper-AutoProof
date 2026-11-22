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

Inductive ty_sub_main_ord_cap (G: ctx) (e: renv) (x: var): nat -> logctx -> typ -> typ -> Prop :=
| ty_sub_main_ord_cap_refl ocl T:
    ty_sub_main_ord_cap G e x 0 ocl T T

| ty_sub_main_ord_cap_sel n ocl T ocp S1 S2 U y A z:
    ty_sub_main_ord_cap G e x n ocp T (logctx_typ ocp (open z S1)) ->
    G ⊢! y ∶ U ⪼ typ_rcd (dec_typ A S1 S2) ->
    logctx_le ocl ocp ->
    ty_sub_main_ord_cap G e x (S n) ocl T (logctx_typ ocp (typ_sel (avar_f y) A (avar_f z)))
| ty_sub_main_ord_cap_bnd n ocl ocp T U:
    ty_sub_main_ord_cap G e x n ocp U (logctx_typ ocp typ_nocap) ->
    logctx_le ocl ocp ->
    ty_sub_main_ord_cap G e x (S n) ocl U (logctx_typ ocp (typ_bnd T))
.

Inductive ty_sub_main_ord (G: ctx) (e: renv) (x: var): nat -> logctx -> typ -> typ -> Prop :=
| ty_sub_main_ord_refl ocl T:
    ty_sub_main_ord G e x 0 ocl T T

| ty_sub_main_ord_sel n ocl T ocp S1 S2 U y A z:
    ty_sub_main_ord G e x n ocp T (logctx_typ ocp (open z S1)) ->
    G ⊢! y ∶ U ⪼ typ_rcd (dec_typ A S1 S2) ->
    logctx_le ocl ocp ->
    ty_sub_main_ord G e x (S n) ocl T (logctx_typ ocp (typ_sel (avar_f y) A (avar_f z)))
| ty_sub_main_ord_bnd n1 n2 ocl ocp T Tn U:
    ty_sub_main_ord G e x n1 ocl U (logctx_typ ocp (open x T)) ->
    ((mode_has_incap typing_mode) -> (ty_has_N_logic G e Tn /\ ty_sub_main_ord G e x n2 logctx_nil Tn (open x T))) ->
    typ_indep_b 0 T ->
    logctx_le ocl ocp ->
    ty_sub_main_ord G e x (S (n1 + n2)) ocl U (logctx_typ ocp (typ_bnd T))
| ty_sub_main_ord_nocap_bnd n ocl ocp T U:
    ty_sub_main_ord G e x n ocp U (logctx_typ ocp typ_nocap) ->
    logctx_le ocl ocp ->
    ty_sub_main_ord G e x (S n) ocl U (logctx_typ ocp (typ_bnd T))
.

Section WithContext.

Context (G: ctx) (e: renv) (x: var).

Context (Hin: inert G).

End WithContext.

End WithTypingMode.
