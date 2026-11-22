Set Implicit Arguments.

Require Import LibExtra DotTactics.

Require Import Coq.Program.Equality.

Require Import AbstractSyntax TypingMode Equivalence GeneralTyping.

Require Import PreciseTyping RecordTypes InertContext TightTyping Subenvironments Narrowing InertTightSubtyping EnvCorrespondence Indep Weakening Orctx Logctx Logpath LogpathOrder.

Require Import TypeInduction TypLogicInduction.

Require Import LayeredCommon LayeredSubtypingAtomic.

Require Import LayeredCapabilityBasic LayeredCapabilityBasicClosure LayeredCapabilityLogic LayeredCapabilityMain.

Require Import LayeredTypingAtomic LayeredTypingBasic LayeredTypingBasicClosure LayeredTypingLogic LayeredTypingMain.

Require Import LayeredSubtypingMainTree.

Section WithTypingMode.

Context {typing_mode: Mode}.

Inductive ty_sub_main_tree_ord (G: ctx) (e: renv) (x: var): nat -> typ -> typ -> Prop :=
| ty_sub_main_tree_ord_refl T:
    ty_sub_main_tree_ord G e x 0 T T

| ty_sub_main_tree_ord_sel n tr T ocp S1 S2 U y A z:
    ty_main_tree_linear_sub G e x tr T (logctx_typ ocp (open z S1)) ->
    G ⊢! y ∶ U ⪼ typ_rcd (dec_typ A S1 S2) ->
    n =  (S (ty_main_tree_folds tr)) ->
    ty_sub_main_tree_ord G e x n T (logctx_typ ocp (typ_sel (avar_f y) A (avar_f z)))
| ty_sub_main_tree_ord_bnd n tr ocp ocl T U:
    ty_main_tree_linear_sub G e x tr (logctx_typ ocl U) (logctx_typ ocp (open x T)) ->
    ((mode_has_incap typing_mode) -> (ty_has_N_logic G e U /\ ty_main_tree_linear_sub G e x (ty_main_tree_under_lc tr (logctx_path ocp)) U (open x T))) ->
    logctx_follow ocl ocp ->
    typ_indep_b 0 T ->
    n = (S (ty_main_tree_folds tr)) ->
    ty_sub_main_tree_ord G e x n (logctx_typ ocl U) (logctx_typ ocp (typ_bnd T))
| ty_sub_main_tree_ord_nocap_bnd n tr ocp T U:
    ty_main_tree_linear_sub G e x tr U (logctx_typ ocp typ_nocap) ->
    n = (S (ty_main_tree_folds tr)) ->
    ty_sub_main_tree_ord G e x n U (logctx_typ ocp (typ_bnd T))
.

Section WithContext.

Context (G: ctx) (e: renv) (x: var).

Context (Hin: inert G).

End WithContext.

Section WithContext.

Context (G: ctx) (e: renv) (x: var).

Context (Hin: inert G).

End WithContext.

End WithTypingMode.
