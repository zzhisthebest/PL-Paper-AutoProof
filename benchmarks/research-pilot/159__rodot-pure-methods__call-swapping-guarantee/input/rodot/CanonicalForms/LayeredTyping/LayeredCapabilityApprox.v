Set Implicit Arguments.

Require Import Coq.Program.Equality.

Require Import LibExtra DotTactics.

Require Import AbstractSyntax TypingMode.

Require Import Equivalence GeneralTyping Indep.

Require Import PreciseTyping RecordTypes InertContext EnvCorrespondence.

Require Import TightTyping InertTightSubtyping.

Require Import Orctx Logctx Logpath.

Require Import WrapAction WrapActionMain.

Require Import LayeredCommon LayeredSubtypingAtomic.

Section WithTypingMode.

Context {typing_mode: Mode}.

Inductive ty_has_top_approx_logic: typ->Prop :=
| ty_has_top_approx_logic_top:
    ty_has_top_approx_logic typ_top
| ty_has_top_approx_logic_M TL TU:
    ty_has_top_approx_logic (typ_rcd (dec_typ (typ_label_refcap typ_refcap_mutability) TL TU))
| ty_has_top_approx_logic_orl T1 T2:
    ty_has_top_approx_logic T1 ->
    ty_has_top_approx_logic (typ_or T1 T2)
| ty_has_top_approx_logic_orr T1 T2:
    ty_has_top_approx_logic T2 ->
    ty_has_top_approx_logic (typ_or T1 T2)
| ty_has_top_approx_logic_and T1 T2:
    ty_has_top_approx_logic T1 ->
    ty_has_top_approx_logic T2 ->
    ty_has_top_approx_logic (typ_and T1 T2)
.

Inductive ty_has_top_approx_main: ctx -> renv -> typ -> Prop :=
| ty_has_top_approx_main_logic G e T:
    ty_has_top_approx_logic T ->
    ty_has_top_approx_main G e T
| ty_has_top_approx_main_name G e oc S1 S2 U y A z:
    ty_has_top_approx_main G e (logctx_typ oc (open z S1)) ->
    G ⊢! y ∶ U ⪼ typ_rcd (dec_typ A S1 S2) ->
    ty_has_top_approx_main G e (logctx_typ oc (typ_sel (avar_f y) A (avar_f z)))
| ty_has_top_approx_main_bnd G e oc T:
    ty_has_top_approx_main G e (logctx_typ oc typ_nocap) ->
    ty_has_top_approx_main G e (logctx_typ oc (typ_bnd T))
.

End WithTypingMode.
