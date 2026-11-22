Set Implicit Arguments.

Require Import LibExtra DotTactics.

Require Import AbstractSyntax TypingMode.

Require Import PreciseTyping InertContext Logctx Logpath.

Require Import WrapAction.

Section WithTypingMode.

Context {typing_mode: Mode}.

Inductive wrap_action_has_N_main: ctx -> renv -> wrap_action -> Prop :=
|  wrap_action_has_N_main_name G e y U z A S1 S2 oc:
    inert G ->
    G ⊢! y ∶ U ⪼ typ_rcd (dec_typ A S1 S2) ->
    wrap_action_has_N_main G e (wrap_action_c oc (open z S1) (typ_sel (avar_f y) A (avar_f z)))
| wrap_action_has_N_main_bnd G e oc T:
    wrap_action_has_N_main G e (wrap_action_c oc typ_nocap (typ_bnd T))
.

End WithTypingMode.
