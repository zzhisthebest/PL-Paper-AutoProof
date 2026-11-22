Set Implicit Arguments.

Require Import LibExtra DotTactics AbstractSyntax TypingMode.

Require Import TFree.

Require Import HeapCorrespondence InertContext EnvCorrespondence ConfigTyping ConfigNotations.

Section WithTypingMode.

Context {typing_mode: Mode}.

Definition ty_config_accessories G e fs S t (T: typ) Lv :=
    inert G /\
    all_tfree_k_stack G fs v_ref /\
    all_tfree_k G t v_ref /\
    ty_nothing_fresh_in_config G T (t ; fs ; S ; e; Lv) /\
    has_null Lv /\
    sealed G /\
    config_closed (t; fs; S; e; Lv) /\
    closed T.

Definition heap_correspond_accessories G (e: renv) (s: heap) :=
  ctx_ok G /\
  ctx_weakens G /\
  ok s /\
  ok e /\
  ctx_kdom v_loc G = dom s /\
  ctx_kdom v_ref G = dom e /\
  renv_corr G e.

End WithTypingMode.
