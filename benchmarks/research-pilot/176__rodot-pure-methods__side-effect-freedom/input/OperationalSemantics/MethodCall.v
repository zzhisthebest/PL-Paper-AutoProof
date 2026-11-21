Set Implicit Arguments.

Require Import LibExtra.

Require Import AbstractSyntax OperationalSemantics.

Inductive method_call_begin: config -> Prop :=
| method_call_begin_c w1 m w2 fs S e Lv:
  method_call_begin (trm_call (avar_f w1) m (avar_f w2); fs; S; e; Lv).

Definition config_stack C := (
  match C with
  t1 ; fs1 ; S1 ; e1 ; Lv1 => fs1
  end
).

Definition config_trm C := (
  match C with
  t1 ; fs1 ; S1 ; e1 ; Lv1 => t1
  end
).

Definition frame_within C1 m := (
  forall k C4,
    k <= m ->
    C1 ⊣ k ↦* C4 ->
    stack_suffix (config_stack C1) (config_stack C4)
).

Definition frame_end_in C1 m C3 := (
  C1 ⊣ m ↦* C3 /\
  frame_within C1 m /\
  (config_stack C3) = (config_stack C1) /\
  exists w3,
    (config_trm C3) = (trm_var (avar_f w3))
).

Definition frame_end_in' C1 m C3 := (
  C1 ⊣ m ↦* C3 /\
  (config_stack C3) = (config_stack C1) /\
  exists w3,
    (config_trm C3) = (trm_var (avar_f w3))
).
