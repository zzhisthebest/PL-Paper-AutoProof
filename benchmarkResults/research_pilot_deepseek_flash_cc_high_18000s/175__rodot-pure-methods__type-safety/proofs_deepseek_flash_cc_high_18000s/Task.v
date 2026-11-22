Set Implicit Arguments.

Require Import LibExtra.

Require Import Coq.Program.Equality.

Require Import AbstractSyntax TypingMode GeneralTyping RecordTypes InertContext OperationalSemantics HeapCorrespondence HeapUpdate EnvCorrespondence ConfigTyping ConfigVarkinds TFree Deref.

Section WithTypingMode.

Context (typing_mode: Mode).

Theorem soundness_initial (t : trm) (T : typ):

    closed t ->
    closed T ->
    ctx_empty⁏empty ⊢ t ∶ T ->
    exists C, (config_initial t C) /\ (

      (exists (n : nat) (Ca : config),
          answer Ca /\ (C ⊣n↦* Ca)) \/

      (forall (n : nat), exists (Cn : config),
            C ⊣n↦* Cn)
    ).

End WithTypingMode.
