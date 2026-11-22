Set Implicit Arguments.

Require Import LibExtra DotTactics AbstractSyntax TypingMode.

Require Import HeapValid ConfigTyping ConfigVarkinds EnvCorrespondence HeapCorrespondence OperationalSemantics HeapUpdate.

Inductive config_valid: config->Prop :=
  inductive_conf_c t s Sigma e Lv:
    ok Sigma ->
    ok e ->
    disjoint (dom e) (dom Sigma) ->
    (fv_env e) \c dom Sigma ->
    config_valid (t; s; Sigma; e; Lv).

Definition conf_ok c: Prop :=
  match c with
  | (t1 ; s1 ; S1 ; e1 ; Lv1) =>
    fresh \{} (length (keys S1 ++ keys e1)%list) (keys S1 ++ keys e1)%list
  end.

Section WithTypingMode.

Context (typing_mode: Mode).

End WithTypingMode.
