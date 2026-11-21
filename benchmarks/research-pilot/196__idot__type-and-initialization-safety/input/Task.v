Set Implicit Arguments.

Require Import LibExtra.

Require Import AbstractSyntax PreTyping Typing GeneralTyping RecordTypes InertTypes DefRecordInertTyping OperationalSemantics Effects Initialization InitTyping ConfigTyping.

Theorem preservation : forall Gamma Delta ℰs effss c c' U,
    ty_config Gamma Delta ℰs effss c U ->
    c ↦ c' ->
    exists Gamma' Delta' ℰs' effss', ty_config (Gamma & Gamma') Delta' ℰs' effss' c' U.

Theorem progress: forall Gamma Delta ℰs Es t s Sigma T,
    ty_config Gamma Delta ℰs Es (t ; s; Sigma) T ->
    answer (t; s; Sigma) \/
    exists s' Sigma' t', (t; s; Sigma) ↦ (t'; s'; Sigma').
