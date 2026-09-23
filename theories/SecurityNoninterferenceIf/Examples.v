From AutoProof.SecurityNoninterferenceIf Require Import
  Syntax Semantics Typing Evaluation Metatheory Substitution LogicalRelation Noninterference.

Example secret_if_result_typed :
  has_type empty
    (tm_if (tm_inl (tm_unit public) secret)
      (tm_unit public) (tm_unit public) High)
    (Ty_Unit secret).
Proof.
  change (has_type empty
    (tm_if (tm_inl (tm_unit public) secret)
      (tm_unit public) (tm_unit public) High)
    (ty_protect High (Ty_Unit public))).
  eapply T_If with (k := secret).
  - apply T_Inl.
    + apply T_Unit. exact I.
    + exact I.
    + exact I.
  - apply T_Unit. exact I.
  - apply T_Unit. exact I.
  - exact I.
Qed.

Example secret_if_result_protected :
  evaluates
    (tm_if (tm_inl (tm_unit public) secret)
      (tm_unit public) (tm_unit public) High)
    (tm_unit secret).
Proof.
  apply big_step_sound.
  change (big_step
    (tm_if (tm_inl (tm_unit public) secret)
      (tm_unit public) (tm_unit public) High)
    (protect_value (tm_unit public) High)).
  eapply B_IfTrue with (k := secret).
  - apply B_Inl. apply B_Unit.
  - exact I.
  - apply B_Unit.
Qed.

Example false_selects_else :
  evaluates
    (tm_if (tm_inr (tm_unit public) public)
      (tm_unit secret) (tm_unit public) Low)
    (tm_unit public).
Proof.
  apply big_step_sound.
  change (big_step
    (tm_if (tm_inr (tm_unit public) public)
      (tm_unit secret) (tm_unit public) Low)
    (protect_value (tm_unit public) Low)).
  eapply B_IfFalse with (k := public).
  - apply B_Inr. apply B_Unit.
  - exact I.
  - apply B_Unit.
Qed.
