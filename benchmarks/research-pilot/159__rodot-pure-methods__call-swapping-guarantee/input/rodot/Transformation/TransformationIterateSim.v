Set Implicit Arguments.

Require Import LibExtra DotTactics AbstractSyntax.

Require Import Context Equivalence Indep GeneralTyping.

Require Import Transformation TransformationLifting Weakening EWeakening Substitution.

Require Import TypingHelpers TransformationConfig ConfigTyping.

Require Import TransformationTerm TransformationConfig TransformationSimilarity.

Section WithTypingMode.

Context (typing_mode: Mode).

Definition trf_lift_sim_conf (TL: TermTransform): TransformConfig :=
  (trf_iterate (TransformCondConfTyped typing_mode) (trf_union (trf_similarity typing_mode) (trf_lift_idtyp_conf typing_mode TL))).

End WithTypingMode.

Section WithTypingMode.

Context (typing_mode: Mode).

End WithTypingMode.
