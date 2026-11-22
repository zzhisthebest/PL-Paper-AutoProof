Set Implicit Arguments.

Require Import LibExtra DotTactics AbstractSyntax.

Require Import Context Equivalence Indep GeneralTyping.

Require Import Transformation TransformationLifting Weakening EWeakening Substitution.

Require Import TypingHelpers TransformationConfig ConfigTyping.

Require Import ConfigSimilarity.

Section WithTypingMode.

Context (typing_mode: Mode).

Inductive trf_similarity: TransformConfig :=
| trf_similarity_c Ga Ca T Gb Cb:
  ty_config Ga Ca T ->
  ty_config Gb Cb T ->
  similar_conf_1to1 Ca Cb ->
  〈Ga ⊢ Ca ∶ T〉 ∼trf_similarity∼> 〈Gb ⊢ Cb ∶ T〉.

End WithTypingMode.
