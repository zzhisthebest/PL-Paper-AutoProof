Set Implicit Arguments.

Require Import LibExtra DotTactics.

Require Import AbstractSyntax TypingMode GeneralTyping InertTightSubtyping GeneralToTight TightTyping InvertibleTyping RecordTypes InertContext PreciseTyping OperationalSemantics Substitution Weakening HeapCorrespondence HeapUpdate CanonicalForms Narrowing EnvCorrespondence EWeakening Visibility ConfigTyping ConfigVarkinds TFree Deref ReferenceTypes TypedOperationalSemantics Defree Defs Closedness.

Require Import TypedReductionEquivalence TypedProgress TypedPreservation.

Require Import Logic.Classical_Prop Logic.Classical_Pred_Type.

Section WithTypingMode.

Context (typing_mode: Mode).

End WithTypingMode.
