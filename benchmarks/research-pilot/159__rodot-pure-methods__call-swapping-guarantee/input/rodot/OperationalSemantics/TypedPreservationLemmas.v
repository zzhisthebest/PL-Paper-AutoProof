Set Implicit Arguments.

Require Import LibExtra DotTactics.

Require Import AbstractSyntax TypingMode GeneralTyping InertTightSubtyping GeneralToTight TightTyping InvertibleTyping RecordTypes RecordDefs InertContext PreciseTyping OperationalSemantics Substitution Renaming Weakening HeapCorrespondence HeapUpdate CanonicalForms Narrowing EnvCorrespondence EWeakening Visibility ConfigTyping ConfigVarkinds TFree Deref ReferenceTypes TypedOperationalSemantics Defree Defs Closedness.

Require Import TypedReductionEquivalence NothingFresh.

Section WithTypingMode.

Context (typing_mode: Mode).

End WithTypingMode.
