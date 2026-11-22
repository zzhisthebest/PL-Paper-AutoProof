Set Implicit Arguments.

Require Import LibExtra DotTactics.

Require Import Coq.Program.Equality.

Require Import AbstractSyntax TypingMode GeneralTyping InertTightSubtyping GeneralToTight TightTyping InvertibleTyping RecordTypes InertContext PreciseTyping OperationalSemantics Substitution Weakening HeapCorrespondence HeapUpdate CanonicalForms Subenvironments Narrowing EnvCorrespondence EWeakening ConfigTyping ConfigVarkinds TFree Deref TypedOperationalSemantics TypedReductionEquivalence TypedProgress TypedPreservation TypedSoundness.

Section WithTypingMode.

Context (typing_mode: Mode).

End WithTypingMode.
