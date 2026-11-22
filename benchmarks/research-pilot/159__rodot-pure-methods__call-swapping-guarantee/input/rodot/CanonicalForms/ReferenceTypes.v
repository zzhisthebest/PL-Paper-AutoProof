Set Implicit Arguments.

Require Import LibExtra DotTactics.

Require Import AbstractSyntax TypingMode GeneralTyping InertTightSubtyping TypeInduction GeneralToTight TightTyping InvertibleTyping FlatInvertibleTyping RecordTypes InertContext PreciseTyping Substitution Weakening Narrowing EnvCorrespondence EWeakening TFree Deref Incap.

Require Import Equivalence.

Require Import Indep.

Require Import LayeredCapabilityMain LayeredTypingMainHard.

Section WithTypingMode.

Context (typing_mode: Mode).

Inductive incap_dec : dec -> Prop :=
| incap_dec_typ : forall A S T, incap_dec (dec_typ (typ_label_normal A) S T)
| incap_dec_fld : forall a S T, incap_dec (dec_fld a S T)
| incap_dec_met : forall m TC TZ TR, incap_dec (dec_met m TC TZ TR)
.

Inductive incap_atomic_type : typ -> Prop :=
| incap_atomic_dec D: incap_dec D -> incap_atomic_type (typ_rcd D)
| incap_atomic_fun S T: incap_atomic_type (typ_fun S T)
.

End WithTypingMode.
