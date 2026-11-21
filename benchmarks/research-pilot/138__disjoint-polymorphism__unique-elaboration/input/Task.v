Require Import String.

Require Import Coq.Structures.Equalities.

Require Import Coq.MSets.MSetInterface.

Require Import Arith.

Require Import Setoid.

Require Import Coq.Program.Equality.

Require Import SystemF.

Require Import Typing.

Module MExtended
       (Import VarTyp : UsualDecidableTypeFull)
       (Import set : MSetInterface.S).

Module MTyping := MTyping(VarTyp)(set).

Export MTyping.

Theorem typ_coherence : forall Gamma e d t E1, has_type_source_alg Gamma e d t E1 -> forall E2, has_type_source_alg Gamma e d t E2 -> E1 = E2.

End MExtended.
