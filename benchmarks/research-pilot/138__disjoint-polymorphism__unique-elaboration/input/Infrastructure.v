Require Import String.

Require Import Coq.Structures.Equalities.

Require Import Coq.Structures.EqualitiesFacts.

Require Import Coq.MSets.MSetInterface.

Require Import Arith.

Require Import Setoid.

Require Import Coq.Program.Equality.

Require Import SystemF.

Require Import Language.

Module MInfrastructure
       (Import VarTyp : UsualDecidableTypeFull)
       (Import set : MSetInterface.S).

Module MLanguage := MLanguage(VarTyp)(set).

Export MLanguage.

End MInfrastructure.
