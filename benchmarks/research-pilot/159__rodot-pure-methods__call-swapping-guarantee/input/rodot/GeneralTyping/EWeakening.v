Set Implicit Arguments.

Require Import LibExtra DotTactics SyntaxClasses.

Require Import AbstractSyntax TypingMode GeneralTyping Equivalence Context.

Class EWeakeningE (A B: Set) (property: EnvProperty A B) :=
  ewkne e1 e2 e3 (a: A) T:
    property (e1 & e3) a T ->
    ok (e1 & e2) ->
    property (e1 & e2 & e3) a T.

Class EWeakening (A B: Set) (property: TypingProperty A B) :=
  ewkn G Go e1 e2 e3 (a: A) T:
    property G Go (e1 & e3) a T ->
    ok (e1 & e2) ->
    property G Go (e1 & e2 & e3) a T.

Section EWeakeningELemmata.

Context {A: Set} {AT: TypingEquiv A} {AW: EWeakeningE AT}.

End EWeakeningELemmata.

Section WeakeningLemmata.

Context {A B: Set} {P: TypingProperty A B} {AW: EWeakening P}.

End WeakeningLemmata.

Definition EWeakeningEInd (A B: Set) (property: EnvProperty A B) :=
   (forall (e: renv) (a: A) (b: B), (property e a b) -> forall e1 e2 e3,
    e = e1 & e3 ->
    ok (e1 & e2) ->
    (property (e1 & e2 & e3) a b)).

Definition EWeakeningInd (A B: Set) (property: TypingProperty A B) :=
   (forall (G:ctx) Go (e: renv) (a: A) (b: B), (property G Go e a b) -> forall e1 e2 e3,
    e = e1 & e3 ->
    ok (e1 & e2) ->
    (property G Go (e1 & e2 & e3) a b)).

Definition EWeakeningTInd (A: Set) (AT: Typing A) := EWeakeningInd obj_typing.

Definition EWeakeningIncapInd (_: ReferenceIncapacitate) :=
  EWeakeningInd obj_ref_incap.

Definition EWeakeningCapbndInd (C : typ_refcap_label) (_ : CapabilityBound C) :=
  EWeakeningInd obj_cap_bnd.

Definition EWeakeningDInd (A: Set) (AT: DecTyping A) := EWeakeningInd obj_dec_typing.

Definition EWeakeningTqInd (A: Set) (AT: TypingEquiv A) := EWeakeningEInd typing_equiv.
