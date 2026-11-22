Set Implicit Arguments.

Require Import LibExtra.

Require Import AbstractSyntax GeneralTyping TypingContext.

Class Unhiding (A B: Set) (property: TypingProperty A B) :=
  unhiding G1 G2 Go e (a: A) (b: B):
    property ((ctx_hide G1) §& G2) Go e a b ->
    property (G1 §& G2) Go e a b.

Class Hiding (A B: Set) (property: TypingProperty A B) :=
  hiding G1 G2 Go e (a: A) (b: B):
    property (G1 §& G2) Go e a b ->
    property ((ctx_hide G1) §& G2) Go e a b.

Section UnhidingLemmata.

Context {A B: Set}{P: TypingProperty A B}{AW: Unhiding P}.

End UnhidingLemmata.

Section HidingLemmata.

Context {A B: Set}{P: TypingProperty A B}{AW: Hiding P}.

End HidingLemmata.

Definition UnhidingInd (A B: Set) (property: TypingProperty A B) :=
  forall G Go e (a: A) (b: B),
    property G Go e a b ->
    forall G1 G2,
      G = (ctx_hide G1) §& G2 ->
      property (G1 §& G2) Go e a b.

Definition UnhidingTInd (A: Set) (t: Typing A) := UnhidingInd obj_typing.

Definition UnhidingDInd (A: Set) (t: DecTyping A) := UnhidingInd obj_dec_typing.

Definition UnhidingIncapInd (_ : ReferenceIncapacitate) :=
  UnhidingInd obj_ref_incap.

Definition UnhidingCapbndInd (C : typ_refcap_label) (_ : CapabilityBound C) :=
  UnhidingInd obj_cap_bnd.

Definition HidingInd (A B: Set) (property: TypingProperty A B) :=
  forall G Go e (a: A) (b: B),
    property G Go e a b ->
    forall G1 G2,
      G = G1 §& G2 ->
      property ((ctx_hide G1) §& G2) Go e a b.

Definition HidingTInd (A: Set) (t: Typing A) := HidingInd obj_typing.

Definition HidingDInd (A: Set) (t: DecTyping A) := HidingInd obj_dec_typing.

Definition HidingIncapInd (_ : ReferenceIncapacitate)
  := HidingInd obj_ref_incap.

Definition HidingCapbndInd (C : typ_refcap_label) (_ : CapabilityBound C)
  := HidingInd obj_cap_bnd.

Section WithTypingMode.

Context (typing_mode: Mode).

End WithTypingMode.
