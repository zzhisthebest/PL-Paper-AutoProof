Set Implicit Arguments.

Require Import Coq.Program.Equality.

Require Import DotTactics LibExtra.

Require Import AbstractSyntax TypingMode Equivalence GeneralTyping Weakening EWeakening Visibility.

Require Import Indep TypingContext.

Section WithTypingMode.

Context {typing_mode: Mode}.

Class Sealing (A B: Set) (AO: Sealable A) (BO: Sealable B) (property: TypingProperty A B) (n: nat) :=
  sealing_obj G Go e (v: A) T x:
    property G Go e v T ->
    property (seal x G) (seal x Go) e (seal x v) (seal_rec n x T).

Definition SealingInd (A B: Set) (AO: Sealable A) (BO: Sealable B) (property: TypingProperty A B) (n: nat) :=
  (forall G Go e (v: A) T,
    property G Go e v T ->
      forall x,
      property (seal x G) (seal x Go) e (seal x v) (seal_rec n x T)).

Definition SealingEInd (A: Set) (AO: Sealable A) (t: TypingEquiv A) :=
  SealingInd AO AO (fun G Go e (a b: A) => typing_equiv e a b) 0.

Definition SealingTInd (A: Set) (AO: Sealable A) (t: Typing A) :=
  SealingInd AO TypSealable obj_typing 0.

Definition SealingDInd (A: Set) (AO: Sealable A) (t: DecTyping A) :=
  SealingInd AO DecSealable obj_dec_typing 0.

Definition SealingIncapInd (t: ReferenceIncapacitate) :=
  SealingInd TypSealable TypSealable obj_ref_incap 0.

Definition SealingCapbndInd (C : typ_refcap_label) (_ : CapabilityBound C)  :=
  SealingInd TypSealable TypSealable obj_cap_bnd 1.

Definition SealingIndN (A B: Set) (AO: Sealable A) (BO: Sealable B) (property: TypingProperty A B) :=
  (forall G Go e (v: A) T,
    property G Go e v T ->
      forall n x,
      property (seal x G) (seal x Go) e (seal_rec n x v) (seal_rec n x T)).

End WithTypingMode.
