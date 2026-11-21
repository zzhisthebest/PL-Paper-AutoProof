Set Implicit Arguments.

Require Import Context Equivalence Indep GeneralTyping TFree.

Require Import LibExtra AbstractSyntax TypingMode.

Require Import Coq.Program.Equality.

Require Import AbstractSyntax TypingMode GeneralTyping Equivalence Indep.

Section WithTypingMode.

Context (typing_mode: Mode).

Class TFreeDom (A B: Set) (AT: TFree A) (property: TypingProperty A B) :=
  tfree_dom G1 Go e (a: A) (b: B):
    property G1 Go e a b ->
    forall x,
    tfree x a ->
    x \in ctx_dom (G1 §§& Go).

Definition TFreeDomInd (A B: Set) (AT: TFree A) (property: TypingProperty A B) :=
  forall G Go e (a: A) (b: B),
    property G Go e a b ->
    forall x,
    tfree x a ->
    x \in ctx_dom (G §§& Go).

Definition TFreeDomTInd (A: Set) (AT: TFree A) (t: Typing A) := TFreeDomInd AT obj_typing.

Definition TFreeDomDInd (A: Set) (AT: TFree A) (t: DecTyping A) := TFreeDomInd AT obj_dec_typing.

End WithTypingMode.

Section WithTypingMode.

Context (typing_mode: Mode).

Context (Hmv: mode_visibility' typing_mode = mode_visibility_hide_method).

Class TFreeVisible (A B: Set) (AT: TFree A) (property: TypingProperty A B) :=
  tfree_visible G1 G2 Go e (a: A) (b: B):
    property ((ctx_hide G1) §& G2) Go e a b ->
    forall x,
    tfree x a ->
    x \in ctx_dom (G2 §§& Go).

Definition TFreeVisibleInd (A B: Set) (AT: TFree A) (property: TypingProperty A B) :=
  forall G Go e (a: A) (b: B),
    property G Go e a b ->
    forall G1 G2,
      G = (ctx_hide G1) §& G2 ->
      forall x,
      tfree x a ->
      x \in ctx_dom (G2 §§& Go).

Definition TFreeVisibleTInd (A: Set) (AT: TFree A) (t: Typing A) := TFreeVisibleInd AT obj_typing.

Definition TFreeVisibleDInd (A: Set) (AT: TFree A) (t: DecTyping A) := TFreeVisibleInd AT obj_dec_typing.

End WithTypingMode.
