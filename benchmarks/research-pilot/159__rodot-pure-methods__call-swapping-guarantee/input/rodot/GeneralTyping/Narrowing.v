Set Implicit Arguments.

Require Import LibExtra DotTactics.

Require Import AbstractSyntax TypingMode GeneralTyping Subenvironments Weakening Env Indep Visibility TypingContext.

Section WithTypingMode.

Context {typing_mode: Mode}.

Class Narrow (A B: Set) (property: TypingProperty A B) :=
    narrow G G' Go e (a: A) (b: B):
      property G Go e a b ->
      ctx_ok (ctx_obj G' Go) ->

      e ⊢ G' ⪯ G ->
      property G' Go e a b.

End WithTypingMode.

Section WithTypingMode.

Context (typing_mode: Mode).

Section NarrowTyLemmata.

Context {A: Set}{AT: Typing A}{AW: Narrow AT}.

End NarrowTyLemmata.

Definition NarrowInd (A B: Set) (property: TypingProperty A B) :=
  (forall G Go e (x : A) T,
    (property G Go e x T -> forall G',
      ctx_ok (ctx_obj G' Go) ->
      e ⊢ G' ⪯ G ->
      property G' Go e x T)
  ).

Definition NarrowTInd (A: Set) (t: Typing A) := NarrowInd obj_typing.

Definition NarrowDInd (A: Set) (t: DecTyping A) := NarrowInd obj_dec_typing.

Definition NarrowIncapInd (_ : ReferenceIncapacitate)
  := NarrowInd obj_ref_incap.

Definition NarrowCapbndInd (C : typ_refcap_label) (_ : CapabilityBound C)
  := NarrowInd obj_cap_bnd.

End WithTypingMode.

Section WithTypingMode.

Context (typing_mode: Mode).

Class TyOpenImpliesTyBnd (A B: Set) (property: TypingProperty A B) :=
    ty_open_implies_ty_bnd T (ti: typ_indep_b 0 T) G1 y vk G2 Go e
                           (a: A) (b: B):
      property (G1 § y / vk ~ open y T §& G2) Go e a b ->
      ctx_weakens_hide G2 ->
      property (G1 § y / vk ~ typ_bnd T §& G2) Go e a b.

Section TyOpenImpliesTyBndLemmata.

Context (A: Set) (AT: Typing A) {AW: TyOpenImpliesTyBnd obj_typing}.

End TyOpenImpliesTyBndLemmata.

Definition TyOpenImpliesTyBndInd y vk T1 (A B: Set) (property: TypingProperty A B) :=
    (forall G Go e (t : A) T,
        property G Go e t T ->
        (forall G1 G2, ctx_weakens_hide G2 ->
              G = G1 § y / vk ~ open y T1 §& G2 ->
              property (G1 § y / vk ~ typ_bnd T1 §& G2) Go e t T)).

Definition TyOpenImpliesTyBndTInd y vk T1 (A: Set) (t: Typing A) :=
    TyOpenImpliesTyBndInd y vk T1 obj_typing.

Definition TyOpenImpliesTyBndDInd y vk T1 (A: Set) (t: DecTyping A) :=
    TyOpenImpliesTyBndInd y vk T1 obj_dec_typing.

Definition TyOpenImpliesTyBndIncapInd y vk T1
             (_ : ReferenceIncapacitate) :=
    TyOpenImpliesTyBndInd y vk T1 obj_ref_incap.

Definition TyOpenImpliesTyBndCapbndInd y vk T1
             (C : typ_refcap_label) (_ : CapabilityBound C) :=
    TyOpenImpliesTyBndInd y vk T1 obj_cap_bnd.

End WithTypingMode.
