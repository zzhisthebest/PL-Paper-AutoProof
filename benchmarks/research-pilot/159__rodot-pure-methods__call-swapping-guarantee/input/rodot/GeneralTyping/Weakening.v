Set Implicit Arguments.

Require Import LibExtra DotTactics.

Require Import AbstractSyntax GeneralTyping TypingContext Env.

Class Weakening (A B: Set) (property: TypingProperty A B) :=
  weaken G1 G2 G3 Go e (ds: A) T:
    (property (G1 §& G3) Go e ds T ->
     ctx_weakens G2 ->
     ctx_ok (G1 §& G2) ->
     property (G1 §& G2 §& G3) Go e ds T).

Section WeakeningLemmata.

Context {A B: Set} {P: TypingProperty A B} {AW: Weakening P}.

End WeakeningLemmata.

Section WeakeningTyLemmata.

Context {A: Set}{AT: Typing A}{AW: Weakening AT}.

End WeakeningTyLemmata.

Section WeakeningSubtyLemmata.

Context {A : Set} {AS : Subtyping} {AW : Weakening AS}.

End WeakeningSubtyLemmata.

Definition WeakeningIndCondition (G: ctx) (property: ctx->Prop) := (
  (property G) ->
  forall G1 G2 G3,
    (G = G1 §& G3 ->
     ctx_weakens G2 ->
     ctx_ok (G1 §& G2) ->
     (property (G1 §& G2 §& G3)))
).

Definition WeakeningInd (A B: Set) (property: TypingProperty A B) :=
  (forall (G:ctx) (Go: objctx) (e:renv) (v : A) T, (WeakeningIndCondition G (fun G => property G Go e v T))).

Definition WeakeningTInd (A: Set) (t: Typing A) := WeakeningInd (obj_typing).

Definition WeakeningDInd (A: Set) (t: DecTyping A) := WeakeningInd (obj_dec_typing).

Definition WeakeningIncapInd (_ : ReferenceIncapacitate) :=
  WeakeningInd obj_ref_incap.

Definition WeakeningCapbndInd (C : typ_refcap_label) (_ : CapabilityBound C) :=
  WeakeningInd obj_cap_bnd.
