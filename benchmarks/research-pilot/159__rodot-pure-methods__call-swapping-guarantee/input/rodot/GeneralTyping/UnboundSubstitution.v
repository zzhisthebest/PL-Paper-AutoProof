Set Implicit Arguments.

Require Import Coq.Program.Equality.

Require Import DotTactics LibExtra.

Require Import AbstractSyntax TypingMode Equivalence GeneralTyping Weakening EWeakening Visibility.

Require Import Indep SubstCommon.

Class UnboundSubstitution {A B: Set} {AS: SubstVar A} {AF: FreeVar A} {BS: SubstVar B} {BF: FreeVar B}
    (property: TypingProperty A B) :=
  unbound_substitution_obj (ys: list var) (S: typ) G1 (xs: list var) G2 Go e (a: A) (b: B):
      property (G1 §& G2) Go e a b ->
      ctx_ok (G1 §& G2 §§& Go) ->
      length ys = length xs ->
      fresh (ctx_fv G1 \u fv_renv e \u (ctx_dom G1) \u (ctx_dom G2) \u (objctx_dom Go)) (length xs) xs ->
      property (G1 §& (subst_ctx_pvars xs ys G2)) (subst_objctx_pvars xs ys Go) e (subst_pvars xs ys a) (subst_pvars xs ys b) .

Section UnboundSubstitutionLemmata.

Context {A B: Set} {AS: SubstVar A} {AF: FreeVar A} {BS: SubstVar B} {BF: FreeVar B}
    {property: TypingProperty A B}{AW: UnboundSubstitution property}.

Context {AO: Openable A} {AAS: AbstractSyntax AO AF AS} {ASI: SubstId AAS} {ASC: SubstCommut AAS}  {ASF: SubstFresh AAS} {AFSC: FvSubstCases AAS}.

Context {BO: Openable B} {BAS: AbstractSyntax BO BF BS} {BSI: SubstId BAS} {BSC: SubstCommut BAS}  {BSF: SubstFresh BAS} {BFSC: FvSubstCases BAS}.

End UnboundSubstitutionLemmata.

Section UnboundSubstitutionTyLemmata.

Context {A: Set}{AS: SubstVar A}{AF: FreeVar A}{AT: Typing A}
    (AW: UnboundSubstitution AT).

End UnboundSubstitutionTyLemmata.

Definition UnboundSubstitutionInd (A B: Set) (su: SubstVar A)  (fa: FreeVar A) (sub: SubstVar B) (fb: FreeVar B) (property: TypingProperty A B) :=
  (forall G Go e (v: A) T,
    property G Go e v T ->
    forall G1 G2 xs ys,
      G = G1 §& G2 ->
      ctx_ok (G1 §& G2 §§& Go) ->
      length ys = length xs ->
      fresh (ctx_fv G1 \u fv_renv e \u (ctx_dom G1) \u (ctx_dom G2) \u (objctx_dom Go)) (length xs) xs ->
      property (G1 §& (subst_ctx_pvars xs ys G2)) (subst_objctx_pvars xs ys Go) e (subst_pvars xs ys v) (subst_pvars xs ys T)).

Definition UnboundSubstitutionEInd (A: Set) (t: TypingEquiv A) (su: SubstVar A) (FA: FreeVar A)  :=
  UnboundSubstitutionInd (su) FA (su) FA (fun G Go e (a b: A) => typing_equiv e a b).

Definition UnboundSubstitutionTInd (A: Set) (t: Typing A) (su: SubstVar A) (FA: FreeVar A)  :=
  UnboundSubstitutionInd (su) FA (TypSubstVar) (TypFreeVar) (obj_typing).

Definition UnboundSubstitutionIncapInd (_: ReferenceIncapacitate) :=
  UnboundSubstitutionInd TypSubstVar TypFreeVar TypSubstVar TypFreeVar obj_ref_incap.

Definition UnboundSubstitutionCapbndInd (C : typ_refcap_label) (_ : CapabilityBound C) :=
  UnboundSubstitutionInd TypSubstVar TypFreeVar TypSubstVar TypFreeVar obj_cap_bnd.

Definition UnboundSubstitutionDInd (A: Set) (t: DecTyping A) (su: SubstVar A) (FA: FreeVar A)  :=
  UnboundSubstitutionInd (su) FA (subst_dec) DecFreeVar (obj_dec_typing).

Section WithTypingMode.

Context {typing_mode: Mode}.

End WithTypingMode.
