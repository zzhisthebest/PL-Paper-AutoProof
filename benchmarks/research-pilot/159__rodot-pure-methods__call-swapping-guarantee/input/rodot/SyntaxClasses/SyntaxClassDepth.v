Set Implicit Arguments.

Require Import LibExtra.

Require Import SyntaxClassDefs SyntaxClassProperties SyntaxClassLemmas SyntaxClassSubstLemmas.

Generalizable Variables A B.

Section Open_depth.

Context `{AS: AbstractSyntax A}.

End Open_depth.

Section Subst_depth.

Context `{AS: AbstractSyntax A}.

End Subst_depth.

Section Close_depth.

Context `{AS: AbstractSyntax A} {Cl: Closing AS}.

End Close_depth.

Section About_OpenTwice.

Context `{OpenTwice}.

End About_OpenTwice.

Section About_OpenCommut.

Context `{OpenCommut A}.

End About_OpenCommut.

Section About_SubstOpenCommut.

Context `{SubstOpenCommut}.

End About_SubstOpenCommut.

Section Seal_depth.

Context `{AS: AbstractSyntax A} `{Sealable A}.

End Seal_depth.

Section About_ClosingSanity.

Section OpenClose.

Context `{OpenClose}.

End OpenClose.

Section CloseOpen.

Context `{CloseOpen}.

End CloseOpen.

Section CloseCommut.

Context `{CloseCommut A}.

End CloseCommut.

Section OpenCloseCommut.

Context `{OpenCloseCommut A}.

End OpenCloseCommut.

Section SubstOpenClose.

Context `{SubstOpenClose}.

End SubstOpenClose.

Section CloseSubst.

Context `{CloseSubst}.

End CloseSubst.

Section SubstCloseCommut.

Context `{SubstCloseCommut}.

End SubstCloseCommut.

End About_ClosingSanity.
