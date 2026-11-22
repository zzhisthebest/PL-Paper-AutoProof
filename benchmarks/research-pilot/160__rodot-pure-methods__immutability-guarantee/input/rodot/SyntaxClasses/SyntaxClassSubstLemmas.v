Set Implicit Arguments.

Require Import LibExtra.

Require Import SyntaxClassDefs SyntaxClassProperties SyntaxClassLemmas.

Generalizable Variables A B.

Section Subst_env.

Context `{AS: AbstractSyntax A}.

End Subst_env.

Section About_SubstFresh.

Context `{SubstFresh A}.

End About_SubstFresh.

Section About_SubstOpenCommut.

Context `{SubstOpenCommut}.

End About_SubstOpenCommut.

Section SubstOpenClose.

Context `{SubstOpenClose}.

End SubstOpenClose.

Section CloseSubst.

Context `{CloseSubst}.

End CloseSubst.

Section SubstCloseCommut.

Context `{SubstCloseCommut}.

End SubstCloseCommut.

Section About_FvSubstCases.

Context `{FvSubstCases}.

End About_FvSubstCases.

Section Subst_Commut.

Context `{SubstCommut}.

End Subst_Commut.

Section SubstId.

Context `{AS: AbstractSyntax}.

Context {SI: SubstId AS}.

End SubstId.

Section Subst.

Context `{AS: AbstractSyntax}.

Context {SI: SubstId AS}.

Context {SC: SubstCommut AS}.

Context {SF: SubstFresh AS}.

Context {FSC: FvSubstCases AS}.

End Subst.

Section SubstClose.

Context `{AS: AbstractSyntax}.

Context {SI: SubstId AS}.

Context {SC: SubstCommut AS}.

Context {SF: SubstFresh AS}.

Context {FSC: FvSubstCases AS}.

Context {CA: Closing AS}.

Context {SCC: SubstCloseCommut CA}.

End SubstClose.

Section OpenTwiceClosed.

Context `{AS: AbstractSyntax A}.

Context {OT: OpenTwice H}.

Context {SOC: SubstOpenCommut AS}.

Context {CA: Closing AS}.

End OpenTwiceClosed.

Section OpenClose.

Context `{AS: AbstractSyntax A}.

Context {OT: OpenTwice H}.

Context {OC: OpenCommut H}.

Context {SOC: SubstOpenCommut AS}.

Context {CA: Closing AS}.

Context {SOCA: SubstOpenClose CA}.

End OpenClose.
