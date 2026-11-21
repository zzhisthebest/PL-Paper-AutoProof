Set Implicit Arguments.

Require Import LibExtra.

Require Import SyntaxClassDefs SyntaxClassProperties SyntaxClassLemmas SyntaxClassSubstLemmas SyntaxClassSubstVarsLemmas.

Generalizable Variables A B.

Section Subst_PVars.

Context `{AS: SubstVar}.

Context `{AF: FreeVar A}.

End Subst_PVars.

Section Subst_PVars.

Context `{AS: AbstractSyntax}.

Context {SF: SubstFresh AS}.

Context {FS: FvSubstCases AS}.

Context {SC: SubstCommut AS}.

Context {SI: SubstId AS}.

Context {OC: OpenCommut H}.

Context {SOC: SubstOpenCommut AS}.

End Subst_PVars.
