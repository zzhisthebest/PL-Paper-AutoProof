Set Implicit Arguments.

Require Import LibExtra.

Require Import SyntaxClassDefs SyntaxClassProperties SyntaxClassLemmas SyntaxClassSubstLemmas.

Generalizable Variables A B.

Section SubstVars.

Context `{AS: AbstractSyntax A}.

End SubstVars.

Section SubstFresh.

Context `{SubstFresh A}.

End SubstFresh.

Section SubstVarsFv.

Context `{AS: AbstractSyntax A}.

Context {AFS: FvSubstCases AS}.

End SubstVarsFv.

Section OpenTwiceClosed.

Context `{AS: AbstractSyntax A}.

Context {OT: OpenTwice H}.

Context {SOC: SubstOpenCommut AS}.

Context {CA: Closing AS}.

End OpenTwiceClosed.

Section SubstVars.

Context `{AC: Closing A}.

Context {ACS: CloseSubst AC} {AFC: FvClose AC}  {AFS: FvSubstCases AS}.

Context {SC: SubstCommut AS}.

Context {SI: SubstId AS}.

Context {SF: SubstFresh AS}.

Context {ACU: CloseUnbound AC}.

Context {ASCC: SubstCloseCommut AC}.

Context {ASOC: SubstOpenClose AC}.

Context {ACC: CloseCommut AC}.

Context {AOC: OpenCommut H}.

Context {AOT: OpenTwice H}.

Context {ASOCo: SubstOpenCommut AS}.

End SubstVars.
