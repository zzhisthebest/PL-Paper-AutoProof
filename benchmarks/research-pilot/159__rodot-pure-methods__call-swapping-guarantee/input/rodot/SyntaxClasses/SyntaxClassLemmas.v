Set Implicit Arguments.

Require Import LibExtra.

Require Import SyntaxClassDefs SyntaxClassProperties.

Generalizable Variables A B.

Section Open.

Context `{AS: AbstractSyntax A}.

End Open.

Section Fv_env.

Context `{AS: AbstractSyntax A}.

End Fv_env.

Section About_OpenTwice.

Context `{OpenTwice}.

End About_OpenTwice.

Section About_OpenCommut.

Context `{OpenCommut A}.

End About_OpenCommut.

Section About_OpenInjective.

Context `{AS: AbstractSyntax A}.

Context {AO: OpenInjective AS}.

Context {AF: FvOpenCases AS}.

End About_OpenInjective.

Section About_FvOpenCases.

Context `{FvOpenCases}.

End About_FvOpenCases.

Section About_ClosingSanity.

Section OpenClose.

Context `{OpenClose}.

End OpenClose.

Section CloseOpen.

Context `{CloseOpen}.

End CloseOpen.

Section OpenCloseCommut.

Context `{OpenCloseCommut}.

End OpenCloseCommut.

Section CloseCommut.

Context `{CloseCommut A}.

End CloseCommut.

End About_ClosingSanity.

Section CloseVars.

Context `{AC: Closing A}.

Context {ACC: CloseCommut AC}.

Context {ACU: CloseUnbound AC}.

End CloseVars.

Section About_SealOpen.

Context `{SealOpen}.

End About_SealOpen.

Section About_SealClose.

Context `{SealClose}.

End About_SealClose.

Section SealOpenTwice.

Context `{AS: AbstractSyntax A}.

Context {OT: OpenTwice H}.

Context {OC: OpenCommut H}.

Context {SA: Sealable A}.

Context {SC: SealOpen AS SA}.

End SealOpenTwice.

Section SealOpenClosed.

Context `{AS: AbstractSyntax A}.

Context {OT: OpenTwice H}.

Context {OC: OpenCommut H}.

Context {SA: Sealable A}.

Context {SO: SealOpen AS SA}.

Context {SC: SealClosed AS SA}.

End SealOpenClosed.

Section OpenTwiceInv.

Context `{AS: AbstractSyntax A}.

Context {OT: OpenTwice H}.

Context {OC: OpenCommut H}.

Context {OTI: OpenTwiceInv AS}.

End OpenTwiceInv.

Section SealOpenClosedInv.

Context `{AS: AbstractSyntax A}.

Context {OT: OpenTwice H}.

Context {SOC: SubstOpenCommut AS}.

Context {CA: Closing AS}.

Context {SOCA: SubstOpenClose CA}.

Context {SA: Sealable A}.

Context {SO: SealOpen AS SA}.

Context {SC: SealClosed AS SA}.

Context {OSI: OpenSealInv AS SA}.

End SealOpenClosedInv.

Section AboutFvClose.

Context `{AS: AbstractSyntax A}.

Context {CA: Closing AS}.

Context {FC: FvClose CA}.

End AboutFvClose.

Section About_CloseUnbound.

Context `{AS: AbstractSyntax A}.

Context {C: Closing AS}.

Context {CU: CloseUnbound C}.

Context {CO: CloseOpen C}.

Context {SOC: SubstOpenClose C}.

End About_CloseUnbound.
