Set Implicit Arguments.

Require Import Coq.Program.Equality.

Require Import DotTactics LibExtra.

Require Import AbstractSyntax TypingMode Equivalence GeneralTyping Weakening EWeakening Visibility.

Require Import Substitution.

Section WithTypingMode.

Context {typing_mode: Mode}.

Section Renaming.

Context {A: Set} {AO: Openable A} {AF: FreeVar A} {AT: Typing A} {AS: SubstVar A}
  {AX: AbstractSyntax AO AF AS}
  {AI: SubstIntro AX} {AW: Substitution AS subst_var AT}{AWE: EWeakening (obj_typing)}.

End Renaming.

End WithTypingMode.
