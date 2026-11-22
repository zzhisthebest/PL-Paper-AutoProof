Require Import Qual.typing.

Set Implicit Arguments.
Open Scope grade_scope.

Theorem Typing_preservation :
  forall W psi a A, Typing W psi a A -> Ctx W ->
  forall b, Step a b -> Typing W psi b A.

Theorem Typing_progress :
  forall psi a A, Typing nil psi a A -> (exists a', Step a a') \/ Value a.
