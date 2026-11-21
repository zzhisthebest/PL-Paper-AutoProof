Require Export Qual.typing.

Set Implicit Arguments.

Open Scope grade_scope.

Fixpoint erasure (phi : grade) (a:tm)  : tm :=
  match a with
  | a_TyUnit => a_TyUnit
  | a_TmUnit => a_TmUnit
  | (a_Pi psi A B) => a_Pi psi (erasure phi A) (erasure phi B)
  | (a_Abs psi A a) =>
      if q_leb q_Top phi then
        a_Abs psi (erasure phi A) (erasure phi a)
      else
        a_Abs psi a_TmUnit (erasure phi a)
  | (a_App a psi b) =>
      if q_leb psi phi then
        a_App (erasure phi a) psi (erasure phi b)
      else
        a_App (erasure phi a) psi a_TmUnit
  | (a_Type s) => a_Type s
  | (a_Var_b nat) => a_Var_b nat
  | (a_Var_f x) => a_Var_f x
  | (a_Sum A1 A2) => a_Sum (erasure phi A1) (erasure phi A2)
  | (a_Inj1 a) => a_Inj1 (erasure phi a)
  | (a_Inj2 a) => a_Inj2 (erasure phi a)
  | (a_Case psi a b1 b2) => a_Case psi (erasure phi a) (erasure phi b1) (erasure phi b2)
  | (a_WSigma psi A B) => a_WSigma psi (erasure phi A) (erasure phi B)
  | (a_WPair a psi b) =>
      if q_leb psi phi then
        a_WPair (erasure phi a) psi (erasure phi b)
      else
        a_WPair a_TmUnit psi (erasure phi b)
  | (a_LetPair psi a b) => a_LetPair psi (erasure phi a) (erasure phi b)
  | (a_SSigma psi A B) => a_SSigma psi (erasure phi A) (erasure phi B)
  | (a_SPair a psi b) =>
      if q_leb psi phi then
        a_SPair (erasure phi a) psi (erasure phi b)
      else
        a_SPair a_TmUnit psi (erasure phi b)
  | (a_Proj1 psi a) => a_Proj1 psi (erasure phi a)
  | (a_Proj2 psi a) => a_Proj2 psi (erasure phi a)
end.

Theorem CEq_GEq_respects_Step :
  (forall P phi phi0 b1 b1',
  CEq P phi phi0 b1 b1' ->  forall b2, Step b1 b2 ->
       exists b2', (phi0 <= phi -> Step b1' b2') /\ CEq P phi phi0 b2 b2') /\
  (forall P phi b1 b1',
  GEq P phi b1 b1' -> forall b2, Step b1 b2 ->
       exists b2', Step b1' b2' /\ GEq P phi b2 b2').

Theorem Erasure_Indistinguishability :
  (forall P phi psi a, CGrade P phi psi a -> CEq P phi psi a (erasure phi a)) /\
  (forall P phi a, Grade P phi a -> GEq P phi a (erasure phi a)).
