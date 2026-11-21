Require Import Language.

(* Session types *)

CoInductive session_type :=
  | SendTB n : (fin n -> type) -> (fin n -> session_type) -> session_type
  | RecvTB n : (fin n -> type) -> (fin n -> session_type) -> session_type
  | EndTB : session_type.


(* The original artifact obtains this equality instance from its Leibniz OFE. *)
Global Instance payload_type_equiv : Equiv type := eq.

Global Instance finvec_equiv `{Equiv T} n : Equiv (fin n -> T) := λ f g, ∀ i, f i ≡ g i.

CoInductive session_type_equiv : Equiv session_type :=
  | cteq_EndT : EndTB ≡ EndTB
  | cteq_SendT n t1 t2 f1 f2 : t1 ≡ t2 -> f1 ≡ f2 -> SendTB n t1 f1 ≡ SendTB n t2 f2
  | cteq_RecvT n t1 t2 f1 f2 : t1 ≡ t2 -> f1 ≡ f2 -> RecvTB n t1 f1 ≡ RecvTB n t2 f2.
Global Existing Instance session_type_equiv.

Parameter session_type_extensionality : ∀ σ1 σ2 : session_type, σ1 ≡ σ2 -> σ1 = σ2.

(*
  Coq's default notion of equality is not good enough for coinductive types:
   the default equality is syntactic equality and not extensional equality.
   We add an axiom to make equality extensional.
   See https://coq.inria.fr/refman/language/core/coinductive.html:
   "More generally, as in the case of positive coinductive types,
   it is consistent to further identify extensional equality of coinductive
   types with propositional equality"
   Such an axiom is similar to functional extensionality, but for coinductive types.
*)

CoFixpoint dual (σ : session_type) : session_type :=
  match σ with
  | SendTB n ts σs => RecvTB n ts (dual ∘ σs)
  | RecvTB n ts σs => SendTB n ts (dual ∘ σs)
  | EndTB => EndTB
  end.

(* Interpretation of session types into linear lambda calculus types *)

CoFixpoint toL (σ : session_type) : type :=
  match σ with
  | SendTB n ts σs => FunT Lin (SumT n (λ i, PairT (toL (dual $ σs i)) (ts i))) UnitT
  | RecvTB n ts σs => FunT Lin UnitT (SumT n (λ i, PairT (toL (σs i)) (ts i)))
  | EndTB => FunT Lin UnitT UnitT
  end.

(* Session type operations in terms of binary barriers *)

Definition SendB e1 i e2 :=
    LetPair (Pair e1 e2) (Fun "x" (Fun "y"
      (Fork (Fun "z" (App (Var "x") (Sum i (Pair (Var "z") (Var "y")))))))).
Definition RecvB e := App e Unit.
Definition ForkB e := Fork e.
Definition CloseB (e : expr) := App e Unit.
