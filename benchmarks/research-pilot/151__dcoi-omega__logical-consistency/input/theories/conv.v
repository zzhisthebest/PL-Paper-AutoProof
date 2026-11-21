Require Import imports par geq.

Module Type conv_sig
  (Import lattice : Lattice)
  (Import syntax : syntax_sig lattice)
  (Import par : par_sig lattice syntax)
  (Import ieq : geq_sig lattice syntax).

Definition iconv Ξ ℓ a b := exists c0 c1, a ⇒* c0 /\ b ⇒* c1 /\ IEq Ξ ℓ c0 c1.

Definition conv Ξ a b := exists ℓ, iconv Ξ ℓ a b.

End conv_sig.
