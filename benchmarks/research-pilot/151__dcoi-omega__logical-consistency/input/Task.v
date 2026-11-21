Require Import imports conv par geq typing.

Module consistency
  (Import lattice : Lattice)
  (Import syntax : syntax_sig lattice)
  (Import par : par_sig lattice syntax)
  (Import ieq : geq_sig lattice syntax)
  (Import conv : conv_sig lattice syntax par ieq)
  (Import typing : typing_sig lattice syntax par ieq conv).

Theorem consistency a ℓ : ~nil ⊢ a ; ℓ ∈ tVoid.

End consistency.
