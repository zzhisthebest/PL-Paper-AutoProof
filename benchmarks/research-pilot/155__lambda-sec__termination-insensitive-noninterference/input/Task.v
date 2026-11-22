From stdpp Require Import relations.

From logrel_ifc.lambda_sec Require Export lang typing.

From logrel_ifc.lambda_sec Require Import lattice.

Section soundness.

Context `{SecurityLattice label}.

Theorem soundness_tini (e : expr) v1 v2 v1' v2' ℓ ℓ' :
    ℓ' ⋢ ζ →
    ℓ  ⊑ ζ →
    [TBool @ (LLabel ℓ')] # (LLabel ℓ) ⊢ₜ e : TBool @ (LLabel ℓ) →
    [] # (LLabel ℓ) ⊢ₜ #v1 : TBool @ (LLabel ℓ') →
    [] # (LLabel ℓ) ⊢ₜ #v2 : TBool @ (LLabel ℓ') →
    ((∃ σ1, rtc pstep (e.[# v1/], ∅) (# v1', σ1)) ∧
     (∃ σ2, rtc pstep (e.[# v2/], ∅) (# v2', σ2))) →
    v1' = v2'.

End soundness.
