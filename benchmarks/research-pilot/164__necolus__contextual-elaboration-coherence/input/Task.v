Require Import Metalib.Metatheory.

Require Import Observations Infrastructure target_inf.

Definition ctx_equiv Γ E1 E2 A := forall e1 e2 dir dir' C c,
    has_type Γ E1 dir A e1 ->
    has_type Γ E2 dir A e2 ->
    CTyp C Γ dir A nil dir' styp_nat c ->
    kleene_equiv (appctx c e1) (appctx c e2).

Theorem coherence_thm : forall Γ E A,
    ctx_equiv Γ E E A.
