Require Import Infrastructure.

Require Import SourceProperty.

Definition kleene_equiv t1 t2 :=
  exists k, t1 ->* (exp_lit k) /\ t2 ->* (exp_lit k).

Definition ctx_equiv Δ Γ E1 E2 A := forall e1 e2 dir dir' C c,
    has_type Δ Γ E1 dir A e1 ->
    has_type Δ Γ E2 dir A e2 ->
    CTyp C Δ Γ dir A nil nil dir' sty_nat c ->
    kleene_equiv (appctx c e1) (appctx c e2).

Theorem coherence : forall Δ Γ E A,
    ctx_equiv Δ Γ E E A.
