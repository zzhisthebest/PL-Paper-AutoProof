From strictness.cbpv Require Import semtyping.

Theorem function_soundness : forall n (γ : attrs n) (Γ : context n) (ρ : env n) M A B q,
  semtyping.ρ_ok ρ Γ ->
  CWt γ Γ M (CAbs q A B) ->
  exists mOuter mInner γInner ρ' M' HInner,
  EvalComp γ ρ M (Closure mOuter mInner (down_env_until γInner mOuter HInner) ρ' M') /\
  forall W, semtyping.LR A W ->
  exists T, EvalComp (q .: γInner) ((mOuter W↓ W) .: ρ') M' T.
