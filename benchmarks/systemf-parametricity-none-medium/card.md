# System F Parametricity — None — Medium

## Input

- `benchmarks/systemf-parametricity-none-medium/input/Task.v` — the single self-contained Rocq input file.

The base language is locally nameless System F with function and universal types, term abstraction/application, and type abstraction/application.

The feature configuration is the base language.

This case uses the experimental LR-reconstruction Medium setting. The file supplies a proved fundamental theorem `binary_fundamental`, the complete proof of `polymorphic_identity_theorem_for_free`, and their auxiliary proofs. The LR definitions to reconstruct are `results_match`, `expression_lifting`, `value_relation`, `expression_relation`; their interfaces are marked with `BEGIN LR` / `END LR`. The proofs impose constraints on the reconstructed LR.

## Target Theorem

```coq
Theorem polymorphic_identity_theorem_for_free : forall t,
  has_type [] empty t
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) ->
  forall U v,
    wf_ty [] U ->
    value v ->
    has_type [] empty v U ->
    tm_app (tm_tapp t U) v -->* v.
```

Every closed term of type `forall X, X -> X`, instantiated at a closed well-formed type `U` and applied to a closed value `v : U`, can evaluate to `v`. In cases with non-deterministic choice, the conclusion asserts the existence of this reduction path.

## Expected Output

Complete only the marked LR blocks in `Task.v`, replacing each admitted placeholder with a concrete definition. Keep the displayed interfaces and every supplied statement and proof script unchanged. A placeholder declared with `Definition` may be implemented with `Fixpoint` or `Equations`, including any required termination obligations within that block. The completed file must compile with Rocq without admissions, added axioms, unsafe flags, or equivalent escape hatches. The supplied downstream proofs are not expected to check while the LR placeholders remain opaque.
