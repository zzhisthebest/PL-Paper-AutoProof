# System F Parametricity — Recursion — Hard

## Input

- `benchmarks/systemf-parametricity-recursion-hard/input/Task.v` — the single self-contained Rocq input file.

The base language is locally nameless System F with function and universal types, term abstraction/application, and type abstraction/application.

Additional features: `Nat` and System T-style primitive recursion (`tm_natrec`), not an unrestricted fixpoint.

The file supplies the language syntax, call-by-value small-step semantics, typing rules, and target theorem. It does not supply a logical relation or fundamental theorem.

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

Complete `Task.v`: construct an appropriate binary, type-indexed logical relation; define the interpretations of type-variable and term-variable contexts; prove the typing-rule obligations and a fundamental theorem; and prove the target theorem. The completed file must compile with Rocq and must not use `Admitted`, added axioms, unsafe flags, or changes to the supplied language definitions and theorem statements.
