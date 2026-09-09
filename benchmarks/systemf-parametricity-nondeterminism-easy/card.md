# System F Parametricity — Non-Determinism — Easy

## Input

- `benchmarks/systemf-parametricity-nondeterminism-easy/input/Task.v` — the single self-contained Rocq input file.

The base language is locally nameless System F with function and universal types, term abstraction/application, and type abstraction/application.

Additional features: binary non-deterministic choice (`tm_choice`).

The file additionally supplies the logical relation formed by `value_relation` and `expression_relation`, together with its direct dependencies, and a proved fundamental theorem `binary_fundamental`. Only the target theorem remains unproved.

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

Complete `Task.v`: use the supplied proved fundamental theorem to prove the target theorem. The completed file must compile with Rocq and must not use `Admitted`, added axioms, unsafe flags, or changes to the supplied language definitions and theorem statements.
