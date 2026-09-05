# STLC Strong Normalization — If-Then-Else — Easy

## Input

- `benchmarks/stlc-normalization-if-easy/input/Task.v` — the single self-contained Rocq input file.

The base language is locally nameless STLC with `Bool`, function types, variables, abstractions, applications, `true`, and `false`.

Additional features: `if`-then-`else` over the existing Boolean terms.

The file additionally supplies the logical relation, its direct dependencies, and a proved fundamental theorem. Only the target theorem remains unproved.

## Target Theorem

```coq
Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
```

Every closed, well-typed term is strongly normalizing for the supplied call-by-value `step` relation: every reduction path is finite.

## Expected Output

Complete `Task.v`: use the supplied proved fundamental theorem to prove the target theorem. The completed file must compile with Rocq and must not use `Admitted`, added axioms, unsafe flags, or changes to the supplied language definitions and theorem statements.
