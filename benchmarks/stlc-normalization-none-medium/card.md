# STLC Strong Normalization — None — Medium

## Input

- `benchmarks/stlc-normalization-none-medium/input/Task.v` — the single self-contained Rocq input file.

The base language is locally nameless STLC with `Bool`, function types, variables, abstractions, applications, `true`, and `false`.

No additional language feature is included.

The file additionally supplies the unary logical relation, its direct dependencies, and the statement of the fundamental theorem. The fundamental theorem and target theorem remain unproved.

## Target Theorem

```coq
Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
```

Every closed, well-typed term is strongly normalizing for the supplied call-by-value `step` relation: every reduction path is finite.

## Expected Output

Complete `Task.v`: prove the stated fundamental theorem for the supplied logical relation, then prove the target theorem. The completed file must compile with Rocq and must not use `Admitted`, added axioms, unsafe flags, or changes to the supplied language definitions and theorem statements.
