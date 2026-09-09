# System F Strong Normalization — If-Then-Else — Medium

## Input

- `benchmarks/systemf-normalization-if-medium/input/Task.v` — the single self-contained Rocq input file.

The base language is locally nameless System F with function and universal types, term abstraction/application, and type abstraction/application.

Additional features: native `Bool`, `true`, `false`, and `if`-then-`else`.

The file additionally supplies the unary logical relation formed by `value_relation` and `expression_relation`, together with its direct definitional dependencies.

## Target Theorem

```coq
Theorem normalization : forall t T,
  has_type [] empty t T ->
  strongly_normalizing t.
```

Every closed, well-typed term is strongly normalizing for the supplied call-by-value `step` relation: every reduction path is finite.

## Expected Output

Complete `Task.v`: formulate and prove a fundamental theorem for the supplied logical relation, then prove the target theorem. The completed file must compile with Rocq and must not use `Admitted`, added axioms, unsafe flags, or changes to the supplied language definitions and theorem statements.
