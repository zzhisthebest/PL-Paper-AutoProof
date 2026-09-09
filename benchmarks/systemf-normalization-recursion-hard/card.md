# System F Strong Normalization — Recursion — Hard

## Input

- `benchmarks/systemf-normalization-recursion-hard/input/Task.v` — the single self-contained Rocq input file.

The base language is locally nameless System F with function and universal types, term abstraction/application, and type abstraction/application.

Additional features: `Nat` and System T-style primitive recursion (`tm_natrec`), not an unrestricted fixpoint.

The file supplies the language syntax, call-by-value small-step semantics, typing rules, and target theorem.

## Target Theorem

```coq
Theorem normalization : forall t T,
  has_type [] empty t T ->
  strongly_normalizing t.
```

Every closed, well-typed term is strongly normalizing for the supplied call-by-value `step` relation: every reduction path is finite.

## Expected Output

Complete `Task.v`: construct an appropriate unary, type-indexed logical relation; define the term-variable context/substitution interpretation; prove the typing-rule obligations and a fundamental theorem; and prove the target theorem. The completed file must compile with Rocq and must not use `Admitted`, added axioms, unsafe flags, or changes to the supplied language definitions and theorem statements.
