# STLC Strong Normalization — If-Then-Else + Non-Determinism + Recursion — Hard

## Input

- `benchmarks/stlc-normalization-if-nondeterminism-recursion-hard/input/Task.v` — the single self-contained Rocq input file.

The base language is locally nameless STLC with `Bool`, function types, variables, abstractions, applications, `true`, and `false`.

Additional features: `if`-then-`else` over the existing Boolean terms; binary non-deterministic choice (`tm_choice`); `Nat` and System T-style primitive recursion (`tm_natrec`), not an unrestricted fixpoint.

The file supplies the language syntax, call-by-value small-step semantics, typing rules, and target theorem.

## Target Theorem

```coq
Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
```

Every closed, well-typed term is strongly normalizing for the supplied call-by-value `step` relation: every reduction path is finite.

## Expected Output

Complete `Task.v`: construct an appropriate unary, type-indexed logical relation; define the term-variable context/substitution interpretation; prove the typing-rule obligations and a fundamental theorem; and prove the target theorem. The completed file must compile with Rocq and must not use `Admitted`, added axioms, unsafe flags, or changes to the supplied language definitions and theorem statements.
