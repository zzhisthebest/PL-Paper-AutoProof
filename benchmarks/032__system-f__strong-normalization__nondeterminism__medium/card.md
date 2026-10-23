# 032 — System F Strong Strong Normalization — Non-Determinism — Medium

## Input

- `benchmarks/032__system-f__strong-normalization__nondeterminism__medium/input/Task.v` — the single self-contained Rocq input file.

The base language is locally nameless System F with function and universal types, term abstraction/application, and type abstraction/application.

Additional features: binary non-deterministic choice (`tm_choice`).

The file supplies the language syntax, call-by-value small-step semantics, typing rules, and target theorem.

## Target Theorem

```coq
Theorem normalization : forall t T,
  has_type [] empty t T ->
  strongly_normalizing t.
```

Every closed, well-typed term is strongly normalizing for the supplied call-by-value `step` relation: every reduction path is finite.

## Expected Output

The input includes proved local helpers for fresh names, context lookup,
local closure, values, and basic reduction composition where applicable.
Design a logical relation and its context interpretation, and formulate
and prove the fundamental theorem needed for the target.

Prove `normalization` in `Task.v`. You may add definitions and helper lemmas.
Keep the supplied definitions, proved lemmas, and target statement unchanged.
The final file must compile without Admitted, added axioms, or unsafe flags.
