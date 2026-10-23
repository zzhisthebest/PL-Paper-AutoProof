# 003 — STLC Strong Strong Normalization — None — Easy

## Input

- `benchmarks/003__stlc__strong-normalization__none__easy/input/Task.v` — the single self-contained Rocq input file.

The base language is locally nameless STLC with `Bool`, function types, variables, abstractions, applications, `true`, and `false`.

The feature configuration is the base language.

The file supplies the language syntax, call-by-value small-step semantics, typing rules, and target theorem.

## Target Theorem

```coq
Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
```

Every closed, well-typed term is strongly normalizing for the supplied call-by-value `step` relation: every reduction path is finite.

## Expected Output

The input includes all Medium support, proved substitution/opening,
typing and evaluation infrastructure, and a reference semantic framework.
The reference logical relation is `value_relation` and `expression_relation`.
Reference fundamental theorem statements are optional suggestions in comments.
Prove the core semantic cases and fundamental theorem using the reference
framework or another logical relation of your choice.

Prove `normalization` in `Task.v`. You may add definitions and helper lemmas.
Keep the supplied definitions, proved lemmas, and target statement unchanged.
The final file must compile without Admitted, added axioms, or unsafe flags.
