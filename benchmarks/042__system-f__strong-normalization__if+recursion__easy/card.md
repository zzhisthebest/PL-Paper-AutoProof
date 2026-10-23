# 042 — System F Strong Strong Normalization — If-Then-Else + Recursion — Easy

## Input

- `benchmarks/042__system-f__strong-normalization__if+recursion__easy/input/Task.v` — the single self-contained Rocq input file.

The base language is locally nameless System F with function and universal types, term abstraction/application, and type abstraction/application.

Additional features: native `Bool`, `true`, `false`, and `if`-then-`else`; `Nat` and System T-style primitive recursion (`tm_natrec`), not an unrestricted fixpoint.

The file supplies the language syntax, call-by-value small-step semantics, typing rules, and target theorem.

## Target Theorem

```coq
Theorem normalization : forall t T,
  has_type [] empty t T ->
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
