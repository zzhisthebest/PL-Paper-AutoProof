# System F Strong Normalization — None — Medium

## Input

- `benchmarks/systemf-normalization-none-medium/input/Task.v` — the single self-contained Rocq input file.

The base language is locally nameless System F with function and universal types, term abstraction/application, and type abstraction/application.

The feature configuration is the base language.

This case uses the experimental LR-reconstruction Medium setting. The file supplies a proved fundamental theorem `fundamental`, the complete proof of `normalization`, and their auxiliary proofs. The LR definitions to reconstruct are `expression_lifting`, `value_relation`, `expression_relation`; their interfaces are marked with `BEGIN LR` / `END LR`. The proofs impose constraints on the reconstructed LR.

## Target Theorem

```coq
Theorem normalization : forall t T,
  has_type [] empty t T ->
  strongly_normalizing t.
```

Every closed, well-typed term is strongly normalizing for the supplied call-by-value `step` relation: every reduction path is finite.

## Expected Output

Complete only the marked LR blocks in `Task.v`, replacing each admitted placeholder with a concrete definition. Keep the displayed interfaces and every supplied statement and proof script unchanged. A placeholder declared with `Definition` may be implemented with `Fixpoint` or `Equations`, including any required termination obligations within that block. The completed file must compile with Rocq without admissions, added axioms, unsafe flags, or equivalent escape hatches. The supplied downstream proofs are not expected to check while the LR placeholders remain opaque.
