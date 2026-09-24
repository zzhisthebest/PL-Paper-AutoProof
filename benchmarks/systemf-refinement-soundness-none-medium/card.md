# System F Refinement Type Safety — None — Medium

## Input

- `benchmarks/systemf-refinement-soundness-none-medium/input/Task.v` — the single self-contained Rocq input file.

The language is locally nameless System F with integers, addition, subtraction, multiplication, and partial division. Its refinement layer uses Boolean formulas, refinement function, existential, and polymorphic types, subtyping, and refinement typing. Division requires a nonzero divisor. The feature configuration is the base language.

This case uses the experimental LR-reconstruction Medium setting. The file supplies a proved fundamental theorem `fundamental`, the complete proof of `never_stuck`, and their auxiliary proofs. The LR definitions to reconstruct are `denotes` and `evals_denotes`; their interfaces are marked with `BEGIN LR` / `END LR`. The proofs impose constraints on the reconstructed LR.

## Target Theorem

```coq
Theorem never_stuck : forall (t t' : tm) (R : rty),
  has_rtype [] empty_rcontext t R ->
  multi t t' ->
  value t' \/ exists t'' : tm, t' --> t''.
```

Every state reachable from a closed refinement-typed program is a value or can take another step.

## Expected Output

Complete only the marked LR blocks in `Task.v`, replacing each admitted placeholder with a concrete definition. Keep the displayed interfaces and every supplied statement and proof script unchanged. A placeholder declared with `Definition` may be implemented with `Fixpoint` or `Equations`, including any required termination obligations within that block. The completed file must compile with Rocq without admissions, added axioms, unsafe flags, or equivalent escape hatches. The supplied downstream proofs are not expected to check while the LR placeholders remain opaque.
