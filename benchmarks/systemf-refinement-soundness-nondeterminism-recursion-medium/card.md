# System F Refinement Type Safety — Nondeterminism-recursion — Medium

## Input

- `benchmarks/systemf-refinement-soundness-nondeterminism-recursion-medium/input/Task.v` — the single self-contained Rocq input file.

The language is locally nameless System F with integers, addition, subtraction, multiplication, and partial division. Its refinement layer uses Boolean formulas, refinement function, existential, and polymorphic types, subtyping, and refinement typing. Division requires a nonzero divisor. Binary choice may reduce to either operand; safety covers every branch. Recursive functions are checked by a nonnegative, strictly decreasing integer metric, with an integer zero test for branching. Strict metric comparisons must hold for all possible integer outcomes.

The file supplies the language syntax, call-by-value small-step semantics, core and refinement typing rules, and the target theorem. It supplies the logical relation: `denotes R v` interprets refinement types at values, and `evals_denotes R t` requires termination and constrains every reachable value.

## Target Theorem

```coq
Theorem never_stuck : forall (t t' : tm) (R : rty),
  has_rtype [] empty_rcontext t R ->
  multi t t' ->
  value t' \/ exists t'' : tm, t' --> t''.
```

Every state reachable from a closed refinement-typed program is a value or can take another step.

## Expected Output

Complete `Task.v`: use the supplied logical relation, define its context interpretation, prove a fundamental theorem, then prove the target theorem. The completed file must compile with Rocq and must not use `Admitted`, added axioms, unsafe flags, or changes to the supplied language definitions and theorem statements.
