# System F Refinement Type Safety — Recursion — Easy

## Input

- `benchmarks/systemf-refinement-soundness-recursion-easy/input/Task.v` — the single self-contained Rocq input file.

The language is locally nameless System F with integers, addition, subtraction, multiplication, and partial division. Its refinement layer uses Boolean formulas, refinement function, existential, and polymorphic types, subtyping, and refinement typing. Division requires a nonzero divisor. Recursive functions are checked by a nonnegative, strictly decreasing integer metric, with an integer zero test for branching.

The file supplies the language syntax, call-by-value small-step semantics, core and refinement typing rules, and the target theorem.

## Target Theorem

```coq
Theorem never_stuck : forall (t t' : tm) (R : rty),
  has_rtype [] empty_rcontext t R ->
  multi t t' ->
  value t' \/ exists t'' : tm, t' --> t''.
```

Every state reachable from a closed refinement-typed program is a value or can take another step.

## Expected Output

The input includes all Medium support, proved substitution/opening,
typing and evaluation infrastructure, and a reference semantic framework.
The reference logical relation is `denotes` and `evals_denotes`.
Reference fundamental theorem statements are optional suggestions in comments.
Prove the core semantic cases and fundamental theorem using the reference
framework or another logical relation of your choice.

Prove `never_stuck` in `Task.v`. You may add definitions and helper lemmas.
Keep the supplied definitions, proved lemmas, and target statement unchanged.
The final file must compile without Admitted, added axioms, or unsafe flags.
