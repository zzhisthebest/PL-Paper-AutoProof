# System F Refinement Type Safety — If — Easy

## Input

- `benchmarks/systemf-refinement-soundness-if-easy/input/Task.v` — the single self-contained Rocq input file.

The language is locally nameless System F with integers, addition, subtraction, multiplication, and partial division. Its refinement layer uses Boolean formulas, refinement function, existential, and polymorphic types, subtyping, and refinement typing. Division requires a nonzero divisor. The if-then-else feature adds Booleans and a Boolean conditional.

The file supplies the language syntax, call-by-value small-step semantics, core and refinement typing rules, and the target theorem. It supplies the logical relation (`denotes` and `evals_denotes`) and a proved fundamental theorem `SystemFRefinementIfSoundness.fundamental`.

## Target Theorem

```coq
Theorem never_stuck : forall (t t' : tm) (R : rty),
  has_rtype [] empty_rcontext t R ->
  multi t t' ->
  value t' \/ exists t'' : tm, t' --> t''.
```

Every state reachable from a closed refinement-typed program is a value or can take another step.

## Expected Output

Complete `Task.v`: use the supplied logical relation and proved fundamental theorem to prove the target theorem. The completed file must compile with Rocq and must not use `Admitted`, added axioms, unsafe flags, or changes to the supplied language definitions and theorem statements.
