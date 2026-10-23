# 101 — Security Noninterference — If-then-else — Medium

## Input

- `benchmarks/101__security-stlc__noninterference__if__medium/input/Task.v` — the single self-contained Rocq input file.

The base language is a locally nameless, recursion-free fragment of the SLam calculus with unit, sums, products, functions, security annotations, subtyping, and protection. Evaluation is left-to-right call-by-value, with security levels `Low` and `High`.

The feature configuration adds a primitive if-then-else construct. Booleans use the existing sum of two unit types. Only the selected branch is evaluated, and its result is protected by the condition's indirect-reader level.

## Target Theorem

```coq
Theorem noninterference : forall (C : program_context) (t1 t2 : tm)
    (T_secret T_result : ty),
  has_type empty t1 T_secret ->
  has_type empty t2 T_secret ->
  context_has_type C T_secret T_result ->
  ground T_result ->
  transparent T_result ->
  ~ flows_to (security_of T_secret).(indirect_reader)
      (security_of T_result).(indirect_reader) ->
  same_result (plug C t1) (plug C t2).
```

Two closed terms of the same secret type are placed in the same typed program context. If the result type is ground and transparent, and the secret's indirect-reader level cannot flow to the result's indirect-reader level, any two completed evaluations produce equal results after security annotations are erased. This is termination-insensitive noninterference.

## Expected Output

The input includes proved local helpers for fresh names, context lookup,
local closure, values, and basic reduction composition where applicable.
Design a logical relation and its context interpretation, and formulate
and prove the fundamental theorem needed for the target.

Prove `noninterference` in `Task.v`. You may add definitions and helper lemmas.
Keep the supplied definitions, proved lemmas, and target statement unchanged.
The final file must compile without Admitted, added axioms, or unsafe flags.
