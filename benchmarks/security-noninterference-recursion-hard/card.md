# Security Noninterference — Recursion — Hard

## Input

- `benchmarks/security-noninterference-recursion-hard/input/Task.v` — the single self-contained Rocq input file.

The base language is a locally nameless, recursion-free fragment of the SLam calculus with unit, sums, products, functions, security annotations, subtyping, and protection. Evaluation is left-to-right call-by-value, with security levels `Low` and `High`.

The feature configuration adds security-labeled natural numbers, successor, and System T-style natural-number recursion. The recursion count is evaluated at runtime; each step receives the predecessor and the previous result. The result is protected by the count's indirect-reader level.

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

Complete `Task.v`: construct a logical relation, formulate and prove its fundamental theorem, and prove the target theorem. The completed file must compile with Rocq and must not use `Admitted`, added axioms, unsafe flags, or changes to the supplied language definitions and theorem statements.
