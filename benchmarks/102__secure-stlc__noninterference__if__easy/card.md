# 102 — Secure STLC Noninterference — If-then-else — Easy

## Input

- `benchmarks/102__secure-stlc__noninterference__if__easy/input/Task.v` — the single self-contained Rocq input file.

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

The input includes all Medium support, proved substitution/opening,
typing and evaluation infrastructure, and a reference semantic framework.
The reference logical relation is `value_relation` and `expression_relation`,
specialized to the Low observer without an erased-typing obligation.
Reference fundamental theorem statements are optional suggestions in comments.
Prove the core semantic cases and fundamental theorem using the reference
framework or another logical relation of your choice.

Prove `noninterference` in `Task.v`. You may add definitions and helper lemmas.
Keep the supplied definitions, proved lemmas, and target statement unchanged.
The final file must compile without Admitted, added axioms, or unsafe flags.
