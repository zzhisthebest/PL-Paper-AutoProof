# Security noninterference with natural-number recursion

This directory extends the recursion-free security language with labeled natural
numbers, successor, and a System T-style natural-number recursor. It is a
self-contained development: its imports stay within this directory and Stdlib.
This is our extension of the SLam-inspired fragment, not a reproduction of
the paper's general recursion.

## Language

- `Ty_Nat kappa` is the type of natural numbers with security `kappa`.
- `tm_nat n kappa` is a labeled natural-number value.
- `tm_succ t r` evaluates a natural-number expression, checks reader access,
  and protects its successor with the number's indirect-reader label.
- `tm_natrec count base step_function r` evaluates these three arguments in
  that order. The count is a runtime expression, not a fixed Rocq parameter.
  The step function has type `Nat_public -> T -> T`, with public arrow labels;
  it receives the predecessor and the recursively computed result. `T` may
  contain functions or secret components.

After the arguments become values, the recursor checks access to the count and
reduces to its finite expansion under the count's indirect-reader protection.
`natrec_unroll` defines that expansion:

```text
unroll 0 base step = base
unroll (n+1) base step = step n (unroll n base step)
```

The small-step semantics expands the finite recursion in one administrative
step; application evaluation remains call-by-value. Every recursive occurrence
uses the predecessor. This is structural recursion, not an unrestricted fixpoint.
The function body can use, ignore, or compute with both arguments.

The result type is `ty_protect count_security.indirect_reader T`.
Consequently, different secret counts may compute different secret results, but
cannot make those differences public. Merely guaranteeing termination would
not enforce this restriction.

## Theorem and proof

`Noninterference.v` retains the same target statement and assumptions as the
base version, over the extended syntax, typing, evaluation, and program
contexts. Ground result types now also include natural numbers. Program
contexts can place their hole in the count, base, or step argument, as well as
under any existing constructor.

The LR compares observable natural numbers for equality. The recursor proof
splits according to visibility of the count:

- Visible counts must agree, and `unroll_related` proves compatibility by
  induction on the count.
- Hidden counts may differ. The protected result is related using the
  hidden-expression lemma and preservation of its underlying type.

`fundamental_expressions` and `noninterference` have complete proofs. No new
premise assumes that a program already satisfies noninterference or that a
particular computation terminates.

## Checks

`Examples.v` verifies a count computed at runtime (`succ 1`, labeled secret),
actual evaluation to the protected result `2`, and a context whose secret
recursive computation changes with the input while its public output stays `7`.
The output example is also proved to evaluate, so it is not a vacuous use of
termination-insensitive equality.

`checks/ProofAudit.v` reports that preservation, the fundamental theorem,
noninterference, and the examples are closed under the global context.
All files compile with Rocq; the compiled audit is checked with `rocq check`.
The three benchmark exports are `benchmarks/security-noninterference-recursion-{hard,medium,easy}`.
They are generated and validated with
`python scripts/generate_noninterference_cases.py --feature recursion`.
