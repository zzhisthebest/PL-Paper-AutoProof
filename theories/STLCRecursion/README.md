# STLC with natural-number recursion

This is a System T-style extension of STLC with `Nat`, `zero`, `succ`, and
primitive recursion. It keeps Boolean constants, locally nameless variables,
and deterministic left-to-right call-by-value evaluation. It does not add
unrestricted `fix`, recursive types, nondeterministic choice, or `if`.

## Recursion

`tm_natrec n base step` recurses over the natural number `n`.
If the result type is `T`, its arguments have types:

```text
n    : Nat
base : T
step : Nat -> T -> T
```

The step function receives the predecessor and the recursive result:

```text
rec zero     base step  --> base
rec (succ n) base step  --> step n (rec n base step)
```

These two reduction rules apply after `n` is a numeral and `base` and `step`
are values. The evaluation rules first evaluate `n`, then `base`, then `step`.
The recursive call uses the smaller numeral `n`. The result type `T` may be
a function type, not just `Nat`. Natural-number case analysis can also be
expressed by ignoring the recursive result; no separate `match` is needed.

## Files and reading order

1. `Syntax.v`: syntax, opening, substitution, local closure, values, reduction,
   and typing rules. Start with `Ty_Nat`, `tm_zero`, `tm_succ`, `tm_natrec`,
   `numeric_value`, the new reduction rules, and `T_Rec`.
2. `Examples.v`: addition (`two_plus_three`) and recursion returning a function
   (`function_result_typed`). Read the definitions first; proofs use later files.
3. `StlcProp.v`: local-closure lemmas, canonical forms, progress, and determinism.
4. `Infrastructure.v`: simultaneous substitution and its interaction with opening.
5. `Norm.v`: logical relation, recursion compatibility, fundamental theorem,
   termination, and normalization. The main new proof is
   `expression_rec_numeral`, by induction on the natural number.

`evaluation_terminates` proves that every term typable in the empty context
evaluates to a value. `normalization` proves `strongly_normalizing` for the
same terms, using determinism. This is normalization for the defined CBV
reduction relation, not a theorem about unrestricted reduction under lambdas.

## Build

From the repository root:

```sh
make theories/STLCRecursion/Examples.vo
```

All five `.v` files have complete proofs, with no `Admitted`. The fundamental
and normalization theorems have no additional axioms (`Print Assumptions`).

## Reference

The language follows natural-number primitive recursion in System T; see
Jonathan Sterling, *Higher-order functions and Brouwer's thesis*, Journal of
Functional Programming 31, e11 (2021), Section 2.2,
[doi:10.1017/S0956796821000095](https://doi.org/10.1017/S0956796821000095).
The Rocq development adapts this repository's existing locally nameless STLC
infrastructure and supplies the recursion definitions and proofs here; it is
not a copy of an accompanying formalization from that paper.
