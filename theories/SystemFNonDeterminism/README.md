# System F + Non-determinism

Adds binary `choice t1 t2`, which can step to either operand. Both operands must have the same type. No Bool, Nat, or recursor is added.

The development retains System F's impredicative polymorphism and the existing locally nameless representation: bound variables use de Bruijn indices, free variables use atoms, and typing abstractions use cofinite opening.

## Target

```coq
Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
```

Here `strongly_normalizing` means there is no infinite path in the **CBV `step` relation defined in Syntax.v**. It is not a theorem about unrestricted reduction beneath abstractions. Every possible choice is covered, not merely one terminating path.

The binary parametricity development also proves the same
`polymorphic_identity_theorem_for_free` as pure System F. Its conclusion
`t[U] v -->* v` asserts that such a path exists; it does not claim that every
nondeterministic path is identical.

## Files and reading order

- `Syntax.v`: syntax, opening, substitution, local closure, values, CBV steps, typing, and strong normalization.
- `LogicalRelation.v`: unary value relation and its expression lifting.
- `Norm.v`: compatibility lemmas, `fundamental`, and `normalization`.
- `Examples.v`: typed polymorphic examples exercising the feature.
- `RelationalEvaluation.v`, `BinaryLogicalRelation.v`, and `TheoremForFree.v`: binary parametricity and the free theorem.
- `Infrastructure.v`: locally nameless and substitution lemmas; consult as needed.

This is a unary normalization development, separate from the binary parametricity relation in `../SystemF`. A value candidate packages a predicate on values and a proof that its members are values. The expression lifting requires local closure, strong normalization, and that every reachable value satisfies the predicate. The universal-type clause quantifies over every locally closed type argument and every value candidate.

Syntax and infrastructure are adapted from this repository's `../SystemF`; feature-specific CBV compatibility proofs are adapted from its STLC normalization developments. The unary System F relation and its type-opening proofs are implemented here; this is not a verbatim external artifact.

## Build

From the repository root:

```sh
make theories/SystemFNonDeterminism/Examples.vo
```

The proofs contain no `Admitted` or additional axioms. `Print Assumptions` reports that `fundamental` and `normalization` are closed under the global context.
