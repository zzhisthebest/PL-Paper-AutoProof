# SLam noninterference: recursion-free fragment

Reference: Nevin Heintze and Jon G. Riecke, *The SLam Calculus: Programming
with Secrecy and Integrity*, POPL 1998, pp. 365–377.
[DOI](https://doi.org/10.1145/268946.268976),
[paper](https://cs.wellesley.edu/~security/papers/slam.pdf).

This directory formalizes the recursion-free fragment of the pure functional
calculus in Section 2, with the two-element lattice `Low <= High`.
It includes unit, sums, products, higher-order functions, subtyping, and
`protect`. Each security annotation contains both `reader` and
`indirect_reader`, with `indirect_reader <= reader`. Booleans are encoded
using sums. General recursion, references, concurrency, and integrity are
outside this fragment. This is not a complete reproduction of the paper.

## Reading order

1. `Syntax.v`: security annotations, types, terms, locally nameless binding.
2. `Semantics.v`: left-to-right call-by-value reduction.
3. `Typing.v`: subtyping and typing rules.
4. `Noninterference.v`: observations, typed program contexts, target theorem.
5. `LogicalRelation.v`: binary LR, compatibility lemmas, fundamental theorem.
6. `Examples.v`: small checked examples of the security mechanisms.

`Evaluation.v` proves that terminating evaluation derivations are equivalent
to small-step `evaluates`. `Metatheory.v` proves weakening, substitution,
preservation, and properties of security erasure. `Substitution.v` proves
simultaneous substitution and its interaction with binders and typing.

## Target

`noninterference` retains the contextual, termination-insensitive statement
of Theorem 2.3. Two closed terms of the same secret type are plugged into the
same typed context. If the result type is ground and transparent, and the
secret's indirect-reader level does not flow to the result's level, then any
two completed evaluations have equal results after security annotations are
erased. The statement does not assume that secret inputs are already values.

`context_has_type C T_hole T_result` types the hole at the fixed type `T_hole`
using a fresh free variable. `program_context` includes holes under binders;
it is not restricted to evaluation contexts.

## Formalization choices

- Bound variables use de Bruijn indices; free variables use atoms. Abstractions
  and case branches bind one term variable. Typing uses cofinite quantification.
- `protect_type` and `protect_value` raise the outer security annotation.
  Application, projection, and case propagate this protection to their results.
  Runtime access checks and the corresponding typing conditions are retained.
- The LR is an operational adaptation of Appendix A.5. `value_relation`
  relates values of the erased underlying type. An unobservable type imposes
  no additional equality condition; observable sums, products, and functions
  are compared structurally. Function tests run at `High` so that test access
  permissions do not hide function behavior.
- `expression_lifting` compares results when both evaluations finish.
  The target uses security-aware typing and annotated evaluation,
  not just their erased counterparts.
- `delay` and `force` support the secret-expression packaging used in the
  paper's final proof. Their typing, relation, and evaluation lemmas are proved.
  The final operational proof instead uses `fundamental_expressions`, which
  permits related expressions as substitutions directly. This stronger lemma
  implies the original value-substitution `fundamental` and handles holes under
  binders without restricting secret inputs to values.

## Status

All definitions and completed proofs compile. `preservation`, evaluation
equivalence, erasure lemmas, and LR compatibility for the language constructs
and subtyping have complete proofs. Observable equality follows from the LR
at transparent ground types. `checks/ProofAudit.v` checks that these results
do not depend on admitted theorems.

`fundamental_expressions`, `fundamental`, and `noninterference` have complete
proofs, with no admitted assumptions. The final proof picks a fresh variable
for the context hole, relates the two secret expressions at their hidden type,
applies `fundamental_expressions`, and obtains equality of observable results.
`checks/ProofAudit.v` includes all three main theorems. These results cover this
recursion-free fragment, not the full recursive language of the paper.
