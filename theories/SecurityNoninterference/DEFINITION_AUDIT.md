# Language definition audit

Reference: Section 2 and Tables 1–3 of
[The SLam Calculus](https://cs.wellesley.edu/~security/papers/slam.pdf).
Scope: the recursion-free fragment, instantiated with a two-element lattice.

## Retained security mechanisms

- Types carry security annotations at every node, with `indirect_reader <= reader`.
- `protect` raises the outer annotation. Application, projection, and case
  propagate the source's indirect-reader level to their results and check
  reader permissions.
- Evaluation is left-to-right call-by-value.
- Arrow subtyping is contravariant in its argument and covariant in its result;
  sums and products are covariant. Subtyping cannot lower security levels.
- Abstractions and case branches bind variables. Opening, substitution, and
  local closure use the same binder depths.

## Scope change

General recursion has been removed from syntax, reduction, typing, evaluation,
program contexts, substitution operations, and examples. The former direct
unfolding variant and its dedicated recursion checks are no longer part of
this development. No extra termination premise was added to `noninterference`.
The security-aware typing and observation conditions of that target remain
unchanged.

This fragment still includes secret inputs, distinguishable public results,
and branching on secret data. `Examples.v` checks that a branch on a secret
boolean protects its result, that unauthorized access is blocked, and that
public true and false are not related. Thus removing recursion has not
removed the information-flow mechanisms being studied.

## Verification status

Weakening, substitution, preservation, equivalence of big-step and small-step
termination, security erasure, and the existing LR compatibility lemmas compile.
`checks/ProofAudit.v` prints their assumptions; the checked results are closed
under the global context.

`fundamental_expressions`, the original `fundamental`, and `noninterference`
are now proved without admitted assumptions. The context proof accepts arbitrary
program contexts, including holes under binders, and arbitrary closed secret
expressions. `Examples.v` also checks an application of the target theorem and
that distinct public boolean values are distinguishable by `same_result`.
