# System F with refinement types

This directory contains a self-contained refinement-type extension of the
repository's locally nameless System F. It does not import SystemRF.

The System F syntax, opening operations, call-by-value semantics, and core
typing judgment are retained. The refinement layer adds object-language
predicates, refinement types, dependent function and existential types,
well-formedness, subtyping, and refinement typing. Its representation follows
the main locally nameless design choices of the SystemRF artifact, without
including SystemRF's unrelated language features.

- `Syntax.v`: locally nameless System F syntax, operational semantics, and core typing rules.
- `Infrastructure.v`: opening, substitution, local-closure, and instantiation lemmas.
- `CoreTyping.v`: structural metatheory for the core System F typing judgment.
- `RefinementLogic.v`: formula syntax, binding operations, formula well-formedness,
  and interpretation. Boolean connectives are interpreted independently of
  the chosen meaning of atomic comparisons.
- `LogicRegression.v`: equivalence with the previous formula interpretation
  and laws for nested conjunction, disjunction, and negation.
- `RefinementTyping.v`: refinement types, subtyping, refinement typing, and erasure.
- `Evaluation.v`: reduction closure, determinism, core type preservation, and halting lemmas.
- `Denotations.v`: the semantic interpretation of refinement types.
- `RefinementSoundness.v`: the fundamental theorem, semantic subtyping, and refinement soundness.
- `Safety.v`: the proved `never_stuck` theorem for refinement-typed programs.
- `Regression.v`: arithmetic evaluation and typing checks, positive division
  examples, and rejection of division by zero.

## Type safety with partial division

The target is type safety in the presence of partial division.
Its statement is `SystemFRefinementSafety.never_stuck`: if
`has_rtype [] empty_rcontext t R` and `multi t t'`, then `t'` is a value
or can take a step. This theorem and its dependencies are proved without
`Admitted` or project-specific axioms. `Print Assumptions` reports only
dependent functional extensionality, used by the Equations-based denotation.
The old erased-safety proof is kept in a comment for reference.
The current core has `Ty_Int`, integer literals `tm_int (n : Z)`,
`tm_arith op t1 t2` for addition/subtraction/multiplication, and
integer division `tm_div t1 t2`, with local-closure and typing rules.
No separate `Ty_Nat` is added to this language: nonnegative integers are
expressed by a refinement using `Pred_Ge`.
The safety dependency chain has been compiled with integers, integer
comparisons, Boolean formulas, and partial division. Free-variable collection
lives in `Syntax.v`.
Core progress is now false: erased typing alone admits division by zero.
`evals_denotes R t` requires an actual evaluation to a value, in addition
to requiring every reachable value to satisfy `R`. The fundamental theorem
establishes this property from refinement typing. Determinism then ensures
that every reachable intermediate state can still evaluate to a value,
which proves `never_stuck`. The division case uses the divisor's nonzero
refinement explicitly. Semantic implication also requires a substitution
satisfying the refinement context.

Build this proof and its regression checks with:
```
make theories/SystemFRefinement/Regression.vo
rocq check -silent -Q theories AutoProof AutoProof.SystemFRefinement.Safety AutoProof.SystemFRefinement.Regression
```
Legacy normalization drafts are excluded from the committed proof chain.

## Refinement formulas and sources

- Rondon, Kawaguchi, and Jhala, [Liquid Types, PLDI 2008, Section 2](https://goto.ucsd.edu/~rjhala/papers/liquid_types.pdf):
  a qualifier is a Boolean predicate template; inferred refinements are
  conjunctions of instantiated qualifiers. A conjunction or a list is not
  itself a defect. This development is not implementing qualifier inference
  or the paper's placeholder syntax.
- Jhala and Vazou, [Refinement Types: A Tutorial, Section 2](https://arxiv.org/html/2010.07763):
  refinement logic has arithmetic predicates and Boolean connectives,
  including conjunction, disjunction, and negation. The connective structure
  here follows that presentation. CNF/DNF are possible representations of
  formulas, rather than a requirement on `R_Refine`.
- Borkowski, Vazou, and Jhala, [Mechanizing Refinement Types, Sections 2–4](https://nikivazou.github.io/static/drafts/rt2.pdf):
  refinement subtyping uses implication under environment assumptions;
  predicates are Boolean-typed expressions. Its implication oracle and
  kinded polymorphism are not implemented merely by adopting its type shapes.

Here `Inductive qualifier` directly defines formulas. For example,
`Pred_And p (Pred_Or q (Pred_Not r))` expresses `p AND (q OR NOT r)`.
Opening and substitution traverse the complete formula. `entails` contains
logical introduction/elimination rules and can use a base refinement stored
in the environment. This is an explicit proof system, not a complete SMT
solver. `entails_sound` proves the soundness of these rules under a
satisfying substitution.

`Pred_Lt t1 t2` and `Pred_Le t1 t2` require both operands to have type
`Ty_Int`; their semantics compares the integer results of the two terms.
`Pred_Gt` and `Pred_Ge` reverse the operands, and `Pred_Ne` negates equality.
For example, `R_Refine Ty_Int (Pred_Ge (tm_bvar 0) (tm_int 0%Z))`
describes nonnegative integers. Replacing `Pred_Ge` with `Pred_Ne` describes
nonzero integers. Arithmetic implication rules, e.g. from `v > 0` to
`v >= 0`, are not yet part of the current propositional `entails` rules.

`interpret_qualifier` interprets connectives in Rocq's `Prop`, taking an
`atom_interpretation` for equality and comparisons. `predicate_holds` uses
the existing `operational_atoms` instance. This is a modularization, not
yet a restriction to a separate pure arithmetic expression language.
`LogicRegression.interpretation_preserved` checks equivalence with the
previous interpretation for every formula. The legacy equality
atom still means that both terms reduce to the same syntactic value; it is
not higher-order extensional equality or the tutorial's SMT logic. Direct
evaluation in `RT_RefineValue` now requires a closed formula: inability to
evaluate a free variable must not establish a negated equality.

## Integer division

Division evaluates its left operand and then its right operand. `ST_DivInt`
requires a nonzero divisor and uses `Z.div` (quotient rounded down, e.g.
`-7 / 3 = -3`). There is no division-by-zero step. Rocq's total definition
of `Z.div` at zero therefore does not define an object-language step.

`T_Div` checks only integer operand types. `RT_Div` additionally requires
the divisor to have `{v : Int | v != 0}`. The result has `{v : Int | True}`.
`RT_Core` has been removed: ordinary typing cannot establish a refinement
typing derivation by itself, even for a call that syntactically contains no
division. `RT_Int` gives a literal `n` the singleton type `{v : Int | v = n}`;
functions and applications use their refinement-specific rules.

Regression checks cover `6 / 2`, a negative quotient, the absence of a step or
value for `6 / 0`, opening a division body, refinement typing for `6 / 2`,
and failure of zero to satisfy the nonzero qualifier. They also prove that
`6 / 0` cannot have any refinement type, that division by any nonzero integer
is refinement-typable, and that a division function can require a nonzero
argument. These supplement the general type-safety proof.

## Total integer arithmetic

`integer_operator` contains `Int_Add`, `Int_Sub`, and `Int_Mul`.
They share one syntax constructor, typing rule, and semantic proof;
division remains separate because it requires a nonzero divisor.
`RT_Arith` records the result with an equality qualifier, rather than
discarding all result information. Operands evaluate left to right.

The regression checks cover negative subtraction, multiplication,
nested arithmetic, zero operands, precise refinement typing for every
operator and pair of integer literals, and arithmetic inside a qualifier.
Arithmetic implication automation and a separate pure logical-expression
syntax remain outstanding; adding operations does not supply either.
