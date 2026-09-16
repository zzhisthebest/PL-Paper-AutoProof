# SystemFRefinementNonDeterminism

Self-contained, locally nameless System F with formula-based refinement types,
integers, arithmetic and partial division. The target is `Safety.never_stuck`:
every state reachable from a closed refinement-typed program is a value or can step.
Ordinary typing alone permits division by zero; the refinement proof supplies
the nonzero-divisor guarantee.

Binary choice can take either branch. `must_terminate` in `Evaluation.v`
requires progress at each state and termination of every successor.
`evals_denotes` uses this all-path property, so one successful path cannot hide
a stuck alternative. Strict qualifier comparisons quantify over all integer
outcomes; a nondeterministic metric cannot be smaller than itself by selecting
different outcomes. `Regression.v` checks unsafe division paths.

## Files

- `Syntax.v`, `Infrastructure.v`, `CoreTyping.v`: language and core metatheory.
- `RefinementLogic.v`: qualifier formulas and their interpretation.
- `RefinementTyping.v`: refinement types, subtyping and typing rules.
- `Evaluation.v`: evaluation metatheory.
- `Denotations.v`: the logical relation, `denotes` and `evals_denotes`.
- `RefinementSoundness.v`: semantic typing and the proved `fundamental` theorem.
- `Safety.v`: the final `never_stuck` theorem.

Equations generates well-founded denotations and uses standard functional
extensionality. There are no admitted proofs or project-specific axioms.
