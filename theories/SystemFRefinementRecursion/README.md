# System F with refinement types and metric-checked recursion

The recursion language now uses an explicit recursive function with a
termination metric, instead of the former System T `tm_natrec`.
This directory and the none variant share the integer-arithmetic design.
Benchmark inputs are generated from these verified definitions and proofs by
`scripts/generate_refinement_cases.py`.

## Definition

`tm_fix A B metric body` binds the argument in `metric`, and the argument
and recursive function in `body`. In the body, bound index 0 is the
argument and bound index 1 is the recursive function.
Its operational rule unfolds the recursive function under call-by-value.
The metric is an annotation, not a runtime test.

`RT_Fix` gives the external function a `measured_input` domain. Within
the body, the recursive function has a `smaller_input` domain:
the new metric must evaluate to an integer satisfying
`0 <= new_metric < current_metric`. The metric can be an arbitrary
Int-typed term template, not just the argument itself.
Natural-valued measures are represented by nonnegative Int values;
there is no separate Nat datatype in this version.

`tm_ifzero` distinguishes zero from nonzero integers. Its refinement
typing rule tests a variable and strengthens that variable's qualifier
in each branch. Other test expressions can first be bound using
lambda/application. No Bool datatype or general Boolean conditional is added.

Qualifiers use formulas, including equality, integer comparisons, and
Boolean connectives. `Entails_Valid` accepts a Rocq proof of an implication
under value substitutions satisfying the context's base refinements.
It is not an axiom or an unchecked SMT oracle.
Division retains the nonzero-divisor requirement and records its result
with an equality qualifier, allowing subsequent arithmetic reasoning.
Addition, subtraction, and multiplication use `tm_arith op t1 t2`,
one shared typing rule `RT_Arith`, and one semantic preservation lemma.
Their result also carries an equality qualifier. They require no
nonzero-divisor premise.

## Checked files

- `Syntax.v`: syntax, opening/substitution, local closure, evaluation, core typing.
- `Infrastructure.v`: updated binding and instantiation lemmas.
- `CoreTyping.v`: core weakening, substitution, and free-variable lemmas.
- `RefinementLogic.v`: formula syntax, binding operations, well-formedness,
  and interpretation parameterized by the meanings of atomic comparisons.
- `LogicRegression.v`: proof that this interpretation agrees with the
  previous one for every formula, plus Boolean-connective regression checks.
- `RefinementTyping.v`: refinement types, refinement typing, metric restriction,
  subtyping, and the proved erasure lemma.
- `Evaluation.v`: core preservation, deterministic evaluation, and halting lemmas.
- `Denotations.v`: the value logical relation `denotes` and expression
  logical relation `evals_denotes`.
- `Termination.v`: independent well-founded orders for nonnegative integer
  ranks, inverse-image measures, and lexicographic products. Relational
  measures require totality and uniqueness of ranks. This module has no
  dependency on program syntax or refinement typing.
- `RefinementSoundness.v`: the proved fundamental theorem, semantic subtyping,
  and `refinement_termination`. Recursive functions use well-founded induction
  using `integer_decreases_wf`. Conversion to natural numbers is confined
  to the independent termination library.
- `Safety.v`: the proved target theorem `never_stuck`.
- `Examples.v`: proved refinement typing for recursion directly to zero
  and recursion on integer division by two; operational and strict-decrease checks.
  Also exhibits a core-typed self-loop, showing why core typing alone cannot
  imply normalization after adding `fix`. Division by zero and infinite
  self-calls are proved not refinement-typable; division-by-two recursion is
  proved safe on every nonnegative integer input.

The refinement-typed recursion examples use metric `n` and input `n >= 0`.
Both `jump_to_zero_typed` and `halve_to_zero_typed` are closed under the
global context.

`count_up_to_zero` additionally demonstrates the operational form
`fix f(n) / (0 - n) = ifzero n then 0 else f(n + 1)`.
Its unfolding and metric-decrease property are proved: for `n < 0`,
`0 <= 0 - (n + 1) < 0 - n`. This checks that the new arithmetic can
express an increasing argument with a decreasing metric; its complete
refinement-typing derivation is not yet included.

## Target theorem

```coq
Theorem never_stuck : forall t t' R,
  has_rtype [] empty_rcontext t R ->
  multi t t' ->
  value t' \/ exists u, t' --> u.
```

The proof chain is `fundamental` → `refinement_termination` → `never_stuck`.
The nonzero-divisor condition is used in `evals_denotes_div`; the metric
condition is used in `recursive_function_denotes`.
No additional termination premise is assumed by the target theorem.
There are no admitted proofs or custom axioms. `Print Assumptions never_stuck`
reports only dependent functional extensionality, used by Equations for the
well-founded logical-relation definition.

Legacy System T proofs are excluded from the committed proof chain.
Their core-normalization claim does not apply to the revised language:
unrestricted core typing with `fix` does not imply termination.

## Reference

The recursive-function typing design follows the single-metric approach in
Jhala and Vazou, *Refinement Types: A Tutorial*, Sections 9.1–9.3:
https://arxiv.org/html/2010.07763#S9

This is an adaptation to this repository's locally nameless language, not a
copy of a formally verified implementation from that tutorial. The language
still accepts a single term-valued metric: lexicographic orders are proved
in `Termination.v`, but are not yet integrated into `tm_fix` or `RT_Fix`.
User-supplied well-founded relations are not language features either.

## Design boundaries and outstanding refactoring

The current qualifiers are operational refinements: their operands are
programs, equality means evaluation to a common value, and integer
comparisons existentially quantify over evaluation results. This is not
the tutorial's separate refinement-logic expression language and is not
an SMT-based type checker. `Entails_Valid` requires an explicit Rocq proof.
`interpret_qualifier` separates the Boolean connectives from the atomic
interpretation; `predicate_holds` still selects `operational_atoms`.
This module boundary does not yet restrict the permitted operand syntax.

In particular, do not copy these metric rules unchanged to a language with
nondeterminism. A metric that may return either zero or one would satisfy
an existential comparison with itself. `Termination.v` includes a checked
counterexample and a general theorem specifying the missing requirement:
each input must have a unique rank (as well as an existing rank). The
current deterministic-language proof discharges uniqueness using
`predicate_result_unique`; no nondeterministic safety theorem is claimed.

The next language change must specify the permitted logical expressions
and their interpretation, then integrate the chosen metric syntax into
typing and prove the corresponding bridges. The existing `never_stuck`
statement must remain unchanged. The present library refactor alone does
not complete that language change or update any benchmark input.

System T remains a legitimate baseline in the other directories. Its
successor/predecessor reduction rule does not limit its definable
algorithms to decrement-by-one source programs. Adding a different
termination discipline is a separate language design, not a repair to
System T.
