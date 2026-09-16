# System F with refinements and if-then-else

This self-contained language extends the updated integer/refinement base
with Boolean literals and a Boolean conditional. It does not import SystemRF.

The target is `SystemFRefinementIfSafety.never_stuck`: every state reachable
from a closed refinement-typed program is a value or can take another step.
Division requires a nonzero divisor. Erased typing alone is insufficient,
since it also admits division by zero.

The checked dependency chain is:
`Syntax`, `Infrastructure`, `CoreTyping`, `RefinementLogic`,
`RefinementTyping`, `Evaluation`, `Denotations`,
`RefinementSoundness`, `Safety`, `Regression`.
The logical relations are `denotes` and `evals_denotes`;
`RefinementSoundness.fundamental` is the fundamental theorem.
Only the selected conditional branch runs, but refinement typing checks both
branches. Regression examples cover branch selection, a typed conditional,
and the impossibility of assigning a refinement type to division by zero.

Qualifiers, integer arithmetic, and partial division have the same definitions
as the base variant. See the base README for their references and limitations.
The safety proof is deterministic; it must not be copied unchanged into a
nondeterministic language.

Legacy normalization drafts are excluded from the committed proof chain
and benchmark inputs.
