# Feature feasibility checks

`FeatureChecks.v` checks extensions against the current termination-insensitive
target. All its lemmas compile and have no axiomatic assumptions.

The subsequent full recursion extension is now proved in
[`SecurityNoninterferenceRecursion`](../../SecurityNoninterferenceRecursion/README.md).
The recursion entries below describe the narrower scope of this initial probe.

| Feature | Result | Scope of checked evidence |
|---|---|---|
| If-then-else | Compatible as derived syntax | Boolean sums and `case` implement if. `if_typing` propagates the condition's indirect-reader label to the result. The true/false evaluation lemmas verify both branches. |
| Non-determinism | The current target is false | `current_target_fails_with_choice` supplies typed secret inputs, a typed context, a ground transparent public result type, the required label separation, and two unequal completed results. |
| Natural-number recursion | Key LR obligations hold; the complete extension is not yet proved | Equal iteration counts preserve the relation by induction. Different secret counts can produce different results and therefore require protection. Protected unfoldings at arbitrary counts are related at Low. |

## If-then-else

`if_term` is an expansion into the existing language, rather than a new
primitive constructor. Branches are shifted to account for the unused binder
introduced by `case`. For this derived syntax, the existing noninterference
theorem applies to well-typed expanded program contexts. A separate primitive
if implementation would still need its own infrastructure or a verified
translation to this expansion.

## Non-determinism

The probe conservatively embeds core terms and adds binary choice with two
small-step rules, either choosing the left or choosing the right branch.
Both branches must have the same type. This small fragment suffices to refute
the proposed target for a larger language containing the same constructs.

The counterexample context chooses between a public true computation that
ignores the secret and public false. One run chooses true and the other false.
No secret is disclosed; the target incorrectly demands equality across
independent choices. A replacement observation could compare sets of possible
erased public results. That replacement has not been defined or proved here.

## Recursion

`unfold_natrec` uses a Rocq natural number to construct a finite core term; its
step functions may depend on the iteration index. This is a local feasibility
check, not a runtime natural-number type or a complete primitive recursor.

`natrec_compatibility` proves the same-count induction obligation using the
existing LR. `secret_iteration_count_requires_protection` checks the concrete
failure of ignoring the count's label: zero iterations return public true,
one iteration returns public false. `protected_secret_counts_related` proves
that wrapping the results in High protection restores the hidden-result LR
obligation, even for different counts.

The complete recursion feature still requires labeled natural values, their
observation relation, runtime recursion rules with access checks and label
propagation, and an extended fundamental/noninterference proof. These checks
do not justify marking a recursion benchmark as complete.

## Reproduce

From the repository root, with the base theory compiled:

```sh
rocq compile -q -R theories AutoProof theories/SecurityNoninterference/checks/FeatureChecks.v
rocq check -silent -R theories AutoProof AutoProof.SecurityNoninterference.checks.FeatureChecks
```
