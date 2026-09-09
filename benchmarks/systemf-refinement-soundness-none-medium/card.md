# System F Refinement Soundness — None — Medium

## Input

- `benchmarks/systemf-refinement-soundness-none-medium/input/Task.v` — the single self-contained Rocq input file.

The base language is locally nameless System F with function and universal types, term abstraction/application, and type abstraction/application.

The refinement-type layer adds predicates, refinement function, existential, and polymorphic types, erasure, subtyping, and refinement typing rules. No additional language feature is included.

The file additionally supplies the unary logical relation formed by `denotes` and `evals_denotes`, together with its direct dependencies. It does not supply a fundamental theorem or its proof.

## Target Theorem

```coq
Theorem refinement_soundness : forall t T ps v,
  has_rtype [] empty_rcontext t (R_Refine T ps) ->
  multi t v ->
  value v ->
  predicates_hold (open_preds_tm ps v).
```

If a closed term has refinement type `{result : T | ps}` and evaluates to a value `v`, then `v` satisfies `ps`.

## Expected Output

Complete `Task.v`: use the supplied logical relation to define the refinement-context/substitution interpretation; prove the typing-rule and subtyping obligations and a fundamental theorem; and prove the target theorem. The completed file must compile with Rocq and must not use `Admitted`, added axioms, unsafe flags, or changes to the supplied language definitions and theorem statements.
