# System F Refinement Soundness — If-then-else + Natural-number recursion — Hard

## Input

- `benchmarks/systemf-refinement-soundness-if-recursion-hard/input/Task.v` — the single self-contained Rocq input file.

The base language is locally nameless System F with function and universal types, term abstraction/application, and type abstraction/application.

The refinement-type layer adds predicates, refinement function, existential, and polymorphic types, erasure, subtyping, and refinement typing rules. The additional language feature set is: If-then-else + Natural-number recursion.

The file supplies the language syntax, call-by-value small-step semantics, core and refinement typing rules, and the target theorem.

## Target Theorem

```coq
Theorem refinement_soundness : forall t T ps v,
  has_rtype [] empty_rcontext t (R_Refine T ps) ->
  multi t v ->
  value v ->
  predicates_hold (open_preds_tm ps v).
```

If a closed term has refinement type `{result : T | ps}`, then every reachable value `v` satisfies `ps`.

## Expected Output

Complete `Task.v`: construct an appropriate unary, type-indexed logical relation; define the refinement-context/substitution interpretation; prove the typing-rule and subtyping obligations and a fundamental theorem; and prove the target theorem. The completed file must compile with Rocq and must not use `Admitted`, added axioms, unsafe flags, or changes to the supplied language definitions and theorem statements.
