# System F Refinement Soundness — None — Easy

## Input

- `benchmarks/systemf-refinement-soundness-none-easy/input/Task.v` — the single self-contained Rocq input file.

The base language is locally nameless System F with function and universal types, term abstraction/application, and type abstraction/application.

The refinement-type layer adds predicates, refinement function, existential, and polymorphic types, erasure, subtyping, and refinement typing rules. The feature configuration is the base language.

The file supplies the language syntax, call-by-value small-step semantics, core and refinement typing rules, the underlying System F normalization metatheory, and the target theorem. It supplies the refinement logical relation (`denotes` and `evals_denotes`) and a proved fundamental theorem named `fundamental`.

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

Complete `Task.v`: use the supplied logical relation and proved fundamental theorem to prove the target theorem. The completed file must compile with Rocq and must not use `Admitted`, added axioms, unsafe flags, or changes to the supplied language definitions and theorem statements.
