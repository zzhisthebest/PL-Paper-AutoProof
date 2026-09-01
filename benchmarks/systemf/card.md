# System F

## Input

- `benchmarks/systemf/input/Task.v` — a self-contained Rocq file containing
  the locally nameless language syntax, call-by-value small-step operational
  semantics, type well-formedness and typing rules, and the target
  `polymorphic_identity_theorem_for_free` theorem.

## Target Theorem

```coq
Theorem polymorphic_identity_theorem_for_free : forall t,
  has_type [] empty t
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) ->
  forall U v,
    wf_ty [] U ->
    value v ->
    has_type [] empty v U ->
    tm_app (tm_tapp t U) v -->* v.
```

## Expected Output

A complete development containing:

- a binary, type-indexed logical relation for System F values and expressions,
  including an interpretation of bound and free type variables by admissible
  relations between two types;
- interpretations of type-variable and term-variable contexts by pairs of
  related substitutions;
- proofs that the logical relation handles all five constructors of
  `has_type`, corresponding to the five cases of induction on a typing
  derivation;
- a fundamental theorem showing that every well-typed term preserves related
  substitutions, and its closed relational-parametricity corollary;
- a derivation of the target free theorem from parametricity, with a complete
  Rocq proof and no `Admitted`.

The names and internal organization of the semantic definitions are not
fixed.
