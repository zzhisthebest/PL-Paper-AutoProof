# STLC

## Input

- `benchmarks/stlc/input/Task.v` — a self-contained Rocq
  file containing the language syntax, call-by-value small-step operational
  semantics, typing rules, and the target `normalization` theorem.

## Target Theorem

```coq
Definition halts (t : tm) : Prop :=
  exists v, t -->* v /\ value v.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  halts t.
```

## Expected Output

A complete development containing:

- one or more type-indexed logical relations on values and/or expressions,
  suitable for proving `normalization`;
- an interpretation of typing contexts that maps each typed variable to a
  replacement term satisfying the corresponding logical relation `R`;
- proofs that `R` handles all six constructors of `has_type`, corresponding
  to the six cases of induction on a typing derivation;
- a complete Rocq proof of the target theorem with no `Admitted`.

The names and internal organization of the semantic definitions are not
fixed.
