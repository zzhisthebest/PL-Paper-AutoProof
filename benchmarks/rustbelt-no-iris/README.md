# RustBelt POPL’18 without Iris

The benchmark case is
[`rustbelt__lambda-rust__type-soundness`](rustbelt__lambda-rust__type-soundness).
It uses the λRust Core and CPS type system from the POPL’18
[technical appendix](https://plv.mpi-sws.org/rustbelt/popl18/appendix.pdf) and
the `popl18` [artifact source](https://github.com/kallydev/lambda-rust/tree/eec05e0aa61e2e8346ab380d0930bbaca4cc1a31)
(pinned mirror). The adapted runtime definitions retain the upstream
[BSD license](LICENSE.rustbelt); the generic step closures come from the
also BSD-licensed Iris program-logic interface of that version.

| File | What it keeps or re-encodes |
| --- | --- |
| `Core.v` | Artifact syntax, values, heap, contexts and head steps, including atomics, both non-atomic phases and fork. Specializes Iris's generic context/thread-pool closure to λRust and retains the artifact's race predicate. |
| `Types.v` | Appendix §1.4 grammar and §§1.4.1–1.4.3: well-formedness, recursive types and size, Copy/Send/Sync, external/local lifetime facts, and lifetime inclusion and liveness. |
| `Inclusion.v` | Appendix §1.4.4 and type reading/writing from §1.4.5: subtyping, context/continuation inclusion, product splitting/joining, borrowing, sharing, reborrowing and unblocking. |
| `Surface.v` | Appendix §1.3 CPS instruction/body syntax. Erasure uses the artifact's `new`, `delete`, `memcpy`, and call expansion (with a fresh continuation binder), and retains the physical steps for starting/ending a lifetime. |
| `Typing.v` | Appendix §1.4.5 instruction and body rules: consequences, continuation definition/jump, lifetime-polymorphic functions/calls, lifetime equalization/start/end, and owned or borrowed sum cases. |
| `Task.v` | The no-data-race **and** no-stuck conclusions of artifact `type_soundness_closed`, from the same empty heap and with the same default exit continuation. The premise uses the syntactic closed-main judgment instead of the Iris assertion. |

The artifact does not have a standalone syntactic typechecker to extract:
its `typed_instruction` and `typed_body` are Iris weakest-precondition
judgments. This case transcribes the published core rules as Rocq judgments.
It uses indexed binders in types, explicit well-formedness and arity premises,
and a scoped hypothesis context for the hypothetical `T-rec` premise.
In `F_call`, the binder for the return value must not capture paths in
the caller's retained resources. This includes projected paths and
resources blocked by a lifetime.
Function lifetime requirements are explicit, as in the appendix; the artifact's
`FP_wf` notation additionally synthesizes requirements from parameter and result
types. That notation is not part of the syntactic judgement here.
There is no memory invariant, semantic interpretation, or proof of soundness
in the input. Static lifetime facts are part of the type system, not the
Iris-based lifetime logic used to prove it.

The source core defines the execution of `Fork` and the safety theorem
checks the whole thread pool. The appendix's core typing rules do not type
raw `Fork`; safe entry points such as `thread::spawn` are separate unsafe
library implementations verified against semantic interfaces in RustBelt.
This task is the closed syntactic core theorem, not a re-verification of
those libraries or of the extension theorem for arbitrary unsafe libraries.

Rocq 9.1 with stdpp 1.13.0 is sufficient. To build the starter definitions
without trying to close the open theorem:

```bash
cd benchmarks/rustbelt-no-iris/rustbelt__lambda-rust__type-soundness/input
rocq makefile -f _CoqProject -o Makefile.coq
make -f Makefile.coq Typing.vo
```

[`checks/CoreExamples.v`](checks/CoreExamples.v) checks representative
derivations outside the model workspace: a closed entry point, lifetime
polymorphism and calls, recursive subtyping, and borrow/share/reborrow and
unblocking. The target has no reference proof in this encoding, and no model
has been run. For a submission,
verify that `Print Assumptions type_soundness_closed.` reports no axioms,
and check its imports independently of compilation.
