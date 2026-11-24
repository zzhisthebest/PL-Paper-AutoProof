# λRust type soundness

Prove `type_soundness_closed` in `Task.v`: every thread in a reachable state
of a closed, well-typed program is a value or can step, and no two threads
have conflicting accesses as defined by the operational semantics.

Edit only `Task.v`. Keep all given definitions and the target statement
unchanged. You may add definitions and auxiliary proofs. Do not use Iris or
an external proof of the result, consult external sources, introduce or use
axioms, or leave admitted or unfinished proofs. A submission violating
these rules is invalid.

Run `make` to check the project.
