# System F: Reduction to Inhabitation

Prove `reduction` in `input/Task.v` without changing the supplied definitions or statement. Show that solvability of elementary Diophantine constraints many-one reduces to Curry-style System F inhabitation.

This is the central reduction of [A Simpler Undecidability Proof for System F Inhabitation](https://doi.org/10.4230/LIPIcs.TYPES.2018.2) (TYPES 2018, proceedings published in 2019; Theorems 19 and 27 are the two correctness directions). The task uses the author's [exact mechanized reduction statement](https://github.com/uds-psl/coq-library-undecidability/blob/c7257b736763d7b2bc3bd25ac47d5fb7ce749c9c/theories/SystemF/Reductions/H10C_SAT_to_SysF_INH.v#L1003) from the [Coq Library of Undecidability Proofs at `c7257b7`](https://github.com/uds-psl/coq-library-undecidability/tree/c7257b736763d7b2bc3bd25ac47d5fb7ce749c9c), under [MPL 2.0](LICENSE). No implementation or proof of the reduction is supplied.
