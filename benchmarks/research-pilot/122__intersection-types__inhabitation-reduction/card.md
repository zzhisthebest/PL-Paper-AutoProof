# Intersection Types: Reduction to Inhabitation

Prove `reduction` in `input/Task.v` without changing the supplied definitions or statement. Show that simple semi-Thue system 01 rewriting many-one reduces to inhabitation in the Coppo–Dezani intersection type system.

This is the central reduction of [Undecidability of Intersection Type Inhabitation at Rank 3 and its Formalization](https://doi.org/10.3233/FI-2019-1856) (Fundamenta Informaticae, 2019). The task uses the author's [exact mechanized statement](https://github.com/uds-psl/coq-library-undecidability/blob/c7257b736763d7b2bc3bd25ac47d5fb7ce749c9c/theories/IntersectionTypes/Reductions/SSTS01_to_CD_INH.v#L680); it does not state a separate rank bound on the image of the reduction.

The definitions are excerpted from the [Coq Library of Undecidability Proofs at `c7257b7`](https://github.com/uds-psl/coq-library-undecidability/tree/c7257b736763d7b2bc3bd25ac47d5fb7ce749c9c), under [MPL 2.0](LICENSE). The reduction construction and proof are not included.
