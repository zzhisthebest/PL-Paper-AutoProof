# Linear π-Calculus: Subject Reduction

Prove `sr` in `input/Task.v`. Do not change the supplied definitions or the statement.

This is the subject reduction result of [Soundness of Typed Transitions in the Linear π-Calculus](https://doi.org/10.1007/978-3-032-28187-6_7) (FORTE 2026). A well-typed process remains well-typed in the updated environment after a labelled transition.

The input is adapted from the [authors’ Coq development at `48d7464`](https://github.com/marcogiunti/Linear-Pi-Calculus/tree/48d74641ee8f6bd8f8c22dfe2e44684cf40a0a2f) ([GPL v3](LICENSE)). The [target](https://github.com/marcogiunti/Linear-Pi-Calculus/blob/48d74641ee8f6bd8f8c22dfe2e44684cf40a0a2f/right_rules.v#L40) is the full relation's theorem, not the left-only fragment. Only the syntax, operational and typing definitions, and witnesses required to load them are retained. The original proof and proof-only dependencies are omitted.
