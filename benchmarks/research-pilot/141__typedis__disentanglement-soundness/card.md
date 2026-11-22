# TypeDis: Disentanglement Soundness

Prove `soundness` in `input/Task.v`. Do not change the supplied definitions or the statement.

This is Theorem 5.1 of [TypeDis: A Type System for Disentanglement](https://arxiv.org/abs/2511.23358) (POPL 2026). A well-typed program that initially contains no allocated locations always remains safe and disentangled, in the sense of the supplied operational definitions.

The input is adapted from the [authors’ Rocq development at `38f6a96`](https://github.com/nobrakal/typedis/tree/38f6a969c4d8f9fb9cbcdb5860946a24600a0b0f) ([MIT](LICENSE)). The [target](https://github.com/nobrakal/typedis/blob/38f6a969c4d8f9fb9cbcdb5860946a24600a0b0f/src/types/final_theorem.v#L435) and its operational predicates are unchanged. Proofs and proof-only imports are omitted; the structural equality and countability instances needed to elaborate the definitions are retained.

Dependency: `rocq-stdpp.1.13.0`.
