# Lambda-sec: Termination-Insensitive Noninterference

Prove `soundness_tini` in `input/Task.v`. Do not change the supplied definitions or the statement.

This is Theorem 4.4 of [Mechanized Logical Relations for Termination-Insensitive Noninterference](https://doi.org/10.1145/3434291) (POPL 2021). If both runs terminate, a well-typed program cannot reveal a high-security Boolean input through its low-security result.

The input is adapted from the [authors’ Coq development at `1f3440d`](https://github.com/logsem/iris-tini/tree/1f3440dc1a992329635a25b1fd81703cd058c817) ([BSD 3-Clause](LICENSE)). The [target](https://github.com/logsem/iris-tini/blob/1f3440dc1a992329635a25b1fd81703cd058c817/theories/lambda_sec/noninterference.v#L55) and its hypotheses are unchanged. The step relation specializes Iris 3.4.0's evaluation-context construction to this language ([Iris license](LICENSE-IRIS)); `pstep` retains the authors’ notation for a step with no observations or spawned threads.

Dependencies: `rocq-stdpp.1.13.0` and [Autosubst v1.9](https://github.com/coq-community/autosubst/tree/v1.9).
