# Type safety for System F<:QA with async/sync qualifiers

Prove `preservation` and `progress` in `input/Task.v`. These are Theorems 3.3 and 3.4 of *Qualifying System F-sub* (OOPSLA 2024). The statements are about machine configurations and continuations, where the qualifier discipline rules out calls from a synchronous context to an asynchronous procedure.

The input requires the artifact's FqMeta and label support. Do not change the definitions or theorem statements.
