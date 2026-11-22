# Catala Default Calculus: Compilation Correctness

Prove `correction_small_steps` in `input/Task.v` without changing the supplied definitions or statement. For any source reduction `s1 → s2`, show that the translations of `s1` and `s2` reduce to a common program.

The target is the correctness result for compiling Catala's default construct to options, one of the contributions of [Abstract Machines and Small-Step Semantics: a Winning Ticket for Proof Automation?](https://doi.org/10.1145/3756907.3756926) (PPDP 2025).

This task adapts the [Rocq software artifact by Alain Delaet, Sandrine Blazy, and Denis Merigoux](https://zenodo.org/records/15583348), distributed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/). It retains the syntax, reduction relation, translation, and the original statement in `theories/catala/trans.v`. Imports and file boundaries were simplified and unrelated definitions and proofs were removed. The relationship operator retains the attribution from the original `sequences.v`.

Requires Autosubst 1.9.
