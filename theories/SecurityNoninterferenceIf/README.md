# SecurityNoninterferenceIf

This self-contained extension adds primitive `tm_if condition yes no reader`.
Booleans are represented by the existing sum of two public unit types:
`tm_inl` is true and `tm_inr` is false. Branches do not bind variables.
Only the selected branch runs. Its result is protected by the condition's
indirect-reader label, preventing implicit information flow.

The target is `noninterference` in `Noninterference.v`, with the same statement
as the base language. `LogicalRelation.v` proves `fundamental_expressions`.
`Examples.v` checks branch selection and protection;
`checks/ProofAudit.v` prints assumptions of the principal results.

This is an extension of our SLam-inspired fragment, not an exact reproduction
of the original paper's full language.
