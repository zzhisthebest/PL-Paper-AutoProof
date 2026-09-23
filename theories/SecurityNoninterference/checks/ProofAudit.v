From AutoProof.SecurityNoninterference Require Import
  Evaluation Metatheory LogicalRelation Noninterference.

(* Each result below must be closed under the global context. *)
Print Assumptions big_step_iff_evaluates.
Print Assumptions evaluates_protected_function.
Print Assumptions preservation.
Print Assumptions evaluates_erasure.
Print Assumptions value_relation_protect_values.
Print Assumptions value_relation_subtype.
Print Assumptions expression_relation_unit.
Print Assumptions expression_relation_abs.
Print Assumptions expression_relation_app.
Print Assumptions expression_relation_pair.
Print Assumptions expression_relation_inl.
Print Assumptions expression_relation_inr.
Print Assumptions expression_relation_fst.
Print Assumptions expression_relation_snd.
Print Assumptions expression_relation_case.
Print Assumptions expression_relation_protect.
Print Assumptions expression_relation_subtype.
Print Assumptions ground_related_values_equal.
Print Assumptions typing_delay.
Print Assumptions delay_secret_expressions_related.
Print Assumptions force_delay_evaluates.
Print Assumptions typing_instantiate.
Print Assumptions fundamental_expressions.
Print Assumptions fundamental.
Print Assumptions noninterference.
