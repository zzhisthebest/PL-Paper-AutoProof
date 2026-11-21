Parameter sort : Set.

Parameter axiom : sort -> sort -> Prop.

Parameter rule_pi : sort -> sort -> sort -> Prop.

Parameter rule_sig : sort -> sort -> sort -> Prop.

Parameter rule_eq : sort -> sort -> Prop.

Parameter rule_t : sort -> sort -> Prop.

Parameter rule_unit : sort -> Prop.

Parameter rule_bool : sort -> Prop.

Parameter sort_regularity : forall s1, exists s2, axiom s1 s2.
